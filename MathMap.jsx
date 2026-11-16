import React, { useState, useMemo, useEffect, useLayoutEffect, useRef, useCallback } from "react";

// =============================================================================
// Six focused trees instead of one sprawling graph:
//   - Algebraic Structures : sets + operations/axioms ("is-a" in the strict sense)
//   - Analysis             : functions/sequences/series, mostly PROPERTY chains
//                            (child "implies" parent — a looser but still tree-
//                            shaped relation; Lipschitz implies uniformly
//                            continuous implies continuous)
//   - Numbers & Combinatorics : ℕ⊂ℤ⊂ℚ⊂ℝ⊂ℂ ("embeds into"), arithmetic, counting
//   - Matrices & Linear Maps   : object taxonomies (types of matrix, endomorphism)
//   - Probability           : random variable taxonomy
//   - Patterns: Sub/Quotient/Morphism : the cross-cutting pattern every structure
//                            above shares (subobjects, quotients, morphisms)
// Cross-links (seeAlso) connect concepts across trees without merging them.
// prepa: "MPSI" | "MP" | undefined -> explicitly taught in French CPGE (MP and
//   MP* share one official programme; MP* = same content, more depth/pace).
// =============================================================================

function D(key, label, upLabel, downLabel, branches, nodes) {
  return { key, label, upLabel, downLabel, branches, nodes, byId: Object.fromEntries(nodes.map((n) => [n.id, n])) };
}

// ---------------------------------------------------------------------------
// DOMAIN 1 — Algebraic Structures ("is-a")
// ---------------------------------------------------------------------------
const ALGEBRA_NODES = [
  { id: "set", name: "Set", branch: "root", parents: [], blurb: "A collection of elements with no imposed structure.", delta: "no axioms — just membership", fr: "ensemble" },
  { id: "binary-relation", name: "Binary Relation", branch: "root", parents: ["set"], blurb: "A subset of E×E describing which pairs of elements are related.", delta: "R ⊆ E×E", fr: "relation binaire", prepa: "MPSI" },
  { id: "preorder", name: "Preorder", branch: "order", parents: ["binary-relation"], blurb: "Reflexive and transitive, but not necessarily antisymmetric — the scaffold beneath both orders and equivalences.", delta: "+ reflexive, transitive" },
  { id: "equivalence-relation", name: "Equivalence Relation", branch: "root", parents: ["preorder"], blurb: "A preorder that is also symmetric — partitions the set into classes. Corresponds exactly to a partition of E.", delta: "+ symmetric: xRy ⟹ yRx", fr: "relation d'équivalence", prepa: "MPSI" },
  { id: "quotient-set", name: "Quotient Set", branch: "root", parents: ["set"], blurb: "The set of equivalence classes E/∼ of a set under an equivalence relation — the machinery behind ℤ/nℤ.", delta: "elements = equivalence classes", fr: "ensemble quotient E/∼", prepa: "MPSI" },

  { id: "poset", name: "Partially Ordered Set", branch: "order", parents: ["preorder"], blurb: "A preorder that is also antisymmetric.", delta: "+ antisymmetric: x≤y & y≤x ⟹ x=y", fr: "ensemble ordonné", prepa: "MPSI" },
  { id: "total-order", name: "Totally Ordered Set", branch: "order", parents: ["poset"], blurb: "A poset in which every two elements are comparable.", delta: "+ trichotomy: any x,y comparable", fr: "ordre total", prepa: "MPSI" },
  { id: "well-order", name: "Well-Ordered Set", branch: "order", parents: ["total-order"], blurb: "Every nonempty subset has a least element — underlies proof by induction on ℕ.", delta: "+ every nonempty subset has a least element", fr: "bon ordre (récurrence sur ℕ)", prepa: "MPSI" },
  { id: "lattice", name: "Lattice", branch: "order", parents: ["poset"], blurb: "A poset in which every pair of elements has a join (sup) and meet (inf). Usually peripheral to the syllabus.", delta: "+ every pair has join ∨ and meet ∧" },
  { id: "distributive-lattice", name: "Distributive Lattice", branch: "order", parents: ["lattice"], blurb: "A lattice where ∨ and ∧ distribute over each other.", delta: "+ ∨,∧ mutually distribute" },
  { id: "boolean-algebra", name: "Boolean Algebra", branch: "order", parents: ["distributive-lattice"], blurb: "A complemented distributive lattice — models classical logic / set algebra.", delta: "+ complementation, 0 and 1 bounds" },
  { id: "complete-lattice", name: "Complete Lattice", branch: "order", parents: ["lattice"], blurb: "Every subset (not just pairs) has a join and meet.", delta: "+ arbitrary sups/infs exist" },

  { id: "magma", name: "Magma", branch: "group", parents: ["set"], blurb: "A set with a single closed binary operation — 'loi de composition interne', the first brick of the structures chapter.", delta: "+ closed binary operation •", fr: "magma (loi de composition interne)", prepa: "MPSI" },
  { id: "semigroup", name: "Semigroup", branch: "group", parents: ["magma"], blurb: "A magma where the operation is associative — a stepping stone toward monoïde, rarely named on its own in class.", delta: "+ associativity: (a•b)•c = a•(b•c)", fr: "loi associative", prepa: "MPSI" },
  { id: "monoid", name: "Monoid", branch: "group", parents: ["semigroup"], blurb: "A semigroup with an identity element — e.g. (ℕ,+) or (ℕ,×), monoids that aren't groups.", delta: "+ identity element e: e•a = a•e = a", fr: "monoïde", prepa: "MPSI" },
  { id: "group", name: "Group", branch: "group", parents: ["monoid"], blurb: "A monoid in which every element has an inverse.", delta: "+ inverses: ∀a ∃a⁻¹, a•a⁻¹ = e", fr: "groupe", prepa: "MPSI" },
  { id: "abelian-group", name: "Abelian Group", branch: "group", parents: ["group"], blurb: "A group whose operation is commutative.", delta: "+ commutativity: a•b = b•a", fr: "groupe commutatif / abélien", prepa: "MPSI" },
  { id: "cyclic-group", name: "Cyclic Group", branch: "group", parents: ["abelian-group"], blurb: "Generated by a single element. The classic prépa example: 𝕌ₙ, the n-th roots of unity in ℂ — a finite cyclic subgroup of ℂ×.", delta: "+ ∃g: every element = gⁿ", fr: "groupe cyclique (ex: 𝕌ₙ)", prepa: "MPSI" },
  { id: "symmetric-group", name: "Symmetric Group Sₙ", branch: "group", parents: ["group"], blurb: "The group of permutations of {1,...,n} under composition — non-abelian for n≥3, central to the determinant chapter. Every permutation decomposes into disjoint cycles and into transpositions; the signature ε:Sₙ→{-1,1} is a group homomorphism.", delta: "specific group: all bijections of a finite set", fr: "groupe symétrique, permutations, signature", prepa: "MPSI", seeAlso: [{ domain: "numbers", id: "nu-permutation" }] },
  { id: "alternating-group", name: "Alternating Group Aₙ", branch: "group", parents: ["symmetric-group"], blurb: "The subgroup of Sₙ consisting of even permutations — kernel of the signature homomorphism.", delta: "+ ε(σ) = +1 (even permutations)", fr: "groupe alterné Aₙ", prepa: "MPSI" },
  { id: "general-linear-group", name: "General Linear Group GL(E)", branch: "group", parents: ["group"], blurb: "Invertible linear maps of a vector space E (or invertible n×n matrices), under composition.", delta: "specific group: automorphisms of a vector space", fr: "groupe linéaire GL(E), GLₙ(K)", prepa: "MPSI" },
  { id: "orthogonal-group", name: "Orthogonal Group O(E)", branch: "group", parents: ["group"], blurb: "Linear isometries of a Euclidean space — maps preserving the inner product. A orthogonal ⟺ AᵀA=I ⟺ A⁻¹=Aᵀ.", delta: "specific group: isometries of a Euclidean space", fr: "groupe orthogonal O(E), Oₙ(ℝ)", prepa: "MP" },
  { id: "special-orthogonal-group", name: "Special Orthogonal Group SO(n)", branch: "group", parents: ["orthogonal-group"], blurb: "The subgroup of O(n) with determinant +1 — rotations, as opposed to reflections.", delta: "+ det = +1 (rotations only)", fr: "groupe spécial orthogonal SO(n)", prepa: "MP" },
  { id: "unitary-group", name: "Unitary Group U(n)", branch: "group", parents: ["group"], blurb: "Linear isometries of a Hermitian space — the complex analogue of O(n).", delta: "specific group: isometries of a Hermitian space", fr: "groupe unitaire (approfondi en MP*)", prepa: "MP" },
  { id: "free-group", name: "Free Group", branch: "group", parents: ["group"], blurb: "Generated by a set with no relations beyond the group axioms.", delta: "+ no relations among generators" },
  { id: "lie-group", name: "Lie Group", branch: "group", parents: ["group", "smooth-manifold"], blurb: "A group that is also a smooth manifold, with smooth operations.", delta: "+ smooth manifold structure; •, ⁻¹ smooth" },
  { id: "topological-group", name: "Topological Group", branch: "group", parents: ["group", "topological-space"], blurb: "A group with a topology making • and inverse continuous.", delta: "+ topology; •, ⁻¹ continuous" },

  { id: "semiring", name: "Semiring", branch: "ring", parents: ["set"], blurb: "Two monoid-like operations (+, ×) with distributivity, but + need not have inverses — pure scaffolding here. ℕ is the running example.", delta: "+, × with distributivity; no additive inverses", fr: "ex: ℕ", prepa: "MPSI", seeAlso: [{ domain: "numbers", id: "nu-N" }] },
  { id: "ring", name: "Ring", branch: "ring", parents: ["abelian-group", "semiring"], blurb: "Abelian group under +, monoid under ×, × distributes over +. French convention always assumes a multiplicative identity 1.", delta: "+ multiplicative monoid; distributivity", fr: "anneau", prepa: "MPSI" },
  { id: "rng", name: "Rng", branch: "ring", parents: ["abelian-group"], blurb: "A ring without the requirement of a multiplicative identity — essentially never used in CPGE.", delta: "× need not have identity 1" },
  { id: "comm-ring", name: "Commutative Ring", branch: "ring", parents: ["ring"], blurb: "A ring where multiplication is commutative.", delta: "+ a×b = b×a", fr: "anneau commutatif", prepa: "MPSI" },
  { id: "domain", name: "Integral Domain", branch: "ring", parents: ["comm-ring"], blurb: "A nonzero commutative ring with no zero divisors. ℤ and K[X] are the two running examples.", delta: "+ ab=0 ⟹ a=0 or b=0; 1≠0", fr: "anneau intègre", prepa: "MPSI", seeAlso: [{ domain: "numbers", id: "nu-Z" }] },
  { id: "gcd-domain", name: "GCD Domain", branch: "ring", parents: ["domain"], blurb: "Integral domain where every pair of elements has a gcd — the abstract theory behind pgcd(a,b) in ℤ and K[X].", delta: "+ gcd(a,b) exists for all a,b" },
  { id: "ufd", name: "Unique Factorization Domain", branch: "ring", parents: ["gcd-domain"], blurb: "Every element factors uniquely into irreducibles — proven concretely for ℤ (primes) and K[X] (irreducible polynomials), though the abstract term isn't standard prépa vocabulary.", delta: "+ unique factorization into irreducibles" },
  { id: "pid", name: "Principal Ideal Domain", branch: "ring", parents: ["ufd"], blurb: "Every ideal is generated by a single element. Proven explicitly for ℤ ('les idéaux de ℤ sont les nℤ') and for K[X] — the result is useful even though 'PID' as a named abstract structure isn't usually introduced.", delta: "+ every ideal = (a) for some a", fr: "(fait établi pour ℤ et K[X])", prepa: "MPSI", seeAlso: [{ domain: "morphisms", id: "mo-principal-ideal" }] },
  { id: "euclidean-domain", name: "Euclidean Domain", branch: "ring", parents: ["pid"], blurb: "A domain admitting a division algorithm with remainder — the division euclidienne in both ℤ and K[X] is a cornerstone of the arithmetic and polynomial chapters.", delta: "+ Euclidean function allowing division w/ remainder", fr: "division euclidienne (ℤ, K[X])", prepa: "MPSI" },
  { id: "field", name: "Field", branch: "ring", parents: ["euclidean-domain", "division-ring"], blurb: "A commutative ring where every nonzero element is invertible.", delta: "+ every nonzero element has multiplicative inverse", fr: "corps", prepa: "MPSI" },
  { id: "finite-field", name: "Finite Field", branch: "ring", parents: ["field"], blurb: "A field with finitely many elements. In prépa: ℤ/pℤ is a field exactly when p is prime.", delta: "+ |F| = pⁿ finite", fr: "ex: ℤ/pℤ, p premier", prepa: "MPSI" },
  { id: "algebraically-closed-field", name: "Algebraically Closed Field", branch: "ring", parents: ["field"], blurb: "Every non-constant polynomial has a root in the field. ℂ's closure is the théorème de d'Alembert–Gauss, often stated and used as an admitted result.", delta: "+ every poly of degree ≥1 has a root", fr: "théorème de d'Alembert–Gauss (ℂ)", prepa: "MPSI", seeAlso: [{ domain: "numbers", id: "nu-C" }] },
  { id: "ordered-field", name: "Ordered Field", branch: "ring", parents: ["field", "ordered-ring"], blurb: "A field with a compatible total order — the implicit backdrop whenever inequalities are used on ℝ.", delta: "+ compatible total order ≤", fr: "ex: ℝ", prepa: "MPSI", seeAlso: [{ domain: "numbers", id: "nu-R" }] },
  { id: "real-closed-field", name: "Real Closed Field", branch: "ring", parents: ["ordered-field"], blurb: "Ordered field where every positive element has a square root and every odd-degree poly has a root (ℝ is the model example).", delta: "+ sqrt of positives exist; odd-degree polys have roots" },
  { id: "division-ring", name: "Division Ring", branch: "ring", parents: ["ring"], blurb: "A ring where every nonzero element has a multiplicative inverse — non-commutative fields (e.g. quaternions).", delta: "+ every nonzero element invertible (× need not commute)" },
  { id: "ordered-ring", name: "Ordered Ring", branch: "ring", parents: ["comm-ring"], blurb: "A ring equipped with a compatible total order.", delta: "+ compatible total order ≤" },
  { id: "local-ring", name: "Local Ring", branch: "ring", parents: ["comm-ring"], blurb: "A commutative ring with a unique maximal ideal.", delta: "+ unique maximal ideal" },
  { id: "noetherian-ring", name: "Noetherian Ring", branch: "ring", parents: ["comm-ring"], blurb: "Every ascending chain of ideals stabilizes (equivalently: ideals are finitely generated).", delta: "+ ascending chain condition on ideals" },
  { id: "boolean-ring", name: "Boolean Ring", branch: "ring", parents: ["comm-ring"], blurb: "Every element is idempotent: a² = a.", delta: "+ a² = a for all a" },

  { id: "z-mod-n", name: "ℤ/nℤ", branch: "ring", parents: ["comm-ring", "quotient-set"], blurb: "Integers modulo n, built as a quotient set of ℤ by the congruence relation. A field exactly when n is prime.", delta: "quotient of ℤ; field ⟺ n prime", fr: "anneau ℤ/nℤ", prepa: "MPSI", seeAlso: [{ domain: "numbers", id: "nu-congruence" }] },
  { id: "poly-ring", name: "Polynomial Ring K[X]", branch: "ring", parents: ["euclidean-domain", "algebra-over-field"], blurb: "Polynomials over a field K. Simultaneously a Euclidean domain (division euclidienne of polynomials) and a K-algebra — one of the central examples in the rings chapter. Infinite-dimensional as a K-vector space.", delta: "division euclidienne, Bézout, irreducibles", fr: "algèbre des polynômes K[X]", prepa: "MPSI", seeAlso: [{ domain: "matrices", id: "mx-polynomial" }] },
  { id: "poly-ring-degree-n", name: "Kₙ[X] (degree ≤ n)", branch: "ring", parents: ["vector-space"], blurb: "Polynomials of degree at most n — a finite-dimensional (dim n+1) subspace of K[X], not itself closed under multiplication so not a subring.", delta: "finite-dim'l subspace of K[X], dim = n+1", fr: "Kₙ[X]", prepa: "MPSI" },
  { id: "rational-fraction-field", name: "Field of Rational Fractions K(X)", branch: "ring", parents: ["field"], blurb: "The field of fractions of K[X] — rational functions, studied via partial fraction decomposition.", delta: "fraction field of K[X]", fr: "fractions rationnelles, décomposition en éléments simples", prepa: "MPSI", seeAlso: [{ domain: "matrices", id: "mx-rational-function" }] },
  { id: "matrix-ring", name: "Matrix Ring Mₙ(K)", branch: "ring", parents: ["ring", "algebra-over-field"], blurb: "Square n×n matrices over K under +, × — non-commutative for n≥2, and simultaneously a K-algebra.", delta: "non-commutative for n≥2", fr: "anneau/algèbre Mₙ(K)", prepa: "MPSI", seeAlso: [{ domain: "matrices", id: "mx-square-matrix" }] },
  { id: "endomorphism-algebra", name: "Endomorphism Algebra L(E)", branch: "ring", parents: ["ring", "algebra-over-field"], blurb: "Linear endomorphisms of E under composition — a ring (non-commutative if dim E ≥ 2) and a K-algebra.", delta: "anneau (L(E),+,∘); non-comm. if dim E≥2", fr: "algèbre L(E)", prepa: "MPSI", seeAlso: [{ domain: "matrices", id: "mx-endomorphism" }] },

  { id: "module", name: "Module (over ring R)", branch: "module", parents: ["abelian-group"], blurb: "An abelian group with scalar multiplication by a ring, compatible with + and ×. Occasionally mentioned as 'what vector spaces generalize to' — not developed in CPGE.", delta: "+ scalar action by ring R" },
  { id: "vector-space", name: "Vector Space", branch: "module", parents: ["module"], blurb: "A module where the ring of scalars is a field — the natural scalar setting for linear algebra.", delta: "scalars restricted to a field", fr: "espace vectoriel", prepa: "MPSI" },
  { id: "algebra-over-field", name: "Algebra (over a field)", branch: "module", parents: ["vector-space", "ring"], blurb: "A vector space equipped with a compatible bilinear multiplication — exactly what K[X], Mₙ(K) and L(E) are.", delta: "+ bilinear multiplication compatible with scalars", fr: "K-algèbre (K[X], Mₙ(K), L(E))", prepa: "MPSI" },
  { id: "associative-algebra", name: "Associative Algebra", branch: "module", parents: ["algebra-over-field"], blurb: "An algebra where multiplication is associative.", delta: "+ associativity of ×" },
  { id: "lie-algebra", name: "Lie Algebra", branch: "module", parents: ["vector-space"], blurb: "A vector space with an alternating bilinear bracket [·,·] satisfying the Jacobi identity.", delta: "+ bracket [x,y], Jacobi identity, [x,x]=0" },
  { id: "normed-space", name: "Normed Vector Space", branch: "module", parents: ["vector-space"], blurb: "A vector space with a norm ‖·‖. Officially: 'la topologie est étudiée dans le cadre général des espaces vectoriels normés' — this, rather than abstract metric spaces, is the standard topological framework in this setting.", delta: "+ norm ‖v‖ satisfying triangle inequality", fr: "espace vectoriel normé (EVN)", prepa: "MP" },
  { id: "banach-space", name: "Banach Space", branch: "module", parents: ["normed-space", "complete-metric-space"], blurb: "A normed space complete w.r.t. its induced metric. Finite-dimensional normed spaces are automatically complete — used implicitly rather than named at length.", delta: "+ completeness under induced metric" },
  { id: "hilbert-space", name: "Hilbert Space", branch: "module", parents: ["inner-product-space", "banach-space"], blurb: "An inner product space complete under its induced norm — the infinite-dimensional generalization of espace euclidien.", delta: "+ completeness under inner-product norm" },

  { id: "bilinear-space", name: "Bilinear Form Space", branch: "forms", parents: ["vector-space"], blurb: "A vector space E equipped with a bilinear form B: E×E → K.", delta: "+ bilinear form B(x,y)", fr: "forme bilinéaire", prepa: "MP" },
  { id: "symmetric-bilinear-space", name: "Symmetric Bilinear Form Space", branch: "forms", parents: ["bilinear-space"], blurb: "A bilinear space where B(x,y) = B(y,x).", delta: "+ B(x,y) = B(y,x)", fr: "forme bilinéaire symétrique", prepa: "MP" },
  { id: "quadratic-space", name: "Quadratic Form Space", branch: "forms", parents: ["symmetric-bilinear-space"], blurb: "The equivalent structure via Q(x) = B(x,x); recovers B by polarization. Treated more lightly than inner-product theory.", delta: "Q(x) = B(x,x)", fr: "forme quadratique", prepa: "MP" },
  { id: "sesquilinear-space", name: "Sesquilinear Form Space", branch: "forms", parents: ["vector-space"], blurb: "A complex vector space with a form linear in one variable, conjugate-linear in the other.", delta: "+ sesquilinear form", fr: "forme sesquilinéaire (MP*)", prepa: "MP" },
  { id: "hermitian-form-space", name: "Hermitian Form Space", branch: "forms", parents: ["sesquilinear-space"], blurb: "A sesquilinear space where the form satisfies Hermitian symmetry B(x,y) = conj(B(y,x)).", delta: "+ Hermitian symmetry", fr: "forme hermitienne (MP*)", prepa: "MP" },
  { id: "inner-product-space", name: "Inner Product Space (real)", branch: "forms", parents: ["symmetric-bilinear-space"], blurb: "A symmetric bilinear space where the form is positive-definite: ⟨x,x⟩ > 0 for x≠0. Also called a pre-Hilbert space.", delta: "+ positive-definite: ⟨x,x⟩ > 0", fr: "espace préhilbertien réel", prepa: "MP" },
  { id: "complex-inner-product-space", name: "Inner Product Space (complex)", branch: "forms", parents: ["hermitian-form-space"], blurb: "A Hermitian form space where the form is positive-definite.", delta: "+ positive-definite Hermitian form", fr: "espace préhilbertien complexe", prepa: "MP" },
  { id: "euclidean-space", name: "Euclidean Space", branch: "forms", parents: ["inner-product-space"], blurb: "A finite-dimensional real inner product space — orthonormal bases, orthogonal projections, adjoints, Gram matrices, groupe orthogonal. In finite dimension E = F ⊕ F⊥.", delta: "+ finite dimension", fr: "espace euclidien", prepa: "MP" },
  { id: "hermitian-space", name: "Hermitian Space", branch: "forms", parents: ["complex-inner-product-space"], blurb: "A finite-dimensional complex inner product space — the complex analogue of a finite-dimensional real inner product space.", delta: "+ finite dimension", fr: "espace hermitien (MP*)", prepa: "MP" },

  { id: "affine-space", name: "Affine Space", branch: "geometry", parents: ["set"], blurb: "A set E of points with an attached vector space acting simply-transitively via translations — the formal backdrop for classical geometry (points vs. vectors). A vector subspace is an affine subspace through the origin; a general affine subspace need not contain 0.", delta: "+ vector space acting by translation", fr: "espace affine", prepa: "MPSI", seeAlso: [{ domain: "morphisms", id: "mo-affine-subspace" }] },
  { id: "euclidean-affine-space", name: "Euclidean Affine Space", branch: "geometry", parents: ["affine-space"], blurb: "An affine space whose attached vector space is Euclidean — distances and angles between points.", delta: "+ attached vector space is Euclidean", fr: "espace affine euclidien", prepa: "MPSI" },

  { id: "topological-space", name: "Topological Space", branch: "topology", parents: ["set"], blurb: "A set with a collection of open sets satisfying union/intersection axioms — abstract general topology is not part of the CPGE programme.", delta: "+ topology τ (open sets)" },
  { id: "metric-space", name: "Metric Space", branch: "topology", parents: ["set"], blurb: "A set with a distance function d(x,y). Prépa mostly works via the distance induced by a norm on a vector space, rather than abstract metric spaces in their own right.", delta: "+ metric d(x,y) ≥0, symmetric, triangle ineq.", fr: "espace métrique (secondaire face aux EVN)" },
  { id: "complete-metric-space", name: "Complete Metric Space", branch: "topology", parents: ["metric-space"], blurb: "Every Cauchy sequence converges within the space — underlies completeness of finite-dimensional normed spaces, used implicitly.", delta: "+ every Cauchy sequence converges" },
  { id: "hausdorff-space", name: "Hausdorff Space", branch: "topology", parents: ["topological-space"], blurb: "Distinct points can be separated by disjoint open sets.", delta: "+ T2 separation axiom" },
  { id: "compact-space", name: "Compact Space", branch: "topology", parents: ["topological-space"], blurb: "Every open cover has a finite subcover. Studied specifically within normed vector spaces (finite dimension: compact ⟺ closed and bounded; Bolzano–Weierstrass / Borel–Lebesgue characterizations).", delta: "+ every open cover has finite subcover", fr: "compacité (dans un EVN)", prepa: "MP" },
  { id: "connected-space", name: "Connected Space", branch: "topology", parents: ["topological-space"], blurb: "Cannot be partitioned into two disjoint nonempty open sets — the general topological notion (path-connectedness, below, is what's actually taught).", delta: "+ no separation into disjoint opens" },
  { id: "path-connected-space", name: "Path-Connected Space", branch: "topology", parents: ["connected-space"], blurb: "Any two points are joined by a continuous path. In a normed vector space this generalizes the intermediate value theorem — 'un dessin pertinent peut valoir preuve'.", delta: "+ any two points joined by a continuous path", fr: "connexité par arcs", prepa: "MP" },
  { id: "manifold", name: "Topological Manifold", branch: "topology", parents: ["hausdorff-space"], blurb: "Locally homeomorphic to Euclidean space ℝⁿ.", delta: "+ locally homeomorphic to ℝⁿ" },
  { id: "smooth-manifold", name: "Smooth Manifold", branch: "topology", parents: ["manifold"], blurb: "A manifold with an atlas whose transition maps are smooth (C∞).", delta: "+ smooth (C∞) transition maps" },
  { id: "riemannian-manifold", name: "Riemannian Manifold", branch: "topology", parents: ["smooth-manifold"], blurb: "A smooth manifold with a smoothly-varying inner product on tangent spaces.", delta: "+ metric tensor g on tangent spaces" },

  { id: "measurable-space", name: "Measurable Space", branch: "probability", parents: ["set"], blurb: "A set Ω with a tribu (σ-algèbre): a collection of subsets closed under complement and countable union. Manipulating tribus in the abstract isn't a goal of the programme — the discrete/countable case is what matters.", delta: "+ σ-algebra 𝒜 (stable under complement, countable union)", fr: "espace probabilisable (Ω, 𝒜)", prepa: "MP", seeAlso: [{ domain: "probability", id: "pr-random-variable" }] },
  { id: "probability-space", name: "Probability Space", branch: "probability", parents: ["measurable-space"], blurb: "A measurable space equipped with a probability measure P: 𝒜 → [0,1] with P(Ω)=1 and σ-additivity.", delta: "+ probability measure P, P(Ω)=1, σ-additive", fr: "espace probabilisé (Ω, 𝒜, P)", prepa: "MP" },

  { id: "category", name: "Category", branch: "category", parents: [], blurb: "Objects and morphisms with composition, satisfying associativity and identity — the most general algebraic-flavored structure. Not part of CPGE.", delta: "objects + morphisms + composition + identity" },
  { id: "groupoid", name: "Groupoid", branch: "category", parents: ["category"], blurb: "A category in which every morphism is invertible.", delta: "+ every morphism invertible" },
  { id: "monoidal-category", name: "Monoidal Category", branch: "category", parents: ["category"], blurb: "A category with a tensor product ⊗ and unit object, associative up to coherent isomorphism.", delta: "+ ⊗, unit object, coherence isomorphisms" },
  { id: "abelian-category", name: "Abelian Category", branch: "category", parents: ["category"], blurb: "A category (like R-Mod) with zero object, kernels, cokernels, and biproducts — where homological algebra works.", delta: "+ zero object, (co)kernels, biproducts" },
];

const ALGEBRA_BRANCHES = {
  root: { label: "Foundations", color: "#8a8578" },
  order: { label: "Order & Relations", color: "#8a4f9e" },
  group: { label: "Group-like", color: "#b8562f" },
  ring: { label: "Ring-like", color: "#2f6b8a" },
  module: { label: "Module / Vector Space", color: "#5c7a3a" },
  forms: { label: "Bilinear / Quadratic Forms", color: "#0f9488" },
  geometry: { label: "Affine Geometry", color: "#4a5a9e" },
  topology: { label: "Topology & Analysis", color: "#b08a1f" },
  probability: { label: "Probability (spaces)", color: "#b8305f" },
  category: { label: "Category Theory", color: "#3a3a3a" },
};

const PREPA_COLORS = { MPSI: "#2f6b8a", MP: "#b8305f" };

// ---------------------------------------------------------------------------
// DOMAIN 2 — Analysis: Functions, Sequences & Series ("implies" / "specializes")
// ---------------------------------------------------------------------------
const ANALYSIS_NODES = [
  { id: "an-function", name: "Function", branch: "func", parents: [], blurb: "f: E→F, assigning one f(x)∈F to each x∈E. Associated objects: domain, codomain, image f(A), inverse image f⁻¹(B), restriction, graph.", delta: "assigns f(x) ∈ F to each x ∈ E", fr: "application / fonction", prepa: "MPSI" },
  { id: "an-injective", name: "Injective Function", branch: "func", parents: ["an-function"], blurb: "f(x)=f(y) ⟹ x=y.", delta: "+ injective", fr: "injective", prepa: "MPSI" },
  { id: "an-surjective", name: "Surjective Function", branch: "func", parents: ["an-function"], blurb: "f(E) = F.", delta: "+ surjective", fr: "surjective", prepa: "MPSI" },
  { id: "an-bijective", name: "Bijective Function", branch: "func", parents: ["an-injective", "an-surjective"], blurb: "Injective and surjective — equivalently, f⁻¹ exists as a function.", delta: "injective + surjective", fr: "bijective", prepa: "MPSI" },
  { id: "an-real-function", name: "Real / Complex Function", branch: "func", parents: ["an-function"], blurb: "f: I ⊆ ℝ or ℂ → ℝ or ℂ. Branches into algebraic properties (bounded, monotone, convex, periodic) and regularity (continuity, differentiability).", delta: "domain/codomain in ℝ or ℂ", fr: "fonction réelle/complexe", prepa: "MPSI" },
  { id: "an-bounded", name: "Bounded Function", branch: "func", parents: ["an-real-function"], delta: "+ ∃M, |f(x)|≤M", fr: "bornée", prepa: "MPSI" },
  { id: "an-monotone", name: "Monotone Function", branch: "func", parents: ["an-real-function"], delta: "+ increasing or decreasing", fr: "monotone", prepa: "MPSI" },
  { id: "an-convex", name: "Convex Function", branch: "func", parents: ["an-real-function"], blurb: "Characterized by monotonicity of f′, or the sign of f″.", delta: "+ f(tx+(1-t)y) ≤ tf(x)+(1-t)f(y)", fr: "convexe", prepa: "MP" },
  { id: "an-periodic", name: "Periodic Function", branch: "func", parents: ["an-real-function"], delta: "+ ∃T, f(x+T)=f(x)", fr: "périodique", prepa: "MPSI" },
  { id: "an-continuous", name: "Continuous Function", branch: "func", parents: ["an-real-function"], blurb: "x→a ⟹ f(x)→f(a). Continuous image of an interval is an interval; continuous image of a compact set is compact (and attains its min/max).", delta: "+ x→a ⟹ f(x)→f(a)", fr: "continue", prepa: "MPSI" },
  { id: "an-uniformly-continuous", name: "Uniformly Continuous Function", branch: "func", parents: ["an-continuous"], blurb: "Continuous on a compact set ⟹ uniformly continuous (Heine).", delta: "+ uniform in x (not just pointwise)", fr: "uniformément continue", prepa: "MP" },
  { id: "an-lipschitz", name: "Lipschitz Function", branch: "func", parents: ["an-uniformly-continuous"], delta: "+ |f(x)-f(y)| ≤ k|x-y|", fr: "lipschitzienne", prepa: "MPSI" },
  { id: "an-homeomorphism", name: "Homeomorphism", branch: "func", parents: ["an-continuous"], blurb: "Bijective, continuous, with continuous inverse.", delta: "bijective + continuous + continuous inverse", fr: "homéomorphisme", prepa: "MP" },
  { id: "an-differentiable", name: "Differentiable Function", branch: "func", parents: ["an-continuous"], blurb: "f'(a) = lim (f(a+h)-f(a))/h exists.", delta: "+ f'(a) exists", fr: "dérivable", prepa: "MPSI" },
  { id: "an-c1", name: "C¹ Function", branch: "func", parents: ["an-differentiable"], delta: "+ f' exists and is continuous", fr: "de classe C¹", prepa: "MPSI" },
  { id: "an-ck", name: "Cᵏ Function", branch: "func", parents: ["an-c1"], delta: "+ k-times continuously differentiable", fr: "de classe Cᵏ", prepa: "MP" },
  { id: "an-cinf", name: "C∞ (Smooth) Function", branch: "func", parents: ["an-ck"], delta: "+ Cᵏ for every k", fr: "de classe C∞", prepa: "MP" },
  { id: "an-analytic", name: "Analytic Function", branch: "func", parents: ["an-cinf"], blurb: "Locally equal to its own convergent Taylor/power series. C∞ does NOT imply analytic — the reverse implication fails.", delta: "+ locally equal to its power series", fr: "analytique (DSE)", prepa: "MP" },

  { id: "an-sequence", name: "Sequence", branch: "seq", parents: [], blurb: "u: ℕ→ℝ or ℂ. A subsequence is a composition with a strictly increasing φ:ℕ→ℕ.", delta: "u: ℕ → ℝ or ℂ", fr: "suite", prepa: "MPSI" },
  { id: "an-bounded-seq", name: "Bounded Sequence", branch: "seq", parents: ["an-sequence"], delta: "+ ∃M, |uₙ|≤M", fr: "bornée", prepa: "MPSI" },
  { id: "an-convergent-seq", name: "Convergent Sequence", branch: "seq", parents: ["an-bounded-seq"], blurb: "Every convergent sequence is bounded; the converse is false.", delta: "+ uₙ → l for some l", fr: "convergente", prepa: "MPSI" },
  { id: "an-cauchy-seq", name: "Cauchy Sequence", branch: "seq", parents: ["an-bounded-seq"], blurb: "In ℝ or ℂ: Cauchy ⟺ convergent (completeness) — the two notions coincide.", delta: "+ |uₙ-uₘ|→0 as n,m→∞", fr: "de Cauchy", prepa: "MPSI" },
  { id: "an-monotone-seq", name: "Monotone Sequence", branch: "seq", parents: ["an-sequence"], blurb: "Monotone + bounded ⟹ convergent (classic criterion).", delta: "+ increasing or decreasing", fr: "monotone", prepa: "MPSI" },
  { id: "an-adjacent-seq", name: "Adjacent Sequences", branch: "seq", parents: ["an-monotone-seq"], blurb: "One increasing, one decreasing, difference → 0 — both converge to the same limit.", delta: "+ paired, difference → 0", fr: "suites adjacentes", prepa: "MPSI" },

  { id: "an-series", name: "Numerical Series Σuₙ", branch: "series", parents: [], blurb: "Studied via its sequence of partial sums Sₙ = Σₖ₌₀ⁿ uₖ.", delta: "defined via partial sums Sₙ", fr: "série numérique", prepa: "MPSI" },
  { id: "an-convergent-series", name: "Convergent Series", branch: "series", parents: ["an-series"], delta: "+ (Sₙ) converges", fr: "convergente", prepa: "MPSI" },
  { id: "an-abs-convergent-series", name: "Absolutely Convergent Series", branch: "series", parents: ["an-convergent-series"], blurb: "Σ|uₙ| converges ⟹ Σuₙ converges (not conversely).", delta: "+ Σ|uₙ| converges", fr: "absolument convergente", prepa: "MPSI" },
  { id: "an-conditionally-convergent", name: "Conditionally (Semi-)Convergent Series", branch: "series", parents: ["an-convergent-series"], blurb: "Convergent but not absolutely convergent — e.g. the alternating harmonic series.", delta: "convergent, but Σ|uₙ| diverges", fr: "semi-convergente", prepa: "MP" },
  { id: "an-summable-family", name: "Summable Family", branch: "series", parents: [], blurb: "Generalizes absolute convergence to an arbitrary countable index set, order-independent — useful in probability, including for double sums.", delta: "order-independent sum over a countable index set", fr: "famille sommable", prepa: "MP" },

  { id: "an-pointwise-conv", name: "Sequence of Functions — Pointwise Convergence", branch: "funcseq", parents: [], blurb: "∀x, fₙ(x)→f(x).", delta: "∀x, fₙ(x) → f(x)", fr: "convergence simple", prepa: "MP" },
  { id: "an-uniform-conv", name: "Uniform Convergence", branch: "funcseq", parents: ["an-pointwise-conv"], blurb: "sup|fₙ(x)-f(x)|→0. Preserves continuity of the limit; allows swapping limit and integral.", delta: "+ sup|fₙ(x)-f(x)| → 0", fr: "convergence uniforme", prepa: "MP" },
  { id: "an-normal-conv", name: "Normal Convergence (series of functions)", branch: "funcseq", parents: ["an-uniform-conv"], blurb: "Σ‖fₙ‖∞ < ∞ — the standard working tool for series of functions.", delta: "+ Σ‖fₙ‖∞ < ∞", fr: "convergence normale", prepa: "MP" },
  { id: "an-power-series", name: "Power Series Σaₙ(x-a)ⁿ", branch: "funcseq", parents: ["an-series"], blurb: "Has a radius of convergence R: absolute convergence for |x-a|<R, divergence for |x-a|>R, normal convergence on any closed disc/segment strictly inside R.", delta: "+ radius of convergence R", fr: "série entière", prepa: "MP" },

  { id: "an-ode", name: "Differential Equation", branch: "ode", parents: [], blurb: "An equation relating a function to its derivative(s).", delta: "relates y to y′ (and beyond)", fr: "équation différentielle", prepa: "MPSI" },
  { id: "an-ode-1st-order", name: "First-Order ODE y′=F(x,y)", branch: "ode", parents: ["an-ode"], delta: "y′ = F(x,y)", fr: "équation différentielle d'ordre 1", prepa: "MPSI" },
  { id: "an-ode-linear-1st", name: "Linear First-Order ODE", branch: "ode", parents: ["an-ode-1st-order"], blurb: "y′+a(x)y=b(x). General solution = one particular solution + solutions of the homogeneous equation.", delta: "y′ + a(x)y = b(x)", fr: "équation linéaire d'ordre 1", prepa: "MPSI" },
  { id: "an-ode-linear-2nd", name: "Linear Second-Order ODE", branch: "ode", parents: ["an-ode-linear-1st"], blurb: "y″+a(x)y′+b(x)y=c(x). For constant coefficients, the characteristic polynomial controls the homogeneous solutions.", delta: "y″ + a(x)y′ + b(x)y = c(x)", fr: "équation linéaire d'ordre 2", prepa: "MP" },
  { id: "an-ode-system", name: "Linear System X′=AX+B", branch: "ode", parents: ["an-ode-linear-1st"], blurb: "Vector-valued; for constant A, the homogeneous solution is X(t)=e^{tA}X(0). Diagonalizing/triangularizing A simplifies computing e^{tA}.", delta: "vector-valued, X′ = AX + B", fr: "système différentiel linéaire", prepa: "MP" },

  { id: "an-multivar-function", name: "Function of Several Variables", branch: "multivar", parents: [], blurb: "f: U⊆ℝⁿ→ℝᵖ.", delta: "f: U ⊆ ℝⁿ → ℝᵖ", fr: "fonction de plusieurs variables", prepa: "MP" },
  { id: "an-partial-derivatives", name: "Admits Partial Derivatives", branch: "multivar", parents: ["an-multivar-function"], blurb: "Necessary but NOT sufficient for differentiability.", delta: "+ ∂f/∂xᵢ exist", fr: "dérivées partielles", prepa: "MP" },
  { id: "an-differentiable-multivar", name: "Differentiable (several variables)", branch: "multivar", parents: ["an-partial-derivatives"], blurb: "⟹ continuous; represented by the Jacobian matrix; for scalar f, df_a(h) = ⟨∇f(a),h⟩ in Euclidean coordinates.", delta: "+ Fréchet-differentiable (Jacobian exists)", fr: "différentiable", prepa: "MP" },
  { id: "an-c1-multivar", name: "C¹ (several variables)", branch: "multivar", parents: ["an-differentiable-multivar"], delta: "+ Jacobian depends continuously on x", fr: "de classe C¹", prepa: "MP" },

  { id: "an-parametrized-curve", name: "Parametrized Curve", branch: "curves", parents: [], blurb: "γ: I→ℝⁿ. A graph {(x,f(x))} is the special case γ(x)=(x,f(x)).", delta: "γ: I → ℝⁿ", fr: "courbe paramétrée", prepa: "MPSI" },
  { id: "an-regular-curve", name: "Regular Curve", branch: "curves", parents: ["an-parametrized-curve"], blurb: "γ'(t)≠0 at every point — has a well-defined tangent line.", delta: "+ γ'(t) ≠ 0 everywhere", fr: "point régulier", prepa: "MPSI" },
];

const ANALYSIS_BRANCHES = {
  func: { label: "Functions & Regularity", color: "#b8562f" },
  seq: { label: "Sequences", color: "#2f6b8a" },
  series: { label: "Series", color: "#5c7a3a" },
  funcseq: { label: "Sequences/Series of Functions", color: "#0f9488" },
  ode: { label: "Differential Equations", color: "#8a4f9e" },
  multivar: { label: "Several Variables", color: "#b08a1f" },
  curves: { label: "Parametrized Curves", color: "#4a5a9e" },
};

// ---------------------------------------------------------------------------
// DOMAIN 3 — Numbers, Arithmetic & Combinatorics ("embeds into" for number
// systems; ordinary "is-a" for the arithmetic/combinatorics sub-trees)
// ---------------------------------------------------------------------------
const NUMBERS_NODES = [
  { id: "nu-N", name: "ℕ", branch: "systems", parents: [], blurb: "Natural numbers, including 0 by French convention. A commutative semiring — no subtraction.", delta: "commutative semiring", fr: "entiers naturels", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "semiring" }] },
  { id: "nu-Z", name: "ℤ", branch: "systems", parents: ["nu-N"], blurb: "Integers — ℕ extended with negatives. An integral domain, not a field.", delta: "integral domain", fr: "entiers relatifs", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "domain" }] },
  { id: "nu-Q", name: "ℚ", branch: "systems", parents: ["nu-Z"], blurb: "Rationals — ℤ extended with multiplicative inverses. A field.", delta: "field", fr: "rationnels", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "field" }] },
  { id: "nu-R", name: "ℝ", branch: "systems", parents: ["nu-Q"], blurb: "Reals — the order-complete field: every nonempty subset bounded above has a supremum. Totally ordered; ℚ and ℝ∖ℚ are both dense in ℝ.", delta: "order-complete ordered field", fr: "réels", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "ordered-field" }] },
  { id: "nu-C", name: "ℂ", branch: "systems", parents: ["nu-R"], blurb: "Complex numbers — ℝ extended with i, i²=-1. Algebraically closed (d'Alembert–Gauss: every nonconstant polynomial splits into linear factors), but admits no field-compatible total order.", delta: "algebraically closed field, unorderable", fr: "complexes", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "algebraically-closed-field" }] },

  { id: "nu-divisibility", name: "Divisibility", branch: "arithmetic", parents: ["nu-Z"], blurb: "a | b : a divides b.", delta: "a | b", fr: "divisibilité", prepa: "MPSI" },
  { id: "nu-prime", name: "Prime Number", branch: "arithmetic", parents: ["nu-divisibility"], blurb: "Only divisible by 1 and itself.", delta: "divisors = {1, p}", fr: "nombre premier", prepa: "MPSI" },
  { id: "nu-gcd", name: "GCD", branch: "arithmetic", parents: ["nu-divisibility"], delta: "greatest common divisor", fr: "pgcd(a,b)", prepa: "MPSI" },
  { id: "nu-coprime", name: "Coprime Integers", branch: "arithmetic", parents: ["nu-gcd"], delta: "gcd(a,b) = 1", fr: "premiers entre eux", prepa: "MPSI" },
  { id: "nu-lcm", name: "LCM", branch: "arithmetic", parents: ["nu-divisibility"], delta: "least common multiple", fr: "ppcm(a,b)", prepa: "MPSI" },
  { id: "nu-bezout", name: "Bézout Identity", branch: "arithmetic", parents: ["nu-gcd"], delta: "∃u,v: au+bv = gcd(a,b)", fr: "identité de Bézout", prepa: "MPSI" },
  { id: "nu-euclidean-algo", name: "Euclidean Algorithm", branch: "arithmetic", parents: ["nu-gcd"], blurb: "Computes gcd(a,b) via repeated Euclidean division.", delta: "repeated division algorithm", fr: "algorithme d'Euclide", prepa: "MPSI" },
  { id: "nu-gauss-lemma", name: "Gauss's Lemma", branch: "arithmetic", parents: ["nu-coprime"], delta: "a|bc & gcd(a,b)=1 ⟹ a|c", fr: "lemme de Gauss", prepa: "MPSI" },
  { id: "nu-prime-factorization", name: "Prime Factorization", branch: "arithmetic", parents: ["nu-prime"], blurb: "Every integer >1 factors uniquely into primes.", delta: "unique factorization into primes", fr: "décomposition en facteurs premiers", prepa: "MPSI" },
  { id: "nu-valuation", name: "p-adic Valuation", branch: "arithmetic", parents: ["nu-prime-factorization"], delta: "vₚ(n) = exponent of p in n", fr: "valuation p-adique", prepa: "MP" },
  { id: "nu-congruence", name: "Congruence mod n", branch: "arithmetic", parents: ["nu-divisibility"], blurb: "a≡b (mod n) ⟺ n|(a-b) — an equivalence relation on ℤ whose quotient is ℤ/nℤ.", delta: "a ≡ b (mod n) ⟺ n | (a-b)", fr: "congruence", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "z-mod-n" }] },
  { id: "nu-diophantine", name: "Diophantine Equation", branch: "arithmetic", parents: ["nu-bezout"], delta: "equation solved over ℤ", fr: "équation diophantienne", prepa: "MPSI" },

  { id: "nu-countable", name: "Countable Set", branch: "combinatorics", parents: [], blurb: "Finite, or in bijection with a subset of ℕ.", delta: "finite or bijects with a subset of ℕ", fr: "dénombrable", prepa: "MP" },
  { id: "nu-finite-set", name: "Finite Set", branch: "combinatorics", parents: ["nu-countable"], blurb: "In bijection with {1,...,n} for some n.", delta: "bijects with {1,...,n}", fr: "ensemble fini", prepa: "MPSI" },
  { id: "nu-countably-infinite", name: "Countably Infinite Set", branch: "combinatorics", parents: ["nu-countable"], delta: "bijects with ℕ itself", fr: "infini dénombrable", prepa: "MP" },
  { id: "nu-uncountable", name: "Uncountable Set", branch: "combinatorics", parents: [], blurb: "Not countable — e.g. ℝ, proven via Cantor's diagonal argument. An important application of Cantor's diagonal argument is that ℝ is not countable.", delta: "not in bijection with any subset of ℕ", fr: "non dénombrable (ex: ℝ)", prepa: "MP" },
  { id: "nu-permutation", name: "Permutation", branch: "combinatorics", parents: ["nu-finite-set"], blurb: "A bijection from a finite set to itself.", delta: "bijection E → E", fr: "permutation", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "symmetric-group" }] },
  { id: "nu-arrangement", name: "Arrangement", branch: "combinatorics", parents: ["nu-finite-set"], blurb: "An ordered selection of k distinct elements from a set of size n (injective sequence).", delta: "ordered selection without repetition", fr: "arrangement", prepa: "MPSI" },
  { id: "nu-combination", name: "Combination", branch: "combinatorics", parents: ["nu-finite-set"], blurb: "An unordered selection of k elements — a subset of size k.", delta: "unordered selection (k-subset)", fr: "combinaison", prepa: "MPSI" },
  { id: "nu-binomial-coeff", name: "Binomial Coefficient", branch: "combinatorics", parents: ["nu-combination"], blurb: "C(n,k): number of k-subsets of an n-set. Governs the binomial theorem.", delta: "counts k-subsets of an n-set", fr: "coefficient binomial, binôme de Newton", prepa: "MPSI" },
];

const NUMBERS_BRANCHES = {
  systems: { label: "Number Systems (ℕ⊂ℤ⊂ℚ⊂ℝ⊂ℂ)", color: "#2f6b8a" },
  arithmetic: { label: "Arithmetic in ℤ", color: "#b8562f" },
  combinatorics: { label: "Combinatorics", color: "#5c7a3a" },
};

// ---------------------------------------------------------------------------
// DOMAIN 4 — Polynomials, Matrices & Linear Maps (object taxonomies, "is-a")
// ---------------------------------------------------------------------------
const MATRICES_NODES = [
  { id: "mx-polynomial", name: "Polynomial", branch: "poly", parents: [], blurb: "A formal expression P=Σ aₖXᵏ over a field K.", delta: "P = Σ aₖXᵏ", fr: "polynôme", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "poly-ring" }] },
  { id: "mx-root", name: "Root of a Polynomial", branch: "poly", parents: ["mx-polynomial"], blurb: "a is a root of P ⟺ (X-a) | P.", delta: "P(a) = 0 ⟺ (X-a) | P", fr: "racine", prepa: "MPSI" },
  { id: "mx-multiple-root", name: "Root of Multiplicity m", branch: "poly", parents: ["mx-root"], delta: "(X-a)ᵐ | P but (X-a)^(m+1) ∤ P", fr: "racine de multiplicité m", prepa: "MPSI" },
  { id: "mx-irreducible-poly", name: "Irreducible Polynomial", branch: "poly", parents: ["mx-polynomial"], blurb: "Cannot be factored into two non-unit polynomials. Over ℂ: degree 1 only. Over ℝ: degree 1 or 2.", delta: "no nontrivial factorization", fr: "irréductible", prepa: "MPSI" },
  { id: "mx-rational-function", name: "Rational Function P/Q", branch: "poly", parents: [], blurb: "A quotient of polynomials, Q≠0 — poles, zeros, polynomial part, partial-fraction decomposition.", delta: "P/Q, Q ≠ 0", fr: "fraction rationnelle", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "rational-fraction-field" }] },

  { id: "mx-linear-form", name: "Linear Form", branch: "linmap", parents: [], blurb: "A linear map E→K.", delta: "u: E → K linear", fr: "forme linéaire", prepa: "MPSI" },
  { id: "mx-endomorphism", name: "Endomorphism", branch: "linmap", parents: [], blurb: "A linear map E→E.", delta: "u: E → E linear", fr: "endomorphisme", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "endomorphism-algebra" }, { domain: "morphisms", id: "mo-endomorphism" }] },
  { id: "mx-automorphism-lin", name: "Automorphism (of E)", branch: "linmap", parents: ["mx-endomorphism"], delta: "+ invertible", fr: "automorphisme", prepa: "MPSI" },
  { id: "mx-projection", name: "Projection / Projector", branch: "linmap", parents: ["mx-endomorphism"], delta: "p² = p", fr: "projecteur", prepa: "MPSI" },
  { id: "mx-symmetry", name: "Symmetry / Involution", branch: "linmap", parents: ["mx-endomorphism"], delta: "s² = Id", fr: "symétrie", prepa: "MPSI" },
  { id: "mx-nilpotent-endo", name: "Nilpotent Endomorphism", branch: "linmap", parents: ["mx-endomorphism"], delta: "uᵐ = 0 for some m", fr: "endomorphisme nilpotent", prepa: "MP" },
  { id: "mx-homothety", name: "Homothety", branch: "linmap", parents: ["mx-endomorphism"], delta: "u = λ·Id", fr: "homothétie", prepa: "MPSI" },
  { id: "mx-triangularizable", name: "Triangularizable Endomorphism", branch: "linmap", parents: ["mx-endomorphism"], blurb: "∃ basis in which the matrix is upper-triangular. Over an algebraically closed field: equivalent to the characteristic polynomial splitting (Cayley–Hamilton: χᵤ(u)=0).", delta: "∃ basis → upper-triangular matrix", fr: "trigonalisable", prepa: "MP" },
  { id: "mx-diagonalizable", name: "Diagonalizable Endomorphism", branch: "linmap", parents: ["mx-triangularizable"], blurb: "∃ basis of eigenvectors. Characterized by a split annihilating polynomial with simple roots.", delta: "∃ basis of eigenvectors", fr: "diagonalisable", prepa: "MP" },

  { id: "mx-matrix", name: "Matrix", branch: "matrix", parents: [], blurb: "A rectangular array (aᵢⱼ) ∈ Mₙ,ₚ(K). After choosing bases, every linear map is represented by a matrix; composition ↔ matrix product, change of basis ↔ transition matrices.", delta: "(aᵢⱼ) ∈ Mₙ,ₚ(K)", fr: "matrice", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "matrix-ring" }] },
  { id: "mx-square-matrix", name: "Square Matrix", branch: "matrix", parents: ["mx-matrix"], delta: "n = p", fr: "matrice carrée", prepa: "MPSI" },
  { id: "mx-diagonal-matrix", name: "Diagonal Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "zero off the diagonal", fr: "matrice diagonale", prepa: "MPSI" },
  { id: "mx-triangular-matrix", name: "Triangular Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "zero below (or above) the diagonal", fr: "matrice triangulaire", prepa: "MPSI" },
  { id: "mx-symmetric-matrix", name: "Symmetric Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "Aᵀ = A", fr: "matrice symétrique", prepa: "MP" },
  { id: "mx-skew-symmetric-matrix", name: "Skew-Symmetric Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "Aᵀ = -A", fr: "matrice antisymétrique", prepa: "MP" },
  { id: "mx-orthogonal-matrix", name: "Orthogonal Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "AᵀA = I ⟺ A⁻¹ = Aᵀ", fr: "matrice orthogonale", prepa: "MP", seeAlso: [{ domain: "algebra", id: "orthogonal-group" }] },
  { id: "mx-hermitian-matrix", name: "Hermitian Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "A* = A (conjugate transpose)", fr: "matrice hermitienne (MP*)", prepa: "MP" },
  { id: "mx-unitary-matrix", name: "Unitary Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "A*A = I", fr: "matrice unitaire (MP*)", prepa: "MP", seeAlso: [{ domain: "algebra", id: "unitary-group" }] },
  { id: "mx-nilpotent-matrix", name: "Nilpotent Matrix", branch: "matrix", parents: ["mx-square-matrix"], delta: "Aᵐ = 0 for some m", fr: "matrice nilpotente", prepa: "MP" },
  { id: "mx-invertible-matrix", name: "Invertible Matrix", branch: "matrix", parents: ["mx-square-matrix"], blurb: "∃A⁻¹. Equivalent to det A≠0, equivalent to rank A=n.", delta: "det A ≠ 0 ⟺ rank A = n", fr: "matrice inversible", prepa: "MPSI" },

  { id: "mx-determinant", name: "Determinant", branch: "linsys", parents: [], blurb: "det: Mₙ(K)→K, the unique alternating n-linear form of the columns normalized by det(Iₙ)=1. det(AB)=det(A)det(B).", delta: "alternating n-linear form, det(Iₙ)=1", fr: "déterminant", prepa: "MPSI" },
  { id: "mx-linear-system", name: "Linear System AX=B", branch: "linsys", parents: [], blurb: "Solved via Gaussian elimination / row-echelon form.", delta: "AX = B", fr: "système linéaire", prepa: "MPSI" },
  { id: "mx-homogeneous-system", name: "Homogeneous System AX=0", branch: "linsys", parents: ["mx-linear-system"], blurb: "Solution set = ker(A), a vector subspace. For AX=B, the solution set (if nonempty) is an affine subspace X₀+ker(A).", delta: "solution set = ker(A)", fr: "système homogène", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "affine-space" }] },
];

const MATRICES_BRANCHES = {
  poly: { label: "Polynomials & Rational Functions", color: "#5c7a3a" },
  linmap: { label: "Linear Maps & Reduction", color: "#b8562f" },
  matrix: { label: "Matrix Taxonomy", color: "#2f6b8a" },
  linsys: { label: "Determinant & Linear Systems", color: "#8a4f9e" },
};

// ---------------------------------------------------------------------------
// DOMAIN 5 — Probability
// ---------------------------------------------------------------------------
const PROBABILITY_NODES = [
  { id: "pr-random-variable", name: "Random Variable", branch: "rv", parents: [], blurb: "A function X: Ω→ℝ (measurable, though in the discrete CPGE setting this is mostly implicit).", delta: "X: Ω → ℝ", fr: "variable aléatoire", prepa: "MP", seeAlso: [{ domain: "algebra", id: "probability-space" }] },
  { id: "pr-discrete-rv", name: "Discrete Random Variable", branch: "rv", parents: ["pr-random-variable"], delta: "+ countable range", fr: "v.a. discrète", prepa: "MP" },
  { id: "pr-finite-rv", name: "Finite-Valued Random Variable", branch: "rv", parents: ["pr-discrete-rv"], delta: "+ finite range", fr: "v.a. finie", prepa: "MPSI" },
  { id: "pr-bernoulli", name: "Bernoulli Random Variable", branch: "rv", parents: ["pr-finite-rv"], delta: "values in {0,1}", fr: "loi de Bernoulli", prepa: "MPSI" },
  { id: "pr-binomial", name: "Binomial Random Variable", branch: "rv", parents: ["pr-bernoulli"], blurb: "Sum of n independent Bernoulli trials.", delta: "sum of n i.i.d. Bernoulli", fr: "loi binomiale", prepa: "MPSI" },
  { id: "pr-geometric", name: "Geometric Random Variable", branch: "rv", parents: ["pr-discrete-rv"], blurb: "Rank of the first success in independent Bernoulli trials — countably infinite support.", delta: "rank of first success", fr: "loi géométrique", prepa: "MP" },
  { id: "pr-poisson", name: "Poisson Random Variable", branch: "rv", parents: ["pr-discrete-rv"], delta: "values in ℕ, parameter λ", fr: "loi de Poisson", prepa: "MP" },
  { id: "pr-random-vector", name: "Random Vector (X₁,...,Xₙ)", branch: "rv", parents: ["pr-random-variable"], delta: "tuple of random variables", fr: "vecteur aléatoire", prepa: "MP" },
  { id: "pr-independence", name: "Independent Events / Variables", branch: "concepts", parents: [], blurb: "P(A∩B)=P(A)P(B). Mutual independence is strictly stronger than pairwise independence. For independent integrable X,Y: E(XY)=E(X)E(Y), so independence ⟹ zero covariance (not conversely).", delta: "P(A∩B) = P(A)P(B)", fr: "indépendance", prepa: "MPSI" },
  { id: "pr-complete-system", name: "Complete System of Events", branch: "concepts", parents: [], blurb: "A partition of Ω into events — basis for the law of total probability and Bayes' formula.", delta: "partition of Ω into events", fr: "système complet d'événements", prepa: "MPSI" },
];

const PROBABILITY_BRANCHES = {
  rv: { label: "Random Variables", color: "#b8305f" },
  concepts: { label: "Independence & Partitions", color: "#2f6b8a" },
};

// ---------------------------------------------------------------------------
// DOMAIN 6 — Patterns: Subobjects, Quotients & Morphisms
// The universal pattern underlying every structure in the Algebra domain.
// ---------------------------------------------------------------------------
const MORPHISMS_NODES = [
  { id: "mo-subobject", name: "Subobject", branch: "sub", parents: [], blurb: "A subset of a structure that is itself stable under the structure's operations — the general pattern behind subgroups, subrings, subspaces.", delta: "subset stable under the structure's operations", fr: "sous-objet" },
  { id: "mo-subgroup", name: "Subgroup", branch: "sub", parents: ["mo-subobject"], delta: "subset stable under •, ⁻¹, containing e", fr: "sous-groupe", prepa: "MPSI" },
  { id: "mo-subring", name: "Subring", branch: "sub", parents: ["mo-subobject"], delta: "subset stable under +, ×, containing 0, 1", fr: "sous-anneau", prepa: "MPSI" },
  { id: "mo-subfield", name: "Subfield", branch: "sub", parents: ["mo-subring"], delta: "subring that is itself a field", fr: "sous-corps", prepa: "MPSI" },
  { id: "mo-ideal", name: "Ideal", branch: "sub", parents: ["mo-subobject"], blurb: "An additive subgroup absorbing multiplication: x∈A, i∈I ⟹ xi∈I. Not generally a subring (need not contain 1). The kernel of a ring homomorphism is always an ideal.", delta: "additive subgroup with absorption: xI ⊆ I", fr: "idéal (noyau d'un morphisme d'anneaux)", prepa: "MPSI" },
  { id: "mo-principal-ideal", name: "Principal Ideal", branch: "sub", parents: ["mo-ideal"], blurb: "Generated by a single element: (a) = aA. Every ideal of ℤ has this form: nℤ.", delta: "generated by one element: (a)", fr: "idéal principal (ex: nℤ)", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "pid" }] },
  { id: "mo-vector-subspace", name: "Vector Subspace", branch: "sub", parents: ["mo-subobject"], delta: "subset stable under + and scalar ×", fr: "sous-espace vectoriel", prepa: "MPSI" },
  { id: "mo-subalgebra", name: "Subalgebra", branch: "sub", parents: ["mo-subobject"], blurb: "Simultaneously a vector subspace and a subring — rarely named explicitly in CPGE.", delta: "subspace that is also a subring" },
  { id: "mo-invariant-subspace", name: "Invariant Subspace", branch: "sub", parents: ["mo-vector-subspace"], blurb: "F with u(F)⊆F for an endomorphism u — central to the reduction chapter.", delta: "u(F) ⊆ F for an endomorphism u", fr: "sous-espace stable", prepa: "MP" },
  { id: "mo-affine-subspace", name: "Affine Subspace", branch: "sub", parents: ["mo-subobject"], blurb: "A + F: a point plus a vector subspace. A vector subspace is the special case through the origin.", delta: "A + F (point + vector subspace)", fr: "sous-espace affine", prepa: "MPSI", seeAlso: [{ domain: "algebra", id: "affine-space" }] },
  { id: "mo-topological-subspace", name: "Topological Subspace", branch: "sub", parents: ["mo-subobject"], blurb: "A subset with the induced (subspace) topology.", delta: "induced topology" },

  { id: "mo-quotient", name: "Quotient", branch: "quot", parents: [], blurb: "An object built by identifying equivalent elements of a larger structure — the same idea behind ℤ/nℤ, generalized to any structure.", delta: "identify equivalent elements", fr: "quotient" },
  { id: "mo-quotient-group", name: "Quotient Group G/H", branch: "quot", parents: ["mo-quotient"], blurb: "Defined when H is a normal subgroup. The general (non-abelian) construction goes beyond CPGE, though the abelian case ℤ/nℤ is used constantly.", delta: "G/H, H normal" },
  { id: "mo-quotient-ring", name: "Quotient Ring A/I", branch: "quot", parents: ["mo-quotient"], blurb: "A/I where I is an ideal. ℤ/nℤ is the concrete prépa example.", delta: "A/I, I an ideal", seeAlso: [{ domain: "algebra", id: "z-mod-n" }] },
  { id: "mo-quotient-vector-space", name: "Quotient Vector Space E/F", branch: "quot", parents: ["mo-quotient"], blurb: "Usually secondary in the syllabus.", delta: "E/F, F a subspace" },

  { id: "mo-morphism", name: "Structure-Preserving Map", branch: "morph", parents: [], blurb: "A function between two structured sets that respects the structure — a group homomorphism respects •, a linear map respects + and scalar ×, a continuous map respects limits.", delta: "f(x ⋆ y) = f(x) ⋆ f(y), structure-dependent", fr: "morphisme" },
  { id: "mo-group-hom", name: "Group Homomorphism", branch: "morph", parents: ["mo-morphism"], delta: "φ(xy) = φ(x)φ(y)", fr: "morphisme de groupes", prepa: "MPSI" },
  { id: "mo-ring-hom", name: "Ring Homomorphism", branch: "morph", parents: ["mo-morphism"], blurb: "Is in particular a group homomorphism for +.", delta: "preserves +, ×, 1", fr: "morphisme d'anneaux", prepa: "MPSI" },
  { id: "mo-linear-map", name: "Linear Map", branch: "morph", parents: ["mo-morphism"], delta: "u(λx+μy) = λu(x)+μu(y)", fr: "application linéaire", prepa: "MPSI", seeAlso: [{ domain: "matrices", id: "mx-endomorphism" }] },
  { id: "mo-affine-map", name: "Affine Map", branch: "morph", parents: ["mo-morphism"], delta: "f(x) = u(x) + b, u linear", fr: "application affine", prepa: "MPSI" },
  { id: "mo-continuous-map", name: "Continuous Map", branch: "morph", parents: ["mo-morphism"], delta: "preserves limits", fr: "application continue", prepa: "MPSI", seeAlso: [{ domain: "analysis", id: "an-continuous" }] },
  { id: "mo-isometry", name: "Isometry", branch: "morph", parents: ["mo-morphism"], delta: "‖u(x)‖ = ‖x‖ (preserves distance)", fr: "isométrie", prepa: "MP", seeAlso: [{ domain: "algebra", id: "orthogonal-group" }] },
  { id: "mo-order-preserving-map", name: "Order-Preserving (Monotone) Map", branch: "morph", parents: ["mo-morphism"], blurb: "Monotone functions are covered extensively in CPGE, just not usually framed explicitly as 'morphisms of ordered sets'.", delta: "x ≤ y ⟹ f(x) ≤ f(y)" },
  { id: "mo-measurable-map", name: "Measurable Map", branch: "morph", parents: ["mo-morphism"], blurb: "Preimages of measurable sets are measurable — formal underpinning of a random variable, beyond what's developed explicitly in CPGE.", delta: "f⁻¹(measurable) is measurable" },
  { id: "mo-endomorphism", name: "Endomorphism", branch: "morph", parents: ["mo-morphism"], delta: "source = target", fr: "endomorphisme", prepa: "MPSI" },
  { id: "mo-isomorphism", name: "Isomorphism", branch: "morph", parents: ["mo-morphism"], blurb: "Bijective structure-preserving map whose inverse also preserves the structure.", delta: "bijective, structure-preserving both ways", fr: "isomorphisme", prepa: "MPSI" },
  { id: "mo-automorphism", name: "Automorphism", branch: "morph", parents: ["mo-endomorphism", "mo-isomorphism"], blurb: "An endomorphism that is also an isomorphism — invertible, structure-preserving, source = target.", delta: "endomorphism + isomorphism", fr: "automorphisme", prepa: "MPSI" },
];

const MORPHISMS_BRANCHES = {
  sub: { label: "Subobjects", color: "#5c7a3a" },
  quot: { label: "Quotients", color: "#b8305f" },
  morph: { label: "Morphisms", color: "#b8562f" },
};

// ---------------------------------------------------------------------------
// Domain registry
// ---------------------------------------------------------------------------
const DOMAINS = [
  D("algebra", "Algebraic Structures", "IS A (generalizes to)", "SPECIALIZATIONS", ALGEBRA_BRANCHES, ALGEBRA_NODES),
  D("analysis", "Analysis: Functions, Sequences & Series", "IMPLIES", "IMPLIED BY (stronger forms)", ANALYSIS_BRANCHES, ANALYSIS_NODES),
  D("numbers", "Numbers, Arithmetic & Combinatorics", "EMBEDS IN / BUILT FROM", "CONTAINS / BUILDS", NUMBERS_BRANCHES, NUMBERS_NODES),
  D("matrices", "Polynomials, Matrices & Linear Maps", "IS A", "SPECIALIZATIONS", MATRICES_BRANCHES, MATRICES_NODES),
  D("probability", "Probability", "IS A", "SPECIALIZATIONS", PROBABILITY_BRANCHES, PROBABILITY_NODES),
  D("morphisms", "Patterns: Sub/Quotient/Morphism", "IS A", "SPECIALIZATIONS", MORPHISMS_BRANCHES, MORPHISMS_NODES),
];
const domainByKey = Object.fromEntries(DOMAINS.map((d) => [d.key, d]));

function getAncestors(byId, id, acc = new Set()) {
  const n = byId[id];
  if (!n) return acc;
  for (const p of n.parents) {
    if (!acc.has(p)) {
      acc.add(p);
      getAncestors(byId, p, acc);
    }
  }
  return acc;
}
function getDescendants(nodes, id, acc = new Set()) {
  for (const n of nodes) {
    if (n.parents.includes(id) && !acc.has(n.id)) {
      acc.add(n.id);
      getDescendants(nodes, n.id, acc);
    }
  }
  return acc;
}
function computeDepths(byId, nodes) {
  const memo = {};
  function depth(id) {
    if (memo[id] !== undefined) return memo[id];
    const n = byId[id];
    if (!n.parents.length) return (memo[id] = 0);
    const d = 1 + Math.max(...n.parents.map((p) => depth(p)));
    memo[id] = d;
    return d;
  }
  nodes.forEach((n) => depth(n.id));
  return memo;
}

// ---------------------------------------------------------------------------
// Band layout. Column = depth (fixed). Inside each branch band we choose ROWS so
// that as many parent→child edges as possible are perfectly horizontal.
//   1. Horizontal edges: a maximum set of same-branch edges in which every node
//      has at most one horizontal edge coming in and one going out (otherwise the
//      line would run through a sibling). That is a path cover of the branch DAG,
//      i.e. a maximum-weight bipartite matching — solved exactly (Hungarian).
//      An edge may skip at most ONE empty column; ties prefer unskipped edges and
//      continuing along the longest line of descendants.
//   2. Each resulting path ("chain") sits on one row and reserves its columns.
//   3. Chains are dropped on rows greedily, then improved by local search: few
//      crossings, no edge through a node, short vertical jumps, compact band.
// Sections stay intact: every branch keeps its own band.
// ---------------------------------------------------------------------------
const NODE_HALF_W = 84;
const NODE_HALF_H = 16;

// Minimum-cost assignment on an n×n matrix (Hungarian algorithm). Returns row → column.
function hungarianMin(cost) {
  const n = cost.length;
  const u = new Array(n + 1).fill(0), v = new Array(n + 1).fill(0), p = new Array(n + 1).fill(0), way = new Array(n + 1).fill(0);
  for (let i = 1; i <= n; i++) {
    p[0] = i;
    let j0 = 0;
    const minv = new Array(n + 1).fill(Infinity);
    const used = new Array(n + 1).fill(false);
    do {
      used[j0] = true;
      const i0 = p[j0];
      let delta = Infinity, j1 = 0;
      for (let j = 1; j <= n; j++) {
        if (used[j]) continue;
        const cur = cost[i0 - 1][j - 1] - u[i0] - v[j];
        if (cur < minv[j]) { minv[j] = cur; way[j] = j0; }
        if (minv[j] < delta) { delta = minv[j]; j1 = j; }
      }
      for (let j = 0; j <= n; j++) {
        if (used[j]) { u[p[j]] += delta; v[j] -= delta; } else minv[j] -= delta;
      }
      j0 = j1;
    } while (p[j0] !== 0);
    do { const j1 = way[j0]; p[j0] = p[j1]; j0 = j1; } while (j0);
  }
  const rowToCol = new Array(n).fill(-1);
  for (let j = 1; j <= n; j++) rowToCol[p[j] - 1] = j - 1;
  return rowToCol;
}

function segHitsRect(ax, ay, bx, by, x0, y0, x1, y1) {
  let t0 = 0, t1 = 1;
  const dx = bx - ax, dy = by - ay;
  // left, right, top, bottom (Liang–Barsky)
  const P = [-dx, dx, -dy, dy], Q = [ax - x0, x1 - ax, ay - y0, y1 - ay];
  for (let i = 0; i < 4; i++) {
    if (P[i] === 0) { if (Q[i] < 0) return false; continue; }
    const r = Q[i] / P[i];
    if (P[i] < 0) { if (r > t1) return false; if (r > t0) t0 = r; }
    else { if (r < t0) return false; if (r < t1) t1 = r; }
  }
  return true;
}
function segsCross(ax, ay, bx, by, cx, cy, dx, dy) {
  const o1 = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
  const o2 = (bx - ax) * (dy - ay) - (by - ay) * (dx - ax);
  const o3 = (dx - cx) * (ay - cy) - (dy - cy) * (ax - cx);
  const o4 = (dx - cx) * (by - cy) - (dy - cy) * (bx - cx);
  return o1 * o2 < 0 && o3 * o4 < 0;
}

// Returns { rowOf: {nodeId: row}, rows: number of rows used }.
function layoutBranchRows(nodesInBranch, allNodes, byId, depthMemo, rankOf, myRank, colWidth, rowHeight) {
  const ids = nodesInBranch.map((n) => n.id);
  const n = ids.length;
  const idx = {};
  ids.forEach((id, i) => (idx[id] = i));
  const col = ids.map((id) => depthMemo[id]);
  const X = col.map((c) => c * colWidth);

  // same-branch edges, and for each node the direction (-1 above / +1 below) of links into other bands
  const edges = [];
  const cross = ids.map(() => []);
  nodesInBranch.forEach((node, ci) => {
    node.parents.forEach((p) => {
      if (idx[p] !== undefined) edges.push([idx[p], ci]);
      else cross[ci].push(rankOf[byId[p].branch] < myRank ? -1 : 1);
    });
  });
  allNodes.forEach((o) => {
    if (o.branch === nodesInBranch[0].branch) return;
    o.parents.forEach((p) => {
      if (idx[p] !== undefined) cross[idx[p]].push(rankOf[o.branch] < myRank ? -1 : 1);
    });
  });

  // ---- 1. horizontal edges = maximum-weight matching (tail → head) ----
  const kids = ids.map(() => []);
  edges.forEach(([p, c]) => kids[p].push(c));
  const height = new Array(n).fill(-1);
  const hOf = (i) => (height[i] >= 0 ? height[i] : (height[i] = kids[i].length ? 1 + Math.max(...kids[i].map(hOf)) : 0));
  for (let i = 0; i < n; i++) hOf(i);

  // importance of a node = how many structures descend from it anywhere in the whole tree
  // (Abelian Group underlies rings, modules, vector spaces… so it outranks Orthogonal Group)
  const childrenAll = {};
  allNodes.forEach((o) => o.parents.forEach((p) => (childrenAll[p] = childrenAll[p] || []).push(o.id)));
  const descCount = (id) => {
    const seen = new Set();
    const stack = [id];
    while (stack.length) for (const c of childrenAll[stack.pop()] || []) if (!seen.has(c)) { seen.add(c); stack.push(c); }
    return seen.size;
  };

  const BIG = 100000; // cardinality dominates every tie-break below
  const cost = Array.from({ length: n }, () => new Array(n).fill(0));
  edges.forEach(([p, c]) => {
    const gap = col[c] - col[p] - 1; // empty columns the line would cross
    if (gap > 1) return; // at most one empty space
    const m = kids[p].length, r = kids[p].indexOf(c); // kids are in data order
    const middle = m > 1 ? 10 * (1 - Math.abs(r - (m - 1) / 2) / ((m - 1) / 2)) : 10;
    cost[p][c] = -(BIG + (gap === 0 ? 400 : 0) + 25 * height[c] + 8 * Math.min(descCount(ids[c]), 40) + middle);
  });
  const assign = hungarianMin(cost);
  const next = new Array(n).fill(-1), prev = new Array(n).fill(-1);
  assign.forEach((j, i) => {
    if (j >= 0 && cost[i][j] < 0) { next[i] = j; prev[j] = i; }
  });
  const isH = new Set();
  edges.forEach(([p, c], e) => { if (next[p] === c) isH.add(e); });

  // ---- 2. chains ----
  const chainOf = new Array(n).fill(-1);
  const chains = [];
  for (let i = 0; i < n; i++) {
    if (prev[i] !== -1) continue;
    const members = [];
    for (let j = i; j !== -1; j = next[j]) { chainOf[j] = chains.length; members.push(j); }
    chains.push(members);
  }
  const K = chains.length;
  const head = chains.map((m) => col[m[0]]);
  const tail = chains.map((m) => col[m[m.length - 1]]);
  const parentChains = chains.map(() => new Set());
  edges.forEach(([p, c]) => { if (chainOf[p] !== chainOf[c]) parentChains[chainOf[c]].add(chainOf[p]); });

  // ---- 3a. greedy placement ----
  const rowOf = new Array(K).fill(null);
  // two chains may share a row only with at least one empty column between them
  const fits = (k, r) => {
    for (let m = 0; m < K; m++) {
      if (m === k || rowOf[m] !== r) continue;
      if (!(tail[k] + 2 <= head[m] || tail[m] + 2 <= head[k])) return false;
    }
    return true;
  };
  const placedRows = () => rowOf.filter((r) => r !== null);
  const order = chains.map((_, k) => k).sort((a, b) => head[a] - head[b] || chains[b].length - chains[a].length || chains[a][0] - chains[b][0]);
  for (const k of order) {
    const pr = [...parentChains[k]].filter((m) => rowOf[m] !== null).map((m) => rowOf[m]);
    const target = pr.length ? pr.reduce((a, b) => a + b, 0) / pr.length : 0;
    const pl = placedRows();
    const lo = Math.min(0, ...pl) - 1, hi = Math.max(0, ...pl) + 1;
    const cands = [];
    for (let r = lo; r <= hi; r++) cands.push(r);
    cands.sort((a, b) => Math.abs(a - target) - Math.abs(b - target) || b - a); // ties: below first
    rowOf[k] = cands.find((r) => fits(k, r));
  }

  // ---- 3b. local search ----
  const SAMPLES = [0, 0.25, 0.5, 0.75, 1].map((t) => { const u = 1 - t; return [u * u * u, 3 * u * u * t, 3 * u * t * t, t * t * t]; });
  const W = { span: 1, far: 0.3, up: 0.5, cross: 6, hit: 10, height: 0.8, pull: 0.15, order: 0.05 };
  // children of one parent, in data order: (u before v) should read top-to-bottom
  const sibPairs = [];
  kids.forEach((cs) => { for (let a = 0; a < cs.length; a++) for (let b = a + 1; b < cs.length; b++) if (chainOf[cs[a]] !== chainOf[cs[b]]) sibPairs.push([cs[a], cs[b]]); });
  const nE = edges.length;
  const ptsX = new Float64Array(5 * nE), ptsY = new Float64Array(5 * nE);
  const ny = new Float64Array(n);

  function score() {
    // Score on the rows as they will be DRAWN: distinct values renumbered 0,1,2… (the search
    // inserts rows at half-steps, which must not make a jump look shorter than it is).
    const vals = [...new Set(rowOf)].sort((a, b) => a - b);
    const rankOfVal = new Map(vals.map((v, i) => [v, i]));
    const rk = rowOf.map((v) => rankOfVal.get(v));
    const lo = 0, hi = vals.length - 1;
    for (let i = 0; i < n; i++) ny[i] = rk[chainOf[i]] * rowHeight;
    let s = W.height * vals.length;
    for (let e = 0; e < nE; e++) {
      const [p, c] = edges[e];
      const dr = rk[chainOf[c]] - rk[chainOf[p]];
      const dy = Math.abs(dr);
      s += W.span * dy + W.far * Math.max(0, dy - 1) * Math.max(0, dy - 1) + (dr < 0 ? W.up * dy : 0);
      const x1 = X[p] + NODE_HALF_W, x2 = X[c] - NODE_HALF_W, y1 = ny[p], y2 = ny[c], xm = (x1 + x2) / 2;
      for (let q = 0; q < 5; q++) {
        const b = SAMPLES[q];
        ptsX[e * 5 + q] = b[0] * x1 + (b[1] + b[2]) * xm + b[3] * x2;
        ptsY[e * 5 + q] = (b[0] + b[1]) * y1 + (b[2] + b[3]) * y2;
      }
    }
    for (let q = 0; q < sibPairs.length; q++) {
      if (rk[chainOf[sibPairs[q][0]]] > rk[chainOf[sibPairs[q][1]]]) s += W.order;
    }
    // pulls towards bands that sit above / below
    for (let i = 0; i < n; i++) {
      const r = rk[chainOf[i]];
      for (const d of cross[i]) s += W.pull * (d < 0 ? r - lo : hi - r);
    }
    // edge ↔ edge crossings
    for (let a = 0; a < nE; a++) {
      const [pa, ca] = edges[a];
      for (let b = a + 1; b < nE; b++) {
        const [pb, cb] = edges[b];
        if (pa === pb || ca === cb || pa === cb || ca === pb) continue;
        let ay0 = Math.min(ptsY[a * 5], ptsY[a * 5 + 4]), ay1 = Math.max(ptsY[a * 5], ptsY[a * 5 + 4]);
        let by0 = Math.min(ptsY[b * 5], ptsY[b * 5 + 4]), by1 = Math.max(ptsY[b * 5], ptsY[b * 5 + 4]);
        if (ay1 < by0 || by1 < ay0) continue;
        if (ptsX[a * 5 + 4] < ptsX[b * 5] || ptsX[b * 5 + 4] < ptsX[a * 5]) continue;
        let hit = false;
        for (let q = 0; q < 4 && !hit; q++) {
          for (let w = 0; w < 4; w++) {
            if (segsCross(ptsX[a * 5 + q], ptsY[a * 5 + q], ptsX[a * 5 + q + 1], ptsY[a * 5 + q + 1], ptsX[b * 5 + w], ptsY[b * 5 + w], ptsX[b * 5 + w + 1], ptsY[b * 5 + w + 1])) { hit = true; break; }
          }
        }
        if (hit) s += W.cross;
      }
    }
    // edge ↔ node overlaps (own endpoints excluded)
    for (let e = 0; e < nE; e++) {
      const [p, c] = edges[e];
      const exMin = ptsX[e * 5], exMax = ptsX[e * 5 + 4];
      for (let k = 0; k < n; k++) {
        if (k === p || k === c) continue;
        const rx0 = X[k] - NODE_HALF_W + 2, rx1 = X[k] + NODE_HALF_W - 2, ry0 = ny[k] - NODE_HALF_H + 2, ry1 = ny[k] + NODE_HALF_H - 2;
        if (exMax < rx0 || exMin > rx1) continue;
        for (let q = 0; q < 4; q++) {
          if (segHitsRect(ptsX[e * 5 + q], ptsY[e * 5 + q], ptsX[e * 5 + q + 1], ptsY[e * 5 + q + 1], rx0, ry0, rx1, ry1)) { s += W.hit; break; }
        }
      }
    }
    return s;
  }

  // hill-climb: move single chains / swap whole rows until nothing improves
  function improve() {
    let cur = score();
    for (let pass = 0; pass < 8; pass++) {
      let improved = false;
      // move one chain to another row (existing, or newly inserted between / beyond rows)
      for (let k = 0; k < K; k++) {
        const old = rowOf[k];
        const used = [...new Set(rowOf)];
        const cand = new Set();
        used.forEach((v) => { cand.add(v); cand.add(v - 0.5); cand.add(v + 0.5); });
        let bestR = old, bestS = cur;
        for (const r of [...cand].sort((a, b) => a - b)) {
          if (r === old || !fits(k, r)) continue;
          rowOf[k] = r;
          const s = score();
          if (s < bestS - 1e-9) { bestS = s; bestR = r; }
        }
        rowOf[k] = bestR;
        if (bestR !== old) { cur = bestS; improved = true; }
      }
      // swap two whole rows
      const used = [...new Set(rowOf)].sort((a, b) => a - b);
      for (let i = 0; i < used.length; i++) {
        for (let j = i + 1; j < used.length; j++) {
          const A = used[i], B = used[j];
          const saved = rowOf.slice();
          for (let k = 0; k < K; k++) { if (saved[k] === A) rowOf[k] = B; else if (saved[k] === B) rowOf[k] = A; }
          const s = score();
          if (s < cur - 1e-9) { cur = s; improved = true; } else for (let k = 0; k < K; k++) rowOf[k] = saved[k];
        }
      }
      if (!improved) break;
    }
    return cur;
  }

  if (K > 1) improve();

  // ---- compress: drop empty rows, renumber 0.. ----
  const distinct = [...new Set(rowOf)].sort((a, b) => a - b);
  const renum = new Map(distinct.map((v, i) => [v, i]));
  const rowOfNode = {};
  ids.forEach((id, i) => (rowOfNode[id] = renum.get(rowOf[chainOf[i]])));
  return { rowOf: rowOfNode, rows: distinct.length, horizontalEdges: isH.size, sameBranchEdges: nE };
}

// =============================================================================
// i18n — French translations. English lives in the node data above; this block
// maps node id -> [name, blurb, delta]. `null` = keep the original (symbolic or
// absent text). Layout never depends on language (it uses the English names).
// =============================================================================
const FR_NODES = {
  // ---- Algebra ----
  "set": ["Ensemble", "Une collection d'éléments sans aucune structure imposée.", "aucun axiome — juste l'appartenance"],
  "binary-relation": ["Relation binaire", "Une partie de E×E décrivant quelles paires d'éléments sont en relation.", null],
  "preorder": ["Préordre", "Réflexive et transitive, mais pas nécessairement antisymétrique — l'échafaudage commun aux ordres et aux équivalences.", "+ réflexive, transitive"],
  "equivalence-relation": ["Relation d'équivalence", "Un préordre qui est aussi symétrique — partitionne l'ensemble en classes. Correspond exactement à une partition de E.", "+ symétrique : xRy ⟹ yRx"],
  "quotient-set": ["Ensemble quotient", "L'ensemble E/∼ des classes d'équivalence d'un ensemble pour une relation d'équivalence — le mécanisme derrière ℤ/nℤ.", "éléments = classes d'équivalence"],
  "poset": ["Ensemble ordonné", "Un préordre qui est de plus antisymétrique.", "+ antisymétrique : x≤y et y≤x ⟹ x=y"],
  "total-order": ["Ensemble totalement ordonné", "Un ensemble ordonné dans lequel deux éléments quelconques sont comparables.", "+ totalité : x,y toujours comparables"],
  "well-order": ["Ensemble bien ordonné", "Toute partie non vide admet un plus petit élément — fondement de la récurrence sur ℕ.", "+ toute partie non vide a un plus petit élément"],
  "lattice": ["Treillis", "Un ensemble ordonné dans lequel toute paire d'éléments admet une borne supérieure (∨) et une borne inférieure (∧). Généralement périphérique au programme.", "+ toute paire a une borne sup ∨ et inf ∧"],
  "distributive-lattice": ["Treillis distributif", "Un treillis où ∨ et ∧ sont mutuellement distributifs.", "+ ∨, ∧ mutuellement distributifs"],
  "boolean-algebra": ["Algèbre de Boole", "Un treillis distributif complémenté — modélise la logique classique et l'algèbre des ensembles.", "+ complémentation, bornes 0 et 1"],
  "complete-lattice": ["Treillis complet", "Toute partie (et pas seulement toute paire) admet une borne supérieure et une borne inférieure.", "+ bornes sup/inf arbitraires existent"],
  "magma": ["Magma", "Un ensemble muni d'une unique loi interne — la « loi de composition interne », première brique du chapitre sur les structures.", "+ loi interne •"],
  "semigroup": ["Demi-groupe", "Un magma dont la loi est associative — une étape vers le monoïde, rarement nommée seule en cours.", "+ associativité : (a•b)•c = a•(b•c)"],
  "monoid": ["Monoïde", "Un demi-groupe avec élément neutre — par ex. (ℕ,+) ou (ℕ,×), des monoïdes qui ne sont pas des groupes.", "+ élément neutre e : e•a = a•e = a"],
  "group": ["Groupe", "Un monoïde dans lequel tout élément est inversible.", "+ inverses : ∀a ∃a⁻¹, a•a⁻¹ = e"],
  "abelian-group": ["Groupe abélien (commutatif)", "Un groupe dont la loi est commutative.", "+ commutativité : a•b = b•a"],
  "cyclic-group": ["Groupe cyclique", "Engendré par un seul élément. L'exemple classique de prépa : 𝕌ₙ, les racines n-ièmes de l'unité — un sous-groupe cyclique fini de ℂ×.", "+ ∃g : tout élément = gⁿ"],
  "symmetric-group": ["Groupe symétrique Sₙ", "Le groupe des permutations de {1,...,n} pour la composition — non abélien dès n≥3, central dans le chapitre sur le déterminant. Toute permutation se décompose en cycles disjoints et en transpositions ; la signature ε : Sₙ→{-1,1} est un morphisme de groupes.", "groupe particulier : toutes les bijections d'un ensemble fini"],
  "alternating-group": ["Groupe alterné Aₙ", "Le sous-groupe de Sₙ formé des permutations paires — noyau du morphisme signature.", "+ ε(σ) = +1 (permutations paires)"],
  "general-linear-group": ["Groupe linéaire GL(E)", "Les applications linéaires inversibles d'un espace vectoriel E (ou les matrices n×n inversibles), pour la composition.", "groupe particulier : automorphismes d'un espace vectoriel"],
  "orthogonal-group": ["Groupe orthogonal O(E)", "Les isométries linéaires d'un espace euclidien — applications qui conservent le produit scalaire. A orthogonale ⟺ AᵀA=I ⟺ A⁻¹=Aᵀ.", "groupe particulier : isométries d'un espace euclidien"],
  "special-orthogonal-group": ["Groupe spécial orthogonal SO(n)", "Le sous-groupe de O(n) de déterminant +1 — les rotations, par opposition aux réflexions.", "+ det = +1 (rotations uniquement)"],
  "unitary-group": ["Groupe unitaire U(n)", "Les isométries linéaires d'un espace hermitien — l'analogue complexe de O(n). Approfondi en MP*.", "groupe particulier : isométries d'un espace hermitien"],
  "free-group": ["Groupe libre", "Engendré par un ensemble sans aucune relation autre que les axiomes de groupe.", "+ aucune relation entre les générateurs"],
  "lie-group": ["Groupe de Lie", "Un groupe qui est aussi une variété différentielle, avec des opérations lisses.", "+ structure de variété lisse ; •, ⁻¹ lisses"],
  "topological-group": ["Groupe topologique", "Un groupe muni d'une topologie rendant • et l'inverse continus.", "+ topologie ; •, ⁻¹ continus"],
  "semiring": ["Semi-anneau", "Deux lois de type monoïde (+, ×) avec distributivité, mais + n'a pas forcément d'opposés — pur échafaudage ici. ℕ est l'exemple type.", "+, × avec distributivité ; pas d'opposés additifs"],
  "ring": ["Anneau", "Groupe abélien pour +, monoïde pour ×, × distributive sur +. La convention française suppose toujours un élément neutre 1 pour ×.", "+ monoïde multiplicatif ; distributivité"],
  "rng": ["Pseudo-anneau (rng)", "Un anneau sans exigence d'élément neutre multiplicatif — pratiquement jamais utilisé en CPGE.", "× n'a pas forcément d'élément neutre 1"],
  "comm-ring": ["Anneau commutatif", "Un anneau où la multiplication est commutative.", "+ a×b = b×a"],
  "domain": ["Anneau intègre", "Un anneau commutatif non nul sans diviseurs de zéro. ℤ et K[X] sont les deux exemples de référence.", "+ ab=0 ⟹ a=0 ou b=0 ; 1≠0"],
  "gcd-domain": ["Anneau à pgcd", "Anneau intègre où toute paire d'éléments admet un pgcd — la théorie abstraite derrière pgcd(a,b) dans ℤ et K[X].", "+ pgcd(a,b) existe pour tous a,b"],
  "ufd": ["Anneau factoriel", "Tout élément se factorise de façon unique en irréductibles — démontré concrètement pour ℤ (nombres premiers) et K[X] (polynômes irréductibles), mais le terme abstrait n'est pas du vocabulaire standard de prépa.", "+ factorisation unique en irréductibles"],
  "pid": ["Anneau principal", "Tout idéal est engendré par un seul élément. Démontré explicitement pour ℤ (« les idéaux de ℤ sont les nℤ ») et pour K[X] — le fait est au cœur du programme de MPSI même si « anneau principal » n'est pas une structure abstraite nommée.", "+ tout idéal = (a) pour un certain a"],
  "euclidean-domain": ["Anneau euclidien", "Un anneau intègre admettant un algorithme de division avec reste — la division euclidienne dans ℤ comme dans K[X] est une pierre angulaire des chapitres d'arithmétique et de polynômes.", "+ stathme euclidien permettant la division avec reste"],
  "field": ["Corps", "Un anneau commutatif où tout élément non nul est inversible.", "+ tout élément non nul a un inverse multiplicatif"],
  "finite-field": ["Corps fini", "Un corps ayant un nombre fini d'éléments. En prépa : ℤ/pℤ est un corps exactement quand p est premier.", "+ |F| = pⁿ fini"],
  "algebraically-closed-field": ["Corps algébriquement clos", "Tout polynôme non constant admet une racine dans le corps. La clôture algébrique de ℂ est le théorème de d'Alembert–Gauss, énoncé et utilisé (admis) en MPSI.", "+ tout polynôme de degré ≥1 a une racine"],
  "ordered-field": ["Corps ordonné", "Un corps muni d'un ordre total compatible — l'arrière-plan implicite dès qu'on manipule des inégalités dans ℝ.", "+ ordre total ≤ compatible"],
  "real-closed-field": ["Corps réel clos", "Corps ordonné où tout élément positif a une racine carrée et tout polynôme de degré impair a une racine (ℝ en est l'exemple modèle).", "+ racines carrées des positifs ; racines des polynômes de degré impair"],
  "division-ring": ["Corps non commutatif (anneau à division)", "Un anneau où tout élément non nul est inversible — des « corps » non commutatifs (par ex. les quaternions).", "+ tout élément non nul inversible (× pas forcément commutative)"],
  "ordered-ring": ["Anneau ordonné", "Un anneau muni d'un ordre total compatible.", "+ ordre total ≤ compatible"],
  "local-ring": ["Anneau local", "Un anneau commutatif possédant un unique idéal maximal.", "+ unique idéal maximal"],
  "noetherian-ring": ["Anneau noethérien", "Toute suite croissante d'idéaux stationne (de façon équivalente : les idéaux sont de type fini).", "+ condition de chaîne ascendante sur les idéaux"],
  "boolean-ring": ["Anneau de Boole", "Tout élément est idempotent : a² = a.", "+ a² = a pour tout a"],
  "z-mod-n": ["ℤ/nℤ", "Les entiers modulo n, construits comme ensemble quotient de ℤ par la relation de congruence. Un corps exactement quand n est premier.", "quotient de ℤ ; corps ⟺ n premier"],
  "poly-ring": ["Anneau des polynômes K[X]", "Les polynômes sur un corps K. À la fois anneau euclidien (division euclidienne des polynômes) et K-algèbre — l'un des deux anneaux centraux de MPSI. De dimension infinie comme K-espace vectoriel.", "division euclidienne, Bézout, irréductibles"],
  "poly-ring-degree-n": ["Kₙ[X] (degré ≤ n)", "Les polynômes de degré au plus n — un sous-espace de dimension finie (n+1) de K[X], non stable par multiplication donc pas un sous-anneau.", "sous-espace de dimension finie de K[X], dim = n+1"],
  "rational-fraction-field": ["Corps des fractions rationnelles K(X)", "Le corps des fractions de K[X] — fractions rationnelles, étudiées via la décomposition en éléments simples.", "corps des fractions de K[X]"],
  "matrix-ring": ["Anneau des matrices Mₙ(K)", "Les matrices carrées n×n sur K pour +, × — non commutatif dès n≥2, et simultanément une K-algèbre.", "non commutatif pour n≥2"],
  "endomorphism-algebra": ["Algèbre des endomorphismes L(E)", "Les endomorphismes linéaires de E pour la composition — un anneau (non commutatif si dim E ≥ 2) et une K-algèbre.", "anneau (L(E),+,∘) ; non comm. si dim E≥2"],
  "module": ["Module (sur un anneau R)", "Un groupe abélien muni d'une multiplication externe par un anneau, compatible avec + et ×. Parfois évoqué comme « ce que généralisent les espaces vectoriels » — non développé en CPGE.", "+ action externe de l'anneau R"],
  "vector-space": ["Espace vectoriel", "Un module dont l'anneau de scalaires est un corps — l'épine dorsale du programme de MPSI/MP.", "scalaires restreints à un corps"],
  "algebra-over-field": ["Algèbre (sur un corps)", "Un espace vectoriel muni d'une multiplication bilinéaire compatible — exactement ce que sont K[X], Mₙ(K) et L(E).", "+ multiplication bilinéaire compatible avec les scalaires"],
  "associative-algebra": ["Algèbre associative", "Une algèbre dont la multiplication est associative.", "+ associativité de ×"],
  "lie-algebra": ["Algèbre de Lie", "Un espace vectoriel muni d'un crochet bilinéaire alterné [·,·] vérifiant l'identité de Jacobi.", "+ crochet [x,y], identité de Jacobi, [x,x]=0"],
  "normed-space": ["Espace vectoriel normé", "Un espace vectoriel muni d'une norme ‖·‖. Officiellement : « la topologie est étudiée dans le cadre général des espaces vectoriels normés » — c'est ce cadre, et non les espaces métriques abstraits, qui est le vrai cadre topologique de MP.", "+ norme ‖v‖ vérifiant l'inégalité triangulaire"],
  "banach-space": ["Espace de Banach", "Un espace normé complet pour sa distance induite. Les espaces normés de dimension finie sont automatiquement complets — utilisé implicitement plutôt que nommé longuement.", "+ complétude pour la distance induite"],
  "hilbert-space": ["Espace de Hilbert", "Un espace préhilbertien complet pour sa norme — la généralisation en dimension infinie de l'espace euclidien.", "+ complétude pour la norme du produit scalaire"],
  "bilinear-space": ["Espace muni d'une forme bilinéaire", "Un espace vectoriel E muni d'une forme bilinéaire B : E×E → K.", "+ forme bilinéaire B(x,y)"],
  "symmetric-bilinear-space": ["Espace muni d'une forme bilinéaire symétrique", "Un espace bilinéaire où B(x,y) = B(y,x).", null],
  "quadratic-space": ["Espace muni d'une forme quadratique", "La structure équivalente via Q(x) = B(x,x) ; on retrouve B par polarisation. Traité plus légèrement que la théorie des produits scalaires.", null],
  "sesquilinear-space": ["Espace muni d'une forme sesquilinéaire", "Un espace vectoriel complexe muni d'une forme linéaire en une variable et semi-linéaire en l'autre. Niveau MP*.", "+ forme sesquilinéaire"],
  "hermitian-form-space": ["Espace muni d'une forme hermitienne", "Un espace sesquilinéaire où la forme vérifie la symétrie hermitienne B(x,y) = conj(B(y,x)). Niveau MP*.", "+ symétrie hermitienne"],
  "inner-product-space": ["Espace préhilbertien réel", "Un espace bilinéaire symétrique où la forme est définie positive : ⟨x,x⟩ > 0 pour x≠0.", "+ définie positive : ⟨x,x⟩ > 0"],
  "complex-inner-product-space": ["Espace préhilbertien complexe", "Un espace muni d'une forme hermitienne définie positive.", "+ forme hermitienne définie positive"],
  "euclidean-space": ["Espace euclidien", "Un espace préhilbertien réel de dimension finie — bases orthonormées, projections orthogonales, adjoints, matrices de Gram, groupe orthogonal. En dimension finie E = F ⊕ F⊥.", "+ dimension finie"],
  "hermitian-space": ["Espace hermitien", "Un espace préhilbertien complexe de dimension finie — l'analogue complexe de l'espace euclidien, niveau MP*.", "+ dimension finie"],
  "affine-space": ["Espace affine", "Un ensemble E de points muni d'un espace vectoriel associé agissant simplement transitivement par translations — le cadre formel de la géométrie classique (points vs vecteurs). Un sous-espace vectoriel est un sous-espace affine passant par l'origine ; un sous-espace affine général ne contient pas forcément 0.", "+ espace vectoriel agissant par translations"],
  "euclidean-affine-space": ["Espace affine euclidien", "Un espace affine dont l'espace vectoriel associé est euclidien — distances et angles entre points.", "+ espace vectoriel associé euclidien"],
  "topological-space": ["Espace topologique", "Un ensemble muni d'une famille d'ouverts vérifiant les axiomes de réunion et d'intersection — la topologie générale abstraite ne fait pas partie du programme de CPGE.", "+ topologie τ (ouverts)"],
  "metric-space": ["Espace métrique", "Un ensemble muni d'une distance d(x,y). La prépa travaille surtout via la distance induite par une norme sur un espace vectoriel, plutôt qu'avec des espaces métriques abstraits.", "+ distance d(x,y) ≥ 0, symétrique, inégalité triangulaire"],
  "complete-metric-space": ["Espace métrique complet", "Toute suite de Cauchy converge dans l'espace — sous-tend la complétude des espaces normés de dimension finie, utilisée implicitement.", "+ toute suite de Cauchy converge"],
  "hausdorff-space": ["Espace séparé (de Hausdorff)", "Deux points distincts peuvent être séparés par des ouverts disjoints.", "+ axiome de séparation T2"],
  "compact-space": ["Espace compact", "Tout recouvrement ouvert admet un sous-recouvrement fini. Étudié spécifiquement dans les espaces vectoriels normés (en dimension finie : compact ⟺ fermé borné ; caractérisations de Bolzano–Weierstrass / Borel–Lebesgue).", "+ tout recouvrement ouvert a un sous-recouvrement fini"],
  "connected-space": ["Espace connexe", "Ne peut pas être partitionné en deux ouverts disjoints non vides — la notion topologique générale (la connexité par arcs, ci-dessous, est ce qui est réellement enseigné).", "+ pas de séparation en deux ouverts disjoints"],
  "path-connected-space": ["Espace connexe par arcs", "Deux points quelconques sont reliés par un chemin continu. Dans un espace vectoriel normé, cela généralise le théorème des valeurs intermédiaires — « un dessin pertinent peut valoir preuve ».", "+ deux points quelconques reliés par un chemin continu"],
  "manifold": ["Variété topologique", "Localement homéomorphe à l'espace euclidien ℝⁿ.", "+ localement homéomorphe à ℝⁿ"],
  "smooth-manifold": ["Variété différentielle", "Une variété munie d'un atlas dont les changements de cartes sont lisses (C∞).", "+ changements de cartes lisses (C∞)"],
  "riemannian-manifold": ["Variété riemannienne", "Une variété différentielle munie d'un produit scalaire variant de façon lisse sur les espaces tangents.", "+ tenseur métrique g sur les espaces tangents"],
  "measurable-space": ["Espace probabilisable", "Un ensemble Ω muni d'une tribu (σ-algèbre) : une famille de parties stable par complémentaire et réunion dénombrable. Manipuler des tribus dans l'abstrait n'est pas un objectif du programme — c'est le cas discret/dénombrable qui compte.", "+ tribu 𝒜 (stable par complémentaire et réunion dénombrable)"],
  "probability-space": ["Espace probabilisé", "Un espace probabilisable muni d'une probabilité P : 𝒜 → [0,1] avec P(Ω)=1 et σ-additivité.", "+ probabilité P, P(Ω)=1, σ-additive"],
  "category": ["Catégorie", "Des objets et des morphismes avec composition, vérifiant associativité et identité — la structure de saveur algébrique la plus générale. Hors programme de CPGE.", "objets + morphismes + composition + identité"],
  "groupoid": ["Groupoïde", "Une catégorie dans laquelle tout morphisme est inversible.", "+ tout morphisme inversible"],
  "monoidal-category": ["Catégorie monoïdale", "Une catégorie munie d'un produit tensoriel ⊗ et d'un objet unité, associatif à isomorphisme cohérent près.", "+ ⊗, objet unité, isomorphismes de cohérence"],
  "abelian-category": ["Catégorie abélienne", "Une catégorie (comme R-Mod) avec objet nul, noyaux, conoyaux et biproduits — là où l'algèbre homologique fonctionne.", "+ objet nul, (co)noyaux, biproduits"],

  // ---- Analysis ----
  "an-function": ["Application / fonction", "f : E→F, associant à chaque x∈E un unique f(x)∈F. Objets associés : ensemble de départ, ensemble d'arrivée, image f(A), image réciproque f⁻¹(B), restriction, graphe.", "associe f(x) ∈ F à chaque x ∈ E"],
  "an-injective": ["Application injective", null, null],
  "an-surjective": ["Application surjective", null, null],
  "an-bijective": ["Application bijective", "Injective et surjective — de façon équivalente, f⁻¹ existe en tant qu'application.", "injective + surjective"],
  "an-real-function": ["Fonction réelle / complexe", "f : I ⊆ ℝ ou ℂ → ℝ ou ℂ. Se ramifie en propriétés algébriques (bornée, monotone, convexe, périodique) et en régularité (continuité, dérivabilité).", "départ/arrivée dans ℝ ou ℂ"],
  "an-bounded": ["Fonction bornée", null, null],
  "an-monotone": ["Fonction monotone", null, "+ croissante ou décroissante"],
  "an-convex": ["Fonction convexe", "Caractérisée par la monotonie de f′, ou le signe de f″.", null],
  "an-periodic": ["Fonction périodique", null, null],
  "an-continuous": ["Fonction continue", "x→a ⟹ f(x)→f(a). L'image continue d'un intervalle est un intervalle ; l'image continue d'un compact est compacte (et atteint ses bornes).", null],
  "an-uniformly-continuous": ["Fonction uniformément continue", "Continue sur un compact ⟹ uniformément continue (Heine).", "+ uniforme en x (pas seulement ponctuelle)"],
  "an-lipschitz": ["Fonction lipschitzienne", null, null],
  "an-homeomorphism": ["Homéomorphisme", "Bijective, continue, de réciproque continue.", "bijective + continue + réciproque continue"],
  "an-differentiable": ["Fonction dérivable", "f′(a) = lim (f(a+h)-f(a))/h existe.", "+ f′(a) existe"],
  "an-c1": ["Fonction de classe C¹", null, "+ f′ existe et est continue"],
  "an-ck": ["Fonction de classe Cᵏ", null, "+ k fois continûment dérivable"],
  "an-cinf": ["Fonction de classe C∞ (lisse)", null, "+ Cᵏ pour tout k"],
  "an-analytic": ["Fonction analytique", "Localement égale à sa propre série entière (série de Taylor) convergente. C∞ n'implique PAS analytique — la réciproque est fausse.", "+ localement égale à sa série entière"],
  "an-sequence": ["Suite", "u : ℕ→ℝ ou ℂ. Une suite extraite est la composée avec un φ : ℕ→ℕ strictement croissant.", "u : ℕ → ℝ ou ℂ"],
  "an-bounded-seq": ["Suite bornée", null, null],
  "an-convergent-seq": ["Suite convergente", "Toute suite convergente est bornée ; la réciproque est fausse.", "+ uₙ → l pour un certain l"],
  "an-cauchy-seq": ["Suite de Cauchy", "Dans ℝ ou ℂ : Cauchy ⟺ convergente (complétude) — les deux notions coïncident.", "+ |uₙ-uₘ|→0 quand n,m→∞"],
  "an-monotone-seq": ["Suite monotone", "Monotone + bornée ⟹ convergente (critère classique).", "+ croissante ou décroissante"],
  "an-adjacent-seq": ["Suites adjacentes", "L'une croissante, l'autre décroissante, différence → 0 — toutes deux convergent vers la même limite.", "+ couple, différence → 0"],
  "an-series": ["Série numérique Σuₙ", "Étudiée via sa suite de sommes partielles Sₙ = Σₖ₌₀ⁿ uₖ.", "définie via les sommes partielles Sₙ"],
  "an-convergent-series": ["Série convergente", null, "+ (Sₙ) converge"],
  "an-abs-convergent-series": ["Série absolument convergente", "Σ|uₙ| converge ⟹ Σuₙ converge (pas réciproquement).", "+ Σ|uₙ| converge"],
  "an-conditionally-convergent": ["Série semi-convergente", "Convergente mais pas absolument convergente — par ex. la série harmonique alternée.", "convergente, mais Σ|uₙ| diverge"],
  "an-summable-family": ["Famille sommable", "Généralise la convergence absolue à un ensemble d'indices dénombrable quelconque, indépendamment de l'ordre — central dans le chapitre de probabilités de MP pour les sommes doubles.", "somme indépendante de l'ordre sur un ensemble d'indices dénombrable"],
  "an-pointwise-conv": ["Suite de fonctions — convergence simple", null, null],
  "an-uniform-conv": ["Convergence uniforme", "sup|fₙ(x)-f(x)|→0. Préserve la continuité de la limite ; permet d'échanger limite et intégrale.", null],
  "an-normal-conv": ["Convergence normale (séries de fonctions)", "Σ‖fₙ‖∞ < ∞ — l'outil de travail standard pour les séries de fonctions.", null],
  "an-power-series": ["Série entière Σaₙ(x-a)ⁿ", "A un rayon de convergence R : convergence absolue pour |x-a|<R, divergence pour |x-a|>R, convergence normale sur tout disque (ou segment) fermé strictement inclus dans le disque de convergence.", "+ rayon de convergence R"],
  "an-ode": ["Équation différentielle", "Une équation reliant une fonction à sa (ses) dérivée(s).", "relie y à y′ (et au-delà)"],
  "an-ode-1st-order": ["Équation différentielle d'ordre 1 : y′=F(x,y)", null, null],
  "an-ode-linear-1st": ["Équation différentielle linéaire d'ordre 1", "y′+a(x)y=b(x). Solution générale = une solution particulière + les solutions de l'équation homogène.", null],
  "an-ode-linear-2nd": ["Équation différentielle linéaire d'ordre 2", "y″+a(x)y′+b(x)y=c(x). À coefficients constants, le polynôme caractéristique pilote les solutions homogènes.", null],
  "an-ode-system": ["Système différentiel linéaire X′=AX+B", "À valeurs vectorielles ; pour A constante, la solution homogène est X(t)=e^{tA}X(0). Diagonaliser ou trigonaliser A simplifie le calcul de e^{tA}.", "à valeurs vectorielles, X′ = AX + B"],
  "an-multivar-function": ["Fonction de plusieurs variables", null, null],
  "an-partial-derivatives": ["Admet des dérivées partielles", "Nécessaire mais PAS suffisant pour la différentiabilité.", "+ les ∂f/∂xᵢ existent"],
  "an-differentiable-multivar": ["Différentiable (plusieurs variables)", "⟹ continue ; représentée par la matrice jacobienne ; pour f scalaire, df_a(h) = ⟨∇f(a),h⟩ en coordonnées euclidiennes.", "+ différentiable (jacobienne existe)"],
  "an-c1-multivar": ["Classe C¹ (plusieurs variables)", null, "+ la jacobienne dépend continûment de x"],
  "an-parametrized-curve": ["Courbe paramétrée", "γ : I→ℝⁿ. Un graphe {(x,f(x))} est le cas particulier γ(x)=(x,f(x)).", null],
  "an-regular-curve": ["Courbe régulière", "γ′(t)≠0 en tout point — admet une tangente bien définie.", "+ γ′(t) ≠ 0 partout"],

  // ---- Numbers ----
  "nu-N": ["ℕ", "Entiers naturels, 0 inclus selon la convention française. Un semi-anneau commutatif — pas de soustraction.", "semi-anneau commutatif"],
  "nu-Z": ["ℤ", "Les entiers relatifs — ℕ étendu aux négatifs. Un anneau intègre, pas un corps.", "anneau intègre"],
  "nu-Q": ["ℚ", "Les rationnels — ℤ étendu aux inverses multiplicatifs. Un corps.", "corps"],
  "nu-R": ["ℝ", "Les réels — le corps ordonné complet : toute partie non vide majorée admet une borne supérieure. Totalement ordonné ; ℚ et ℝ∖ℚ sont tous deux denses dans ℝ.", "corps ordonné complet"],
  "nu-C": ["ℂ", "Les nombres complexes — ℝ étendu par i, i²=-1. Algébriquement clos (d'Alembert–Gauss : tout polynôme non constant est scindé), mais n'admet aucun ordre total compatible avec la structure de corps.", "corps algébriquement clos, non ordonnable"],
  "nu-divisibility": ["Divisibilité", "a | b : a divise b.", null],
  "nu-prime": ["Nombre premier", "Divisible seulement par 1 et par lui-même.", "diviseurs = {1, p}"],
  "nu-gcd": ["PGCD", null, "plus grand commun diviseur"],
  "nu-coprime": ["Entiers premiers entre eux", null, null],
  "nu-lcm": ["PPCM", null, "plus petit commun multiple"],
  "nu-bezout": ["Identité de Bézout", null, null],
  "nu-euclidean-algo": ["Algorithme d'Euclide", "Calcule pgcd(a,b) par divisions euclidiennes successives.", "divisions successives"],
  "nu-gauss-lemma": ["Lemme de Gauss", null, "a|bc et pgcd(a,b)=1 ⟹ a|c"],
  "nu-prime-factorization": ["Décomposition en facteurs premiers", "Tout entier >1 se factorise de façon unique en nombres premiers.", "factorisation unique en nombres premiers"],
  "nu-valuation": ["Valuation p-adique", null, "vₚ(n) = exposant de p dans n"],
  "nu-congruence": ["Congruence modulo n", "a≡b (mod n) ⟺ n|(a-b) — une relation d'équivalence sur ℤ dont le quotient est ℤ/nℤ.", null],
  "nu-diophantine": ["Équation diophantienne", null, "équation résolue dans ℤ"],
  "nu-countable": ["Ensemble dénombrable", "Fini, ou en bijection avec une partie de ℕ.", "fini ou en bijection avec une partie de ℕ"],
  "nu-finite-set": ["Ensemble fini", "En bijection avec {1,...,n} pour un certain n.", "en bijection avec {1,...,n}"],
  "nu-countably-infinite": ["Ensemble infini dénombrable", null, "en bijection avec ℕ lui-même"],
  "nu-uncountable": ["Ensemble non dénombrable", "Non dénombrable — par ex. ℝ, démontré par l'argument diagonal de Cantor. Explicitement signalé dans le programme de MP : « ℝ n'est pas dénombrable ».", "pas en bijection avec une partie de ℕ"],
  "nu-permutation": ["Permutation", "Une bijection d'un ensemble fini dans lui-même.", "bijection E → E"],
  "nu-arrangement": ["Arrangement", "Une sélection ordonnée de k éléments distincts parmi un ensemble de taille n (suite injective).", "sélection ordonnée sans répétition"],
  "nu-combination": ["Combinaison", "Une sélection non ordonnée de k éléments — une partie à k éléments.", "sélection non ordonnée (partie à k éléments)"],
  "nu-binomial-coeff": ["Coefficient binomial", "C(n,k) : nombre de parties à k éléments d'un ensemble à n éléments. Gouverne la formule du binôme.", "dénombre les parties à k éléments d'un n-ensemble"],

  // ---- Matrices & linear maps ----
  "mx-polynomial": ["Polynôme", "Une expression formelle P=Σ aₖXᵏ sur un corps K.", null],
  "mx-root": ["Racine d'un polynôme", "a est racine de P ⟺ (X-a) | P.", null],
  "mx-multiple-root": ["Racine de multiplicité m", null, "(X-a)ᵐ | P mais (X-a)^(m+1) ∤ P"],
  "mx-irreducible-poly": ["Polynôme irréductible", "Ne se factorise pas en deux polynômes non inversibles. Sur ℂ : degré 1 uniquement. Sur ℝ : degré 1 ou 2.", "aucune factorisation non triviale"],
  "mx-rational-function": ["Fraction rationnelle P/Q", "Un quotient de polynômes, Q≠0 — pôles, zéros, partie entière, décomposition en éléments simples.", "P/Q, Q ≠ 0"],
  "mx-linear-form": ["Forme linéaire", "Une application linéaire E→K.", "u : E → K linéaire"],
  "mx-endomorphism": ["Endomorphisme", "Une application linéaire E→E.", "u : E → E linéaire"],
  "mx-automorphism-lin": ["Automorphisme (de E)", null, "+ inversible"],
  "mx-projection": ["Projecteur", null, null],
  "mx-symmetry": ["Symétrie (involution)", null, null],
  "mx-nilpotent-endo": ["Endomorphisme nilpotent", null, "uᵐ = 0 pour un certain m"],
  "mx-homothety": ["Homothétie", null, null],
  "mx-triangularizable": ["Endomorphisme trigonalisable", "∃ une base dans laquelle la matrice est triangulaire supérieure. Sur un corps algébriquement clos : équivalent à un polynôme caractéristique scindé (Cayley–Hamilton : χᵤ(u)=0).", "∃ base où la matrice est triangulaire supérieure"],
  "mx-diagonalizable": ["Endomorphisme diagonalisable", "∃ une base de vecteurs propres. Caractérisé par un polynôme annulateur scindé à racines simples.", "∃ base de vecteurs propres"],
  "mx-matrix": ["Matrice", "Un tableau rectangulaire (aᵢⱼ) ∈ Mₙ,ₚ(K). Après choix de bases, toute application linéaire est représentée par une matrice ; composition ↔ produit matriciel, changement de base ↔ matrices de passage.", null],
  "mx-square-matrix": ["Matrice carrée", null, null],
  "mx-diagonal-matrix": ["Matrice diagonale", null, "nulle hors de la diagonale"],
  "mx-triangular-matrix": ["Matrice triangulaire", null, "nulle sous (ou sur) la diagonale"],
  "mx-symmetric-matrix": ["Matrice symétrique", null, null],
  "mx-skew-symmetric-matrix": ["Matrice antisymétrique", null, null],
  "mx-orthogonal-matrix": ["Matrice orthogonale", null, null],
  "mx-hermitian-matrix": ["Matrice hermitienne", "Niveau MP*.", "A* = A (transposée conjuguée)"],
  "mx-unitary-matrix": ["Matrice unitaire", "Niveau MP*.", null],
  "mx-nilpotent-matrix": ["Matrice nilpotente", null, "Aᵐ = 0 pour un certain m"],
  "mx-invertible-matrix": ["Matrice inversible", "∃A⁻¹. Équivalent à det A≠0, équivalent à rg A=n.", "det A ≠ 0 ⟺ rg A = n"],
  "mx-determinant": ["Déterminant", "det : Mₙ(K)→K, l'unique forme n-linéaire alternée des colonnes normalisée par det(Iₙ)=1. det(AB)=det(A)det(B).", "forme n-linéaire alternée, det(Iₙ)=1"],
  "mx-linear-system": ["Système linéaire AX=B", "Résolu par la méthode du pivot de Gauss / forme échelonnée.", null],
  "mx-homogeneous-system": ["Système homogène AX=0", "Ensemble des solutions = ker(A), un sous-espace vectoriel. Pour AX=B, l'ensemble des solutions (s'il est non vide) est un sous-espace affine X₀+ker(A).", "ensemble des solutions = ker(A)"],

  // ---- Probability ----
  "pr-random-variable": ["Variable aléatoire", "Une application X : Ω→ℝ (mesurable, bien que dans le cadre discret de CPGE ce soit surtout implicite).", null],
  "pr-discrete-rv": ["Variable aléatoire discrète", null, "+ image dénombrable"],
  "pr-finite-rv": ["Variable aléatoire finie", null, "+ image finie"],
  "pr-bernoulli": ["Variable de Bernoulli", null, "valeurs dans {0,1}"],
  "pr-binomial": ["Variable binomiale", "Somme de n épreuves de Bernoulli indépendantes.", "somme de n Bernoulli indépendantes"],
  "pr-geometric": ["Variable géométrique", "Rang du premier succès dans des épreuves de Bernoulli indépendantes — support infini dénombrable.", "rang du premier succès"],
  "pr-poisson": ["Variable de Poisson", null, "valeurs dans ℕ, paramètre λ"],
  "pr-random-vector": ["Vecteur aléatoire (X₁,...,Xₙ)", null, "n-uplet de variables aléatoires"],
  "pr-independence": ["Événements / variables indépendants", "P(A∩B)=P(A)P(B). L'indépendance mutuelle est strictement plus forte que l'indépendance deux à deux. Pour X,Y indépendantes intégrables : E(XY)=E(X)E(Y), donc indépendance ⟹ covariance nulle (pas réciproquement).", null],
  "pr-complete-system": ["Système complet d'événements", "Une partition de Ω en événements — base de la formule des probabilités totales et de la formule de Bayes.", "partition de Ω en événements"],

  // ---- Patterns ----
  "mo-subobject": ["Sous-objet", "Une partie d'une structure qui est elle-même stable par les opérations de la structure — le schéma général derrière les sous-groupes, sous-anneaux et sous-espaces.", "partie stable par les opérations de la structure"],
  "mo-subgroup": ["Sous-groupe", null, "partie stable par •, ⁻¹, contenant e"],
  "mo-subring": ["Sous-anneau", null, "partie stable par +, ×, contenant 0 et 1"],
  "mo-subfield": ["Sous-corps", null, "sous-anneau qui est lui-même un corps"],
  "mo-ideal": ["Idéal", "Un sous-groupe additif absorbant la multiplication : x∈A, i∈I ⟹ xi∈I. En général pas un sous-anneau (ne contient pas forcément 1). Le noyau d'un morphisme d'anneaux est toujours un idéal.", "sous-groupe additif absorbant : xI ⊆ I"],
  "mo-principal-ideal": ["Idéal principal", "Engendré par un seul élément : (a) = aA. Tout idéal de ℤ est de cette forme : nℤ.", "engendré par un élément : (a)"],
  "mo-vector-subspace": ["Sous-espace vectoriel", null, "partie stable par + et par multiplication scalaire"],
  "mo-subalgebra": ["Sous-algèbre", "À la fois sous-espace vectoriel et sous-anneau — rarement nommée explicitement en CPGE.", "sous-espace qui est aussi un sous-anneau"],
  "mo-invariant-subspace": ["Sous-espace stable", "F tel que u(F)⊆F pour un endomorphisme u — central dans le chapitre de réduction.", "u(F) ⊆ F pour un endomorphisme u"],
  "mo-affine-subspace": ["Sous-espace affine", "A + F : un point plus un sous-espace vectoriel. Un sous-espace vectoriel est le cas particulier passant par l'origine.", "A + F (point + sous-espace vectoriel)"],
  "mo-topological-subspace": ["Sous-espace topologique", "Une partie munie de la topologie induite (topologie de sous-espace).", "topologie induite"],
  "mo-quotient": ["Quotient", "Un objet construit en identifiant les éléments équivalents d'une structure plus grande — la même idée que ℤ/nℤ, généralisée à toute structure.", "identifier les éléments équivalents"],
  "mo-quotient-group": ["Groupe quotient G/H", "Défini quand H est un sous-groupe distingué. La construction générale (non abélienne) dépasse le cadre de la CPGE, bien que le cas abélien ℤ/nℤ soit utilisé constamment.", "G/H, H distingué"],
  "mo-quotient-ring": ["Anneau quotient A/I", "A/I où I est un idéal. ℤ/nℤ est l'exemple concret de prépa.", "A/I, I un idéal"],
  "mo-quotient-vector-space": ["Espace vectoriel quotient E/F", "Généralement secondaire dans le programme.", "E/F, F un sous-espace"],
  "mo-morphism": ["Application préservant la structure (morphisme)", "Une application entre deux ensembles structurés qui respecte la structure — un morphisme de groupes respecte •, une application linéaire respecte + et la multiplication scalaire, une application continue respecte les limites.", "f(x ⋆ y) = f(x) ⋆ f(y), selon la structure"],
  "mo-group-hom": ["Morphisme de groupes", null, null],
  "mo-ring-hom": ["Morphisme d'anneaux", "Est en particulier un morphisme de groupes pour +.", "préserve +, ×, 1"],
  "mo-linear-map": ["Application linéaire", null, null],
  "mo-affine-map": ["Application affine", null, "f(x) = u(x) + b, u linéaire"],
  "mo-continuous-map": ["Application continue", null, "préserve les limites"],
  "mo-isometry": ["Isométrie", null, "‖u(x)‖ = ‖x‖ (conserve les distances)"],
  "mo-order-preserving-map": ["Application croissante (monotone)", "Les fonctions monotones sont étudiées abondamment en CPGE, mais généralement pas présentées comme des « morphismes d'ensembles ordonnés ».", null],
  "mo-measurable-map": ["Application mesurable", "Les images réciproques de parties mesurables sont mesurables — fondement formel d'une variable aléatoire, au-delà de ce qui est développé explicitement en CPGE.", "f⁻¹(mesurable) est mesurable"],
  "mo-endomorphism": ["Endomorphisme", null, "départ = arrivée"],
  "mo-isomorphism": ["Isomorphisme", "Une application bijective préservant la structure dont la réciproque préserve aussi la structure.", "bijective, préserve la structure dans les deux sens"],
  "mo-automorphism": ["Automorphisme", "Un endomorphisme qui est aussi un isomorphisme — inversible, préservant la structure, départ = arrivée.", "endomorphisme + isomorphisme"],
};

// Domain + branch labels, FR
const FR_DOMAINS = {
  algebra: { label: "Structures algébriques", up: "EST UN(E) / SE GÉNÉRALISE EN", down: "SPÉCIALISATIONS" },
  analysis: { label: "Analyse : fonctions, suites et séries", up: "IMPLIQUE", down: "IMPLIQUÉ PAR (formes plus fortes)" },
  numbers: { label: "Nombres, arithmétique et dénombrement", up: "SE PLONGE DANS / CONSTRUIT À PARTIR DE", down: "CONTIENT / CONSTRUIT" },
  matrices: { label: "Polynômes, matrices et applications linéaires", up: "EST UN(E)", down: "SPÉCIALISATIONS" },
  probability: { label: "Probabilités", up: "EST UN(E)", down: "SPÉCIALISATIONS" },
  morphisms: { label: "Schémas : sous-objets, quotients, morphismes", up: "EST UN(E)", down: "SPÉCIALISATIONS" },
};
const FR_BRANCHES = {
  algebra: { root: "Fondations", order: "Ordres et relations", group: "Structures de groupe", ring: "Structures d'anneau", module: "Modules / espaces vectoriels", forms: "Formes bilinéaires / quadratiques", geometry: "Géométrie affine", topology: "Topologie et analyse", probability: "Probabilités (espaces)", category: "Théorie des catégories" },
  analysis: { func: "Fonctions et régularité", seq: "Suites", series: "Séries", funcseq: "Suites/séries de fonctions", ode: "Équations différentielles", multivar: "Plusieurs variables", curves: "Courbes paramétrées" },
  numbers: { systems: "Ensembles de nombres (ℕ⊂ℤ⊂ℚ⊂ℝ⊂ℂ)", arithmetic: "Arithmétique dans ℤ", combinatorics: "Dénombrement" },
  matrices: { poly: "Polynômes et fractions rationnelles", linmap: "Applications linéaires et réduction", matrix: "Taxonomie des matrices", linsys: "Déterminant et systèmes linéaires" },
  probability: { rv: "Variables aléatoires", concepts: "Indépendance et partitions" },
  morphisms: { sub: "Sous-objets", quot: "Quotients", morph: "Morphismes" },
};

// Interface strings
const UI = {
  en: {
    title: "A Map of Mathematical Structures & Concepts",
    subtitle: (n, m, k) => `${n} nodes across ${m} trees · ${k} theorems`,
    highlight: "Highlight programme coverage",
    highlightOn: "✓ Programme items only",
    search: "Search this tree…",
    alsoSee: "ALSO SEE",
    notInProgramme: "Shown for broader context.",
    ancestors: (n) => `${n} ancestor${n !== 1 ? "s" : ""}`,
    descendants: (n) => `${n} descendant${n !== 1 ? "s" : ""}`,
    language: "Language",
    zoomIn: "Zoom in (+)",
    zoomOut: "Zoom out (−)",
    zoomReset: "Reset to 100% (0)",
    zoomFit: "Fit the whole tree in the window",
    zoomHint: "Ctrl/⌘ + scroll",
    highlightShort: "Programme",
    highlightShortOn: "✓ Programme",
    backToTree: "← Back to the tree",
    openInfo: "Show details",
    axioms: "Complete axioms",
    axiomsNone: "None — a set carries no structure.",
    thmTab: "Theorems",
    searchThm: "Search theorems…",
    thmAllTopics: "All topics",
    thmCount: (n) => `${n} theorem${n !== 1 ? "s" : ""}`,
    thmNone: "No theorem matches.",
    thmIdea: "Idea of the proof",
    thmHolds: "Holds on",
    thmProves: "Proves that",
    thmIs: "is a(n)",
    thmUses: "Relies on",
    thmUsedBy: "Used by",
    theorems: "Theorems",
    thmOnThis: "Hold on this structure",
    thmInherited: "Hold through a more general structure",
    thmProvesThis: "Prove that something is this structure",
    thmVia: "via",
    openInTree: "Open in the tree",
    backToList: "← Back to the list",
  },
  fr: {
    title: "Carte des structures et concepts mathématiques",
    subtitle: (n, m, k) => `${n} nœuds répartis en ${m} arbres · ${k} théorèmes · point bleu = MPSI, point rose = MP/MP*`,
    highlight: "Surligner MPSI/MP",
    highlightOn: "✓ MPSI/MP seulement",
    search: "Rechercher dans cet arbre…",
    alsoSee: "VOIR AUSSI",
    notInProgramme: "Hors programme de CPGE — affiché pour le contexte.",
    mpsi: "MPSI (1ʳᵉ année)",
    mp: "MP / MP* (2ᵉ année)",
    ancestors: (n) => `${n} ancêtre${n !== 1 ? "s" : ""}`,
    descendants: (n) => `${n} descendant${n !== 1 ? "s" : ""}`,
    language: "Langue",
    zoomIn: "Zoom avant (+)",
    zoomOut: "Zoom arrière (−)",
    zoomReset: "Revenir à 100 % (0)",
    zoomFit: "Ajuster l'arbre à la fenêtre",
    zoomHint: "Ctrl/⌘ + molette",
    highlightShort: "MPSI/MP",
    highlightShortOn: "✓ MPSI/MP",
    backToTree: "← Retour à l'arbre",
    openInfo: "Afficher les détails",
    axioms: "Axiomes complets",
    axiomsNone: "Aucun — un ensemble n'a pas de structure.",
    thmTab: "Théorèmes",
    searchThm: "Rechercher un théorème…",
    thmAllTopics: "Tous les thèmes",
    thmCount: (n) => `${n} théorème${n > 1 ? "s" : ""}`,
    thmNone: "Aucun théorème ne correspond.",
    thmIdea: "Idée de la preuve",
    thmHolds: "S'applique à",
    thmProves: "Démontre que",
    thmIs: "est un(e)",
    thmUses: "S'appuie sur",
    thmUsedBy: "Utilisé par",
    theorems: "Théorèmes",
    thmOnThis: "Valables sur cette structure",
    thmInherited: "Valables via une structure plus générale",
    thmProvesThis: "Démontrent que quelque chose est cette structure",
    thmVia: "via",
    openInTree: "Ouvrir dans l'arbre",
    backToList: "← Retour à la liste",
  },
};

// zoom limits + the padding of the scroll pane (needed to keep the cursor point fixed)
const ZOOM_MIN = 0.2;
const ZOOM_MAX = 2.5;
const PAD_L = 10, PAD_R = 10, PAD_T = 20, PAD_B = 60;
const clampZoom = (z) => Math.min(ZOOM_MAX, Math.max(ZOOM_MIN, z));

// "Mobile layout" = narrow window (phones, tablets in portrait) or a phone held in landscape.
const MOBILE_QUERY = "(max-width: 860px), (max-height: 520px) and (pointer: coarse)";
function useIsMobile() {
  const read = () => typeof window !== "undefined" && typeof window.matchMedia === "function" && window.matchMedia(MOBILE_QUERY).matches;
  const [mobile, setMobile] = useState(read);
  useEffect(() => {
    if (typeof window.matchMedia !== "function") return;
    const mq = window.matchMedia(MOBILE_QUERY);
    const on = () => setMobile(mq.matches);
    on();
    if (mq.addEventListener) mq.addEventListener("change", on);
    else mq.addListener(on);
    return () => {
      if (mq.removeEventListener) mq.removeEventListener("change", on);
      else mq.removeListener(on);
    };
  }, []);
  return mobile;
}

// Split a node label over at most two lines for the 168px node box.
function wrapName(name, max = 24) {
  if (name.length <= max) return [name];
  const mid = name.length / 2;
  let best = -1;
  for (let i = 0; i < name.length; i++) {
    if (name[i] === " " && (best === -1 || Math.abs(i - mid) < Math.abs(best - mid))) best = i;
  }
  const clip = (s) => (s.length > 27 ? s.slice(0, 26) + "…" : s);
  if (best === -1) return [clip(name)];
  return [clip(name.slice(0, best)), clip(name.slice(best + 1))];
}

// =============================================================================
// Complete axioms. Hand-written from the standard definitions (NOT the stacked
// "added" lines of the ancestors: Ring's additive axioms come from Abelian Group
// but are written for + instead of •, Semiring's "no inverses" must not leak, …).
// Each axiom: label EN, label FR, formula. A formula is language-neutral
// (logic symbols) unless it needs words, in which case it is { en, fr }.
// Only nodes of the algebraic-structures tree have a list.
// =============================================================================
const X = (en, fr, f) => ({ en, fr, f });
const AX = {
  // ---- relations & orders ----
  rel_def: X("Relation as a subset", "Relation comme partie", "R ⊆ E × E,   xRy ⟺ (x,y) ∈ R"),
  r_refl: X("Reflexivity", "Réflexivité", "∀x, xRx"),
  r_sym: X("Symmetry", "Symétrie", "xRy ⟹ yRx"),
  r_trans: X("Transitivity", "Transitivité", "xRy ∧ yRz ⟹ xRz"),
  quot_def: X("Equivalence classes", "Classes d'équivalence", "[x] = {y : y ∼ x},   E/∼ = {[x] : x ∈ E}"),
  o_refl: X("Reflexivity", "Réflexivité", "∀x, x ≤ x"),
  o_antisym: X("Antisymmetry", "Antisymétrie", "x ≤ y ∧ y ≤ x ⟹ x = y"),
  o_trans: X("Transitivity", "Transitivité", "x ≤ y ∧ y ≤ z ⟹ x ≤ z"),
  o_total: X("Totality", "Totalité", "∀x,y, x ≤ y ∨ y ≤ x"),
  well: X("Well-ordering", "Bon ordre", "∀A ≠ ∅, ∃m ∈ A, ∀a ∈ A, m ≤ a"),
  lat_join: X("Joins", "Borne supérieure d'une paire", "∀x,y, ∃ x ∨ y = sup{x,y}"),
  lat_meet: X("Meets", "Borne inférieure d'une paire", "∀x,y, ∃ x ∧ y = inf{x,y}"),
  lat_dist: X("Distributivity", "Distributivité", "x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)"),
  lat_bounds: X("Bounds", "Bornes 0 et 1", "∃ 0, 1, ∀x, 0 ≤ x ≤ 1"),
  lat_compl: X("Complements", "Complémentaires", "∀x, ∃x′, x ∨ x′ = 1 ∧ x ∧ x′ = 0"),
  lat_complete: X("Completeness", "Complétude", "∀A ⊆ E, ∃ sup A et inf A"),

  // ---- group-like (law •, neutral e) ----
  closed: X("Internal law", "Loi interne", "∀a,b ∈ G, a • b ∈ G"),
  assoc: X("Associativity", "Associativité", "(a • b) • c = a • (b • c)"),
  identity: X("Neutral element", "Élément neutre", "∃e ∈ G, ∀a, e • a = a • e = a"),
  inverse: X("Inverses", "Symétriques (inverses)", "∀a, ∃a⁻¹, a • a⁻¹ = a⁻¹ • a = e"),
  comm: X("Commutativity", "Commutativité", "a • b = b • a"),
  cyclic: X("Generated by one element", "Monogène", "∃g ∈ G, G = ⟨g⟩ = {gⁿ : n ∈ ℤ}"),
  sym_def: X("Definition", "Définition", "Sₙ = {σ : {1,…,n} → {1,…,n} bijective},   law = ∘"),
  alt_def: X("Definition", "Définition", "Aₙ = {σ ∈ Sₙ : ε(σ) = +1}"),
  gl_def: X("Definition", "Définition", "GL(E) = {u ∈ L(E) : u bijective},   law = ∘"),
  orth_def: X("Definition", "Définition", "O(E) = {u ∈ GL(E) : ∀x,y, ⟨u(x), u(y)⟩ = ⟨x, y⟩}"),
  so_def: X("Rotations", "Rotations", "SO(E) = {u ∈ O(E) : det u = 1}"),
  unit_def: X("Definition", "Définition", "U(E) = {u ∈ GL(E) : ∀x,y, ⟨u(x), u(y)⟩ = ⟨x, y⟩}   (Hermitian)"),
  free_def: X("Freeness", "Liberté", { en: "generated by a set S, with no relation other than the group axioms", fr: "engendré par un ensemble S, sans autre relation que les axiomes de groupe" }),
  cont_mul: X("Continuous law", "Loi continue", "(a, b) ↦ a • b is continuous"),
  cont_inv: X("Continuous inverse", "Passage à l'inverse continu", "a ↦ a⁻¹ is continuous"),
  smooth_mul: X("Smooth law", "Loi lisse", "(a, b) ↦ a • b is C∞"),
  smooth_inv: X("Smooth inverse", "Passage à l'inverse lisse", "a ↦ a⁻¹ is C∞"),

  // ---- ring-like (laws + and ×) ----
  a_closed: X("+ is an internal law", "+ est une loi interne", "∀a,b ∈ A, a + b ∈ A"),
  a_assoc: X("Associativity of +", "Associativité de +", "(a + b) + c = a + (b + c)"),
  a_zero: X("Additive identity", "Neutre de +", "∃0 ∈ A, ∀a, a + 0 = 0 + a = a"),
  a_neg: X("Additive inverses", "Opposés", "∀a, ∃(−a), a + (−a) = 0"),
  a_comm: X("Commutativity of +", "Commutativité de +", "a + b = b + a"),
  m_closed: X("× is an internal law", "× est une loi interne", "∀a,b ∈ A, a × b ∈ A"),
  m_assoc: X("Associativity of ×", "Associativité de ×", "(a × b) × c = a × (b × c)"),
  m_one: X("Multiplicative identity", "Neutre de ×", "∃1 ∈ A, ∀a, 1 × a = a × 1 = a"),
  dist_l: X("Left distributivity", "Distributivité à gauche", "a × (b + c) = a × b + a × c"),
  dist_r: X("Right distributivity", "Distributivité à droite", "(a + b) × c = a × c + b × c"),
  m_comm: X("Commutativity of ×", "Commutativité de ×", "a × b = b × a"),
  zero_abs: X("0 is absorbing", "0 est absorbant", "0 × a = a × 0 = 0"),
  nonzero: X("Nontrivial", "Non trivial", "1 ≠ 0"),
  no_zd: X("No zero divisors", "Intégrité", "a × b = 0 ⟹ a = 0 ∨ b = 0"),
  m_inv: X("Invertibility of nonzero elements", "Inversibilité des éléments non nuls", "∀a ≠ 0, ∃a⁻¹, a × a⁻¹ = a⁻¹ × a = 1"),
  gcd_ex: X("Existence of gcd", "Existence du pgcd", "∀a, b, ∃ gcd(a, b)"),
  fact_ex: X("Existence of factorization", "Existence de la factorisation", { en: "every nonzero non-unit is a product of irreducibles", fr: "tout élément non nul non inversible est un produit d'irréductibles" }),
  fact_uniq: X("Uniqueness of factorization", "Unicité de la factorisation", { en: "unique up to order and multiplication by units", fr: "unique à l'ordre et aux inversibles près" }),
  principal: X("Principal ideals", "Idéaux principaux", "every ideal I = (a) = aA"),
  euclid: X("Euclidean division", "Division euclidienne", "∃ν : A∖{0} → ℕ, ∀a, b ≠ 0, ∃q, r : a = bq + r ∧ (r = 0 ∨ ν(r) < ν(b))"),
  finite: X("Finite", "Fini", "|F| < ∞   (then |F| = pⁿ)"),
  alg_closed: X("Algebraically closed", "Algébriquement clos", "∀P ∈ F[X], deg P ≥ 1 ⟹ ∃a ∈ F, P(a) = 0"),
  o_add: X("Order compatible with +", "Ordre compatible avec +", "a ≤ b ⟹ a + c ≤ b + c"),
  o_mul: X("Order compatible with ×", "Ordre compatible avec ×", "0 ≤ a ∧ 0 ≤ b ⟹ 0 ≤ a × b"),
  sqrt_pos: X("Square roots", "Racines carrées", "∀a ≥ 0, ∃b, b² = a"),
  odd_root: X("Odd-degree polynomials", "Polynômes de degré impair", "deg P odd ⟹ ∃a, P(a) = 0"),
  local: X("Unique maximal ideal", "Unique idéal maximal", "∃! maximal ideal 𝔪 ⊂ A"),
  acc: X("Ascending chain condition", "Condition de chaîne ascendante", "I₀ ⊆ I₁ ⊆ I₂ ⊆ … ⟹ ∃N, ∀n ≥ N, Iₙ = I_N"),
  idem: X("Idempotence", "Idempotence", "∀a, a² = a"),
  zmodn_def: X("Construction", "Construction", "ℤ/nℤ = ℤ/∼  where a ∼ b ⟺ n | (a − b)"),
  poly_def: X("Definition", "Définition", "K[X] = {Σ aₖXᵏ : aₖ ∈ K, finitely many ≠ 0},   K a field"),
  polyn_def: X("Definition", "Définition", "Kₙ[X] = {P ∈ K[X] : deg P ≤ n},   dim = n + 1"),
  ratfrac_def: X("Definition", "Définition", "K(X) = {P/Q : P, Q ∈ K[X], Q ≠ 0},   P/Q = P′/Q′ ⟺ PQ′ = P′Q"),
  matrix_def: X("Definition", "Définition", "Mₙ(K) = n × n matrices over K,   × = matrix product"),
  end_def: X("Definition", "Définition", "L(E) = {u : E → E linear},   × = composition ∘"),

  // ---- modules, vector spaces, algebras ----
  e_closed: X("+ is an internal law", "+ est une loi interne", "x + y ∈ E"),
  e_assoc: X("Associativity of +", "Associativité de +", "(x + y) + z = x + (y + z)"),
  e_zero: X("Zero vector", "Vecteur nul", "∃0_E, x + 0_E = x"),
  e_neg: X("Opposites", "Opposés", "∀x, ∃(−x), x + (−x) = 0_E"),
  e_comm: X("Commutativity of +", "Commutativité de +", "x + y = y + x"),
  m_ring: X("Scalars", "Scalaires", "R is a ring with 1"),
  v_field: X("Scalars", "Scalaires", "K is a field"),
  v_real: X("Scalars", "Scalaires", "K = ℝ"),
  v_complex: X("Scalars", "Scalaires", "K = ℂ"),
  sm_dist_v: X("Distributivity over vectors", "Distributivité sur les vecteurs", "λ(x + y) = λx + λy"),
  sm_dist_s: X("Distributivity over scalars", "Distributivité sur les scalaires", "(λ + μ)x = λx + μx"),
  sm_assoc: X("Compatibility of products", "Compatibilité des produits", "(λμ)x = λ(μx)"),
  sm_unit: X("Unit acts trivially", "Le scalaire 1 agit trivialement", "1 · x = x"),
  alg_compat: X("Bilinear product", "Produit bilinéaire", "(λx)y = λ(xy) = x(λy)"),
  lie_bil: X("Bilinear bracket", "Crochet bilinéaire", "[·,·] : E × E → E bilinear"),
  lie_alt: X("Alternating", "Alterné", "[x, x] = 0"),
  lie_jac: X("Jacobi identity", "Identité de Jacobi", "[x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0"),
  n_field: X("Scalars", "Scalaires", "K = ℝ or ℂ"),
  n_pos: X("Positivity", "Positivité", "‖x‖ ≥ 0"),
  n_sep: X("Separation", "Séparation", "‖x‖ = 0 ⟺ x = 0"),
  n_hom: X("Homogeneity", "Homogénéité", "‖λx‖ = |λ|·‖x‖"),
  n_tri: X("Triangle inequality", "Inégalité triangulaire", "‖x + y‖ ≤ ‖x‖ + ‖y‖"),
  cauchy: X("Completeness", "Complétude", "every Cauchy sequence in E converges in E"),
  ip_norm: X("Induced norm", "Norme induite", "‖x‖ = √B(x,x)"),

  // ---- bilinear / quadratic / Hermitian forms ----
  bil: X("Bilinearity", "Bilinéarité", "B(λx + μy, z) = λB(x,z) + μB(y,z),   B(x, λy + μz) = λB(x,y) + μB(x,z)"),
  sym: X("Symmetry", "Symétrie", "B(x,y) = B(y,x)"),
  quad_def: X("Quadratic form", "Forme quadratique", "Q(x) = B(x,x),   B(x,y) = ½(Q(x+y) − Q(x) − Q(y))   (char K ≠ 2)"),
  sesq: X("Sesquilinearity", "Sesquilinéarité", { en: "linear in x, conjugate-linear in y (convention-dependent)", fr: "linéaire en x, semi-linéaire en y (selon la convention)" }),
  herm: X("Hermitian symmetry", "Symétrie hermitienne", "B(x,y) = conj(B(y,x))"),
  pos: X("Positivity", "Positivité", "∀x, B(x,x) ≥ 0"),
  def: X("Definiteness", "Caractère défini", "B(x,x) = 0 ⟹ x = 0"),
  fdim: X("Finite dimension", "Dimension finie", "dim E < ∞"),

  // ---- affine geometry ----
  aff_data: X("Data", "Données", "set E of points, vector space E⃗, action (A, u) ↦ A + u"),
  aff_vs: X("Direction", "Direction", { en: "E⃗ is a K-vector space (axioms of a vector space)", fr: "E⃗ est un K-espace vectoriel (axiomes d'espace vectoriel)" }),
  aff_zero: X("Zero translation", "Translation nulle", "A + 0 = A"),
  aff_assoc: X("Composition of translations", "Composition des translations", "(A + u) + v = A + (u + v)"),
  aff_trans: X("Simply transitive", "Action simplement transitive", "∀A, B, ∃! u ∈ E⃗, B = A + u"),
  aff_eucl: X("Euclidean direction", "Direction euclidienne", { en: "E⃗ is a Euclidean space", fr: "E⃗ est un espace euclidien" }),

  // ---- topology & analysis ----
  t_empty: X("∅ and E are open", "∅ et E sont ouverts", "∅ ∈ τ ∧ E ∈ τ"),
  t_union: X("Unions", "Réunions", "(Uᵢ)ᵢ ⊆ τ ⟹ ⋃ᵢ Uᵢ ∈ τ"),
  t_inter: X("Finite intersections", "Intersections finies", "U, V ∈ τ ⟹ U ∩ V ∈ τ"),
  d_pos: X("Positivity", "Positivité", "d(x,y) ≥ 0"),
  d_sep: X("Separation", "Séparation", "d(x,y) = 0 ⟺ x = y"),
  d_sym: X("Symmetry", "Symétrie", "d(x,y) = d(y,x)"),
  d_tri: X("Triangle inequality", "Inégalité triangulaire", "d(x,z) ≤ d(x,y) + d(y,z)"),
  cauchy_m: X("Completeness", "Complétude", "every Cauchy sequence converges"),
  t2: X("Hausdorff (T2)", "Séparé (T2)", "x ≠ y ⟹ ∃ open U ∋ x, V ∋ y, U ∩ V = ∅"),
  compact: X("Compactness", "Compacité", "E = ⋃ᵢ Uᵢ (Uᵢ open) ⟹ ∃ finite J, E = ⋃_{i ∈ J} Uᵢ"),
  connected: X("Connectedness", "Connexité", "E = U ⊔ V, U, V open ⟹ U = ∅ ∨ V = ∅"),
  pathconn: X("Path-connectedness", "Connexité par arcs", "∀x, y, ∃γ : [0,1] → E continuous, γ(0) = x, γ(1) = y"),
  loc_rn: X("Locally Euclidean", "Localement euclidien", "∀x, ∃ open U ∋ x, U homeomorphic to an open subset of ℝⁿ"),
  second_ctbl: X("Second countable (usual convention)", "À base dénombrable (convention usuelle)", "∃ a countable basis of open sets"),
  smooth_atlas: X("Smooth atlas", "Atlas lisse", "transition maps φⱼ ∘ φᵢ⁻¹ are C∞"),
  riem_g: X("Riemannian metric", "Métrique riemannienne", "p ↦ g_p, an inner product on T_pM, smooth in p"),

  // ---- probability ----
  sig_omega: X("Contains Ω", "Contient Ω", "Ω ∈ 𝒜"),
  sig_comp: X("Complements", "Complémentaires", "A ∈ 𝒜 ⟹ Ω∖A ∈ 𝒜"),
  sig_union: X("Countable unions", "Réunions dénombrables", "Aₙ ∈ 𝒜 for all n ⟹ ⋃ₙ Aₙ ∈ 𝒜"),
  p_range: X("Values", "Valeurs", "P : 𝒜 → [0, 1]"),
  p_norm: X("Normalisation", "Normalisation", "P(Ω) = 1"),
  p_sigma: X("σ-additivity", "σ-additivité", "Aₙ pairwise disjoint ⟹ P(⨆ₙ Aₙ) = Σₙ P(Aₙ)"),

  // ---- categories ----
  cat_data: X("Data", "Données", "objects, sets Hom(A,B), composition ∘ : Hom(B,C) × Hom(A,B) → Hom(A,C)"),
  cat_assoc: X("Associativity", "Associativité", "h ∘ (g ∘ f) = (h ∘ g) ∘ f"),
  cat_id: X("Identities", "Identités", "∀A, ∃ id_A,  f ∘ id_A = f = id_B ∘ f"),
  cat_inv: X("Every morphism is invertible", "Tout morphisme est inversible", "∀f : A → B, ∃g : B → A, g ∘ f = id_A ∧ f ∘ g = id_B"),
  mon_tensor: X("Tensor product", "Produit tensoriel", "a bifunctor ⊗ : 𝒞 × 𝒞 → 𝒞"),
  mon_unit: X("Unit object", "Objet unité", "an object I ∈ 𝒞"),
  mon_coh: X("Coherence", "Cohérence", { en: "natural isomorphisms (A⊗B)⊗C ≅ A⊗(B⊗C) and I⊗A ≅ A ≅ A⊗I, satisfying the pentagon and triangle identities", fr: "isomorphismes naturels (A⊗B)⊗C ≅ A⊗(B⊗C) et I⊗A ≅ A ≅ A⊗I, vérifiant les identités du pentagone et du triangle" }),
  ab_hom: X("Hom-groups", "Hom abéliens", { en: "each Hom(A,B) is an abelian group and ∘ is bilinear", fr: "chaque Hom(A,B) est un groupe abélien et ∘ est bilinéaire" }),
  ab_zero: X("Zero object", "Objet nul", { en: "an object that is both initial and terminal", fr: "un objet à la fois initial et final" }),
  ab_biprod: X("Biproducts", "Biproduits", "A ⊕ B exists for all A, B"),
  ab_kc: X("Kernels and cokernels", "Noyaux et conoyaux", { en: "every morphism has a kernel and a cokernel", fr: "tout morphisme a un noyau et un conoyau" }),
  ab_normal: X("Normality", "Normalité", { en: "every monomorphism is a kernel, every epimorphism a cokernel", fr: "tout monomorphisme est un noyau, tout épimorphisme un conoyau" }),
};

// ---- bundles: each list literally contains the one it extends ----
const B = {};
B.magma = ["closed"];
B.semigroup = [...B.magma, "assoc"];
B.monoid = [...B.semigroup, "identity"];
B.group = [...B.monoid, "inverse"];
B.abelian = [...B.group, "comm"];

B.addgroup = ["a_closed", "a_assoc", "a_zero", "a_neg", "a_comm"];
B.semiring = ["a_closed", "a_assoc", "a_zero", "a_comm", "m_closed", "m_assoc", "m_one", "dist_l", "dist_r", "zero_abs"];
B.rng = [...B.addgroup, "m_closed", "m_assoc", "dist_l", "dist_r"];
B.ring = [...B.addgroup, "m_closed", "m_assoc", "m_one", "dist_l", "dist_r"];
B.commring = [...B.ring, "m_comm"];
B.domain = [...B.commring, "nonzero", "no_zd"];
B.field = [...B.commring, "nonzero", "m_inv"];
B.order = ["o_refl", "o_antisym", "o_trans", "o_total"];
B.orderedfield = [...B.field, ...B.order, "o_add", "o_mul"];

B.vecgroup = ["e_closed", "e_assoc", "e_zero", "e_neg", "e_comm"];
B.scalaract = ["sm_dist_v", "sm_dist_s", "sm_assoc", "sm_unit"];
B.module = [...B.vecgroup, "m_ring", ...B.scalaract];
B.vs = [...B.vecgroup, "v_field", ...B.scalaract];
B.vsR = [...B.vecgroup, "v_real", ...B.scalaract];
B.vsC = [...B.vecgroup, "v_complex", ...B.scalaract];
B.kalg = [...B.ring, "v_field", ...B.scalaract, "alg_compat"]; // French convention: unital associative K-algebra
B.kalgExtra = ["v_field", ...B.scalaract, "alg_compat"];
B.normed = [...B.vecgroup, "n_field", ...B.scalaract, "n_pos", "n_sep", "n_hom", "n_tri"];
B.realip = [...B.vsR, "bil", "sym", "pos", "def"];
B.complexip = [...B.vsC, "sesq", "herm", "pos", "def"];

B.topspace = ["t_empty", "t_union", "t_inter"];
B.manifold = [...B.topspace, "t2", "loc_rn", "second_ctbl"];
B.smooth = [...B.manifold, "smooth_atlas"];
B.metric = ["d_pos", "d_sep", "d_sym", "d_tri"];
B.category = ["cat_data", "cat_assoc", "cat_id"];

const AXIOMS = {
  set: [],
  "binary-relation": ["rel_def"],
  preorder: ["r_refl", "r_trans"],
  "equivalence-relation": ["r_refl", "r_sym", "r_trans"],
  "quotient-set": ["r_refl", "r_sym", "r_trans", "quot_def"],
  poset: ["o_refl", "o_antisym", "o_trans"],
  "total-order": B.order,
  "well-order": [...B.order, "well"],
  lattice: ["o_refl", "o_antisym", "o_trans", "lat_join", "lat_meet"],
  "distributive-lattice": ["o_refl", "o_antisym", "o_trans", "lat_join", "lat_meet", "lat_dist"],
  "boolean-algebra": ["o_refl", "o_antisym", "o_trans", "lat_join", "lat_meet", "lat_dist", "lat_bounds", "lat_compl"],
  "complete-lattice": ["o_refl", "o_antisym", "o_trans", "lat_complete"],

  magma: B.magma,
  semigroup: B.semigroup,
  monoid: B.monoid,
  group: B.group,
  "abelian-group": B.abelian,
  "cyclic-group": [...B.abelian, "cyclic"],
  "symmetric-group": [...B.group, "sym_def"],
  "alternating-group": [...B.group, "alt_def"],
  "general-linear-group": [...B.group, "gl_def"],
  "orthogonal-group": [...B.group, "orth_def"],
  "special-orthogonal-group": [...B.group, "orth_def", "so_def"],
  "unitary-group": [...B.group, "unit_def"],
  "free-group": [...B.group, "free_def"],
  "lie-group": [...B.group, ...B.smooth, "smooth_mul", "smooth_inv"],
  "topological-group": [...B.group, ...B.topspace, "cont_mul", "cont_inv"],

  semiring: B.semiring,
  ring: B.ring,
  rng: B.rng,
  "comm-ring": B.commring,
  domain: B.domain,
  "gcd-domain": [...B.domain, "gcd_ex"],
  ufd: [...B.domain, "fact_ex", "fact_uniq"],
  pid: [...B.domain, "principal"],
  "euclidean-domain": [...B.domain, "euclid"],
  field: B.field,
  "finite-field": [...B.field, "finite"],
  "algebraically-closed-field": [...B.field, "alg_closed"],
  "ordered-field": B.orderedfield,
  "real-closed-field": [...B.orderedfield, "sqrt_pos", "odd_root"],
  "division-ring": [...B.ring, "nonzero", "m_inv"],
  "ordered-ring": [...B.commring, ...B.order, "o_add", "o_mul"],
  "local-ring": [...B.commring, "local"],
  "noetherian-ring": [...B.commring, "acc"],
  "boolean-ring": [...B.commring, "idem"],
  "z-mod-n": [...B.commring, "zmodn_def"],
  "poly-ring": ["poly_def", ...B.domain, "euclid", ...B.kalgExtra],
  "poly-ring-degree-n": ["polyn_def", ...B.vs],
  "rational-fraction-field": ["ratfrac_def", ...B.field],
  "matrix-ring": ["matrix_def", ...B.kalg],
  "endomorphism-algebra": ["end_def", ...B.kalg],

  module: B.module,
  "vector-space": B.vs,
  "algebra-over-field": B.kalg,
  "associative-algebra": B.kalg,
  "lie-algebra": [...B.vs, "lie_bil", "lie_alt", "lie_jac"],
  "normed-space": B.normed,
  "banach-space": [...B.normed, "cauchy"],
  "hilbert-space": [...B.realip, "ip_norm", "cauchy"],

  "bilinear-space": [...B.vs, "bil"],
  "symmetric-bilinear-space": [...B.vs, "bil", "sym"],
  "quadratic-space": [...B.vs, "bil", "sym", "quad_def"],
  "sesquilinear-space": [...B.vsC, "sesq"],
  "hermitian-form-space": [...B.vsC, "sesq", "herm"],
  "inner-product-space": B.realip,
  "complex-inner-product-space": B.complexip,
  "euclidean-space": [...B.realip, "fdim"],
  "hermitian-space": [...B.complexip, "fdim"],

  "affine-space": ["aff_data", "aff_vs", "aff_zero", "aff_assoc", "aff_trans"],
  "euclidean-affine-space": ["aff_data", "aff_vs", "aff_zero", "aff_assoc", "aff_trans", "aff_eucl"],

  "topological-space": B.topspace,
  "metric-space": B.metric,
  "complete-metric-space": [...B.metric, "cauchy_m"],
  "hausdorff-space": [...B.topspace, "t2"],
  "compact-space": [...B.topspace, "compact"],
  "connected-space": [...B.topspace, "connected"],
  "path-connected-space": [...B.topspace, "pathconn"],
  manifold: B.manifold,
  "smooth-manifold": B.smooth,
  "riemannian-manifold": [...B.smooth, "riem_g"],

  "measurable-space": ["sig_omega", "sig_comp", "sig_union"],
  "probability-space": ["sig_omega", "sig_comp", "sig_union", "p_range", "p_norm", "p_sigma"],

  category: B.category,
  groupoid: [...B.category, "cat_inv"],
  "monoidal-category": [...B.category, "mon_tensor", "mon_unit", "mon_coh"],
  "abelian-category": [...B.category, "ab_hom", "ab_zero", "ab_biprod", "ab_kc", "ab_normal"],
};

// =============================================================================
// THEOREM DATABASE. Linked to the trees by node id:
//   on   : structures/objects on which the theorem holds. An entry is an id, or
//          [id, [condition EN, condition FR]].
//   pr   : "this theorem proves that <of> has the structure <id>": [[of EN, of FR], id].
//   uses : other theorems it relies on (a dependency graph).
// n = name, s = statement, i = idea of the proof, each as [EN, FR].
// prepa = where it is taught (MPSI / MP); absent = not an explicit programme item.
// =============================================================================
const FIN = ["finite-dimensional", "de dimension finie"];
const THM_TOPICS = {
  struct: { en: "Groups, rings & fields", fr: "Groupes, anneaux & corps", color: "#b8562f" },
  arith: { en: "Arithmetic & polynomials", fr: "Arithmétique & polynômes", color: "#2f6b8a" },
  linalg: { en: "Linear algebra & reduction", fr: "Algèbre linéaire & réduction", color: "#5c7a3a" },
  euclid: { en: "Euclidean & Hermitian spaces", fr: "Espaces euclidiens & hermitiens", color: "#0f9488" },
  topo: { en: "Topology of normed spaces", fr: "Topologie des espaces normés", color: "#b08a1f" },
  analysis: { en: "Real analysis", fr: "Analyse réelle", color: "#8a4f9e" },
  series: { en: "Series & sequences of functions", fr: "Séries & suites de fonctions", color: "#4a5a9e" },
  diffeq: { en: "Differential equations", fr: "Équations différentielles", color: "#a0642b" },
  proba: { en: "Probability", fr: "Probabilités", color: "#b8305f" },
  comb: { en: "Sets & counting", fr: "Ensembles & dénombrement", color: "#8a8578" },
};
const THM_KINDS = {
  theorem: { en: "Theorem", fr: "Théorème" },
  proposition: { en: "Proposition", fr: "Proposition" },
  inequality: { en: "Inequality", fr: "Inégalité" },
};

const THEOREMS = [
  // ===================== groups, rings, fields =====================
  { id: "subgroup-criterion", topic: "struct", kind: "proposition", prepa: "MPSI",
    n: ["Subgroup criterion", "Caractérisation des sous-groupes"],
    s: ["A subset H of a group G is a subgroup iff H ≠ ∅ and ∀x,y ∈ H, xy⁻¹ ∈ H.", "Une partie H d'un groupe G est un sous-groupe ssi H ≠ ∅ et ∀x,y ∈ H, xy⁻¹ ∈ H."],
    i: ["Take y = x to get e, then x = e to get inverses, then products.", "Prendre y = x pour obtenir e, puis x = e pour obtenir les inverses, puis les produits."],
    on: ["group", "mo-subgroup"],
    pr: [[["a subset H ⊆ G with H ≠ ∅ and xy⁻¹ ∈ H", "une partie H ⊆ G non vide avec xy⁻¹ ∈ H"], "group"]] },
  { id: "morphism-kernel-image", topic: "struct", kind: "proposition", prepa: "MPSI",
    n: ["Kernel and image of a group morphism", "Noyau et image d'un morphisme de groupes"],
    s: ["For a group morphism φ : G → G′, ker φ is a subgroup of G, im φ is a subgroup of G′, and φ is injective ⟺ ker φ = {e}.", "Pour un morphisme de groupes φ : G → G′, ker φ est un sous-groupe de G, im φ un sous-groupe de G′, et φ est injectif ⟺ ker φ = {e}."],
    i: ["φ(x) = φ(y) ⟺ xy⁻¹ ∈ ker φ.", "φ(x) = φ(y) ⟺ xy⁻¹ ∈ ker φ."],
    on: ["group", "mo-group-hom"],
    pr: [[["ker φ", "ker φ"], "group"], [["im φ", "im φ"], "group"]], uses: ["subgroup-criterion"] },
  { id: "roots-of-unity", topic: "struct", kind: "proposition", prepa: "MPSI",
    n: ["The n-th roots of unity", "Les racines n-ièmes de l'unité"],
    s: ["𝕌ₙ = {z ∈ ℂ : zⁿ = 1} = {e^{2ikπ/n} : 0 ≤ k < n} is a cyclic subgroup of (ℂ*, ×) of order n, generated by e^{2iπ/n}.", "𝕌ₙ = {z ∈ ℂ : zⁿ = 1} = {e^{2ikπ/n} : 0 ≤ k < n} est un sous-groupe cyclique de (ℂ*, ×), d'ordre n, engendré par e^{2iπ/n}."],
    i: ["zⁿ = 1 ⟺ |z| = 1 and arg z ∈ (2π/n)ℤ.", "zⁿ = 1 ⟺ |z| = 1 et arg z ∈ (2π/n)ℤ."],
    on: ["cyclic-group", "nu-C"],
    pr: [[["𝕌ₙ", "𝕌ₙ"], "cyclic-group"]] },
  { id: "lagrange", topic: "struct", kind: "theorem",
    n: ["Lagrange's theorem", "Théorème de Lagrange"],
    s: ["In a finite group G, the order of every subgroup divides |G|. In particular the order of each element divides |G|, and g^{|G|} = e.", "Dans un groupe fini G, l'ordre de tout sous-groupe divise |G|. En particulier l'ordre de chaque élément divise |G| et g^{|G|} = e."],
    i: ["The left cosets gH partition G and all have |H| elements.", "Les classes à gauche gH partitionnent G et ont toutes |H| éléments."],
    on: [["group", ["finite", "fini"]], "cyclic-group", "symmetric-group"], uses: ["equiv-partition"] },
  { id: "signature", topic: "struct", kind: "theorem", prepa: "MPSI",
    n: ["Signature of a permutation", "Signature d'une permutation"],
    s: ["There is a unique group morphism ε : (Sₙ, ∘) → ({−1, 1}, ×) sending every transposition to −1. Its kernel Aₙ is the alternating group.", "Il existe un unique morphisme de groupes ε : (Sₙ, ∘) → ({−1, 1}, ×) envoyant toute transposition sur −1. Son noyau Aₙ est le groupe alterné."],
    i: ["Count inversions, or take the determinant of the permutation matrix.", "Compter les inversions, ou prendre le déterminant de la matrice de permutation."],
    on: ["symmetric-group"],
    pr: [[["ker ε", "ker ε"], "alternating-group"]], uses: ["morphism-kernel-image"] },
  { id: "cycle-decomposition", topic: "struct", kind: "theorem", prepa: "MPSI",
    n: ["Decomposition into disjoint cycles", "Décomposition en cycles disjoints"],
    s: ["Every permutation of a finite set is a product of cycles with disjoint supports, unique up to order; hence it is a product of transpositions.", "Toute permutation d'un ensemble fini est un produit de cycles à supports disjoints, unique à l'ordre près ; c'est donc un produit de transpositions."],
    i: ["Follow the orbit of each element.", "Suivre l'orbite de chaque élément."],
    on: ["symmetric-group", "nu-permutation"] },
  { id: "finite-domain-field", topic: "struct", kind: "proposition",
    n: ["A finite integral domain is a field", "Un anneau intègre fini est un corps"],
    s: ["Every finite integral domain is a field.", "Tout anneau intègre fini est un corps."],
    i: ["For a ≠ 0, x ↦ ax is injective, hence bijective, so ax = 1 has a solution.", "Pour a ≠ 0, x ↦ ax est injective donc bijective, d'où une solution de ax = 1."],
    on: ["domain", "finite-field"],
    pr: [[["a finite integral domain", "un anneau intègre fini"], "field"]] },
  { id: "ker-ideal", topic: "struct", kind: "proposition", prepa: "MPSI",
    n: ["Kernel of a ring morphism", "Noyau d'un morphisme d'anneaux"],
    s: ["If φ : A → B is a ring morphism, then ker φ is an ideal of A and im φ is a subring of B.", "Si φ : A → B est un morphisme d'anneaux, ker φ est un idéal de A et im φ un sous-anneau de B."],
    i: ["φ(ax) = φ(a)φ(x) = 0 when x ∈ ker φ.", "φ(ax) = φ(a)φ(x) = 0 si x ∈ ker φ."],
    on: ["ring", "mo-ring-hom"],
    pr: [[["ker φ", "ker φ"], "mo-ideal"], [["im φ", "im φ"], "mo-subring"]] },

  // ===================== arithmetic & polynomials =====================
  { id: "congruence-compat", topic: "arith", kind: "proposition", prepa: "MPSI",
    n: ["Congruences are compatible with + and ×", "Compatibilité des congruences avec + et ×"],
    s: ["If a ≡ a′ and b ≡ b′ (mod n), then a + b ≡ a′ + b′ and ab ≡ a′b′ (mod n). Hence ℤ/nℤ inherits + and ×.", "Si a ≡ a′ et b ≡ b′ (mod n), alors a + b ≡ a′ + b′ et ab ≡ a′b′ (mod n). Ainsi ℤ/nℤ hérite de + et ×."],
    i: ["Write a′ = a + nk, b′ = b + nl and expand.", "Écrire a′ = a + nk, b′ = b + nl et développer."],
    on: ["nu-congruence", "z-mod-n", "quotient-set"],
    pr: [[["ℤ/nℤ", "ℤ/nℤ"], "comm-ring"]] },
  { id: "euclidean-division", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Euclidean division (ℤ and K[X])", "Division euclidienne (ℤ et K[X])"],
    s: ["For a ∈ ℤ and b ∈ ℤ∖{0} there is a unique (q, r) with a = bq + r and 0 ≤ r < |b|. For A, B ∈ K[X] with B ≠ 0 there is a unique (Q, R) with A = BQ + R and deg R < deg B.", "Pour a ∈ ℤ et b ∈ ℤ∖{0} il existe un unique (q, r) tel que a = bq + r et 0 ≤ r < |b|. Pour A, B ∈ K[X], B ≠ 0, il existe un unique (Q, R) tel que A = BQ + R et deg R < deg B."],
    i: ["Existence: least nonnegative remainder / induction on deg A. Uniqueness: size or degree argument.", "Existence : plus petit reste positif / récurrence sur deg A. Unicité : argument de taille ou de degré."],
    on: ["euclidean-domain", "poly-ring", "nu-Z"],
    pr: [[["ℤ", "ℤ"], "euclidean-domain"], [["K[X]", "K[X]"], "euclidean-domain"]] },
  { id: "ideals-principal", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Ideals of ℤ and of K[X] are principal", "Les idéaux de ℤ et de K[X] sont principaux"],
    s: ["Every ideal of ℤ is of the form nℤ (n ≥ 0). Every ideal of K[X] (K a field) is generated by one polynomial, unique if monic.", "Tout idéal de ℤ est de la forme nℤ (n ≥ 0). Tout idéal de K[X] (K corps) est engendré par un polynôme, unique s'il est unitaire."],
    i: ["Take the least positive element (resp. a nonzero polynomial of least degree) and use Euclidean division.", "Prendre le plus petit élément positif (resp. un polynôme non nul de degré minimal) et utiliser la division euclidienne."],
    on: ["pid", "mo-ideal", "mo-principal-ideal"],
    pr: [[["ℤ", "ℤ"], "pid"], [["K[X]", "K[X]"], "pid"]], uses: ["euclidean-division"] },
  { id: "euclid-pid-ufd", topic: "arith", kind: "theorem",
    n: ["Euclidean ⟹ principal ⟹ factorial", "Euclidien ⟹ principal ⟹ factoriel"],
    s: ["Every Euclidean domain is a principal ideal domain, and every principal ideal domain is a unique factorization domain.", "Tout anneau euclidien est principal, et tout anneau principal est factoriel."],
    i: ["The proof for ℤ and K[X] is the one of the two neighbouring theorems, carried over verbatim.", "La preuve pour ℤ et K[X] est celle des deux théorèmes voisins, qui s'étend telle quelle."],
    on: ["euclidean-domain", "pid"],
    pr: [[["a Euclidean domain", "un anneau euclidien"], "pid"], [["a principal ideal domain", "un anneau principal"], "ufd"]], uses: ["ideals-principal"] },
  { id: "poly-domain", topic: "arith", kind: "proposition", prepa: "MPSI",
    n: ["K[X] is an integral domain", "K[X] est intègre"],
    s: ["For nonzero P, Q ∈ K[X], deg(PQ) = deg P + deg Q; hence K[X] has no zero divisors.", "Pour P, Q ∈ K[X] non nuls, deg(PQ) = deg P + deg Q ; donc K[X] n'a pas de diviseurs de zéro."],
    i: ["The leading coefficients multiply to a nonzero number.", "Les coefficients dominants se multiplient en un scalaire non nul."],
    on: ["poly-ring"],
    pr: [[["K[X]", "K[X]"], "domain"]] },
  { id: "poly-factorization", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Factorization into irreducible polynomials", "Décomposition en facteurs irréductibles"],
    s: ["Every nonconstant polynomial of K[X] is a product of irreducible polynomials, unique up to order and nonzero constants (unique if we require monic factors).", "Tout polynôme non constant de K[X] est un produit de polynômes irréductibles, unique à l'ordre et aux constantes non nulles près (unique si l'on impose des facteurs unitaires)."],
    i: ["Induction on the degree, uniqueness through Gauss's lemma in K[X].", "Récurrence sur le degré ; unicité via le lemme de Gauss dans K[X]."],
    on: ["poly-ring", "mx-irreducible-poly"],
    pr: [[["K[X]", "K[X]"], "ufd"]], uses: ["euclid-pid-ufd"] },
  { id: "dalembert", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["d'Alembert–Gauss theorem", "Théorème de d'Alembert–Gauss"],
    s: ["Every nonconstant polynomial of ℂ[X] has a root in ℂ; hence it splits into linear factors. (Admitted in the programme.)", "Tout polynôme non constant de ℂ[X] admet une racine dans ℂ ; il est donc scindé. (Admis au programme.)"],
    i: ["Minimum of |P| on ℂ is attained and must be 0 (d'Alembert's lemma).", "Le minimum de |P| sur ℂ est atteint et vaut 0 (lemme de d'Alembert)."],
    on: ["poly-ring", "nu-C", "mx-irreducible-poly"],
    pr: [[["ℂ", "ℂ"], "algebraically-closed-field"]] },
  { id: "irreducibles-R-C", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Irreducible polynomials over ℂ and ℝ", "Polynômes irréductibles sur ℂ et sur ℝ"],
    s: ["Over ℂ the irreducible polynomials are those of degree 1. Over ℝ they are those of degree 1 and those of degree 2 with negative discriminant.", "Sur ℂ les irréductibles sont les polynômes de degré 1. Sur ℝ ce sont ceux de degré 1 et ceux de degré 2 de discriminant strictement négatif."],
    i: ["Pair each non-real root with its conjugate.", "Associer chaque racine non réelle à sa conjuguée."],
    on: ["mx-irreducible-poly", "poly-ring"], uses: ["dalembert"] },
  { id: "root-divisibility", topic: "arith", kind: "proposition", prepa: "MPSI",
    n: ["Roots and divisibility", "Racines et divisibilité"],
    s: ["a is a root of P ⟺ (X − a) | P. A nonzero polynomial of degree n has at most n roots (over a field).", "a est racine de P ⟺ (X − a) | P. Un polynôme non nul de degré n a au plus n racines (sur un corps)."],
    i: ["Euclidean division by X − a; then induction on the degree.", "Division euclidienne par X − a ; puis récurrence sur le degré."],
    on: ["mx-root", "poly-ring"], uses: ["euclidean-division"] },
  { id: "multiplicity-derivatives", topic: "arith", kind: "proposition", prepa: "MPSI",
    n: ["Multiplicity and derivatives", "Multiplicité et dérivées"],
    s: ["In characteristic 0, a is a root of multiplicity m of P ⟺ P(a) = P′(a) = … = P^{(m−1)}(a) = 0 and P^{(m)}(a) ≠ 0.", "En caractéristique 0, a est racine de multiplicité m de P ⟺ P(a) = P′(a) = … = P^{(m−1)}(a) = 0 et P^{(m)}(a) ≠ 0."],
    i: ["Taylor formula for polynomials at a.", "Formule de Taylor pour les polynômes en a."],
    on: ["mx-multiple-root", "mx-root"], uses: ["root-divisibility"] },
  { id: "interpolation", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Lagrange interpolation", "Interpolation de Lagrange"],
    s: ["For distinct a₀, …, aₙ ∈ K and any b₀, …, bₙ ∈ K there is a unique P ∈ Kₙ[X] with P(aᵢ) = bᵢ. The map P ↦ (P(a₀), …, P(aₙ)) is an isomorphism Kₙ[X] → Kⁿ⁺¹.", "Pour a₀, …, aₙ ∈ K distincts et b₀, …, bₙ ∈ K quelconques, il existe un unique P ∈ Kₙ[X] tel que P(aᵢ) = bᵢ. L'application P ↦ (P(a₀), …, P(aₙ)) est un isomorphisme Kₙ[X] → Kⁿ⁺¹."],
    i: ["The map is linear and injective (a degree-≤ n polynomial with n + 1 roots is 0); equal dimensions finish.", "L'application est linéaire et injective (un polynôme de degré ≤ n à n + 1 racines est nul) ; dimensions égales."],
    on: ["poly-ring-degree-n"],
    pr: [[["P ↦ (P(a₀), …, P(aₙ))", "P ↦ (P(a₀), …, P(aₙ))"], "mo-isomorphism"]], uses: ["root-divisibility", "iso-criterion"] },
  { id: "partial-fractions", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Partial fraction decomposition", "Décomposition en éléments simples"],
    s: ["Every F = P/Q ∈ K(X) is uniquely the sum of a polynomial and of simple elements: over ℂ, terms c/(X − a)ᵏ for the poles a; over ℝ, also terms (αX + β)/(X² + pX + q)ᵏ with p² − 4q < 0.", "Toute fraction F = P/Q ∈ K(X) s'écrit de façon unique comme somme d'un polynôme et d'éléments simples : sur ℂ, des termes c/(X − a)ᵏ pour les pôles a ; sur ℝ, aussi des termes (αX + β)/(X² + pX + q)ᵏ avec p² − 4q < 0."],
    i: ["Factor Q into irreducibles and apply Bézout in K[X] repeatedly.", "Factoriser Q en irréductibles et appliquer Bézout dans K[X]."],
    on: ["rational-fraction-field", "mx-rational-function"], uses: ["poly-factorization", "irreducibles-R-C"] },
  { id: "bezout", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Bézout's theorem", "Théorème de Bézout"],
    s: ["For a, b ∈ ℤ with d = gcd(a, b), there are u, v ∈ ℤ with au + bv = d. In particular a and b are coprime ⟺ ∃u, v, au + bv = 1.", "Pour a, b ∈ ℤ et d = pgcd(a, b), il existe u, v ∈ ℤ tels que au + bv = d. En particulier a et b sont premiers entre eux ⟺ ∃u, v, au + bv = 1."],
    i: ["The ideal aℤ + bℤ is principal; its generator is the gcd.", "L'idéal aℤ + bℤ est principal ; son générateur est le pgcd."],
    on: ["nu-bezout", "nu-gcd", "nu-coprime", "nu-diophantine", "pid"], uses: ["ideals-principal"] },
  { id: "gauss-lemma", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Gauss's lemma", "Lemme de Gauss"],
    s: ["If a | bc and gcd(a, b) = 1, then a | c.", "Si a | bc et pgcd(a, b) = 1, alors a | c."],
    i: ["Bézout: au + bv = 1 ⟹ c = auc + bcv, both terms divisible by a.", "Bézout : au + bv = 1 ⟹ c = auc + bcv, deux termes divisibles par a."],
    on: ["nu-gauss-lemma", "nu-coprime"], uses: ["bezout"] },
  { id: "fta", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Fundamental theorem of arithmetic", "Théorème fondamental de l'arithmétique"],
    s: ["Every integer n ≥ 2 is a product of primes, uniquely up to order.", "Tout entier n ≥ 2 est un produit de nombres premiers, de façon unique à l'ordre près."],
    i: ["Existence by strong induction; uniqueness from Gauss's lemma.", "Existence par récurrence forte ; unicité par le lemme de Gauss."],
    on: ["nu-prime-factorization", "nu-prime", "nu-valuation"],
    pr: [[["ℤ", "ℤ"], "ufd"]], uses: ["gauss-lemma"] },
  { id: "units-zmodn", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Invertible elements of ℤ/nℤ", "Inversibles de ℤ/nℤ"],
    s: ["The class of k is invertible in ℤ/nℤ iff gcd(k, n) = 1. In particular ℤ/nℤ is a field ⟺ n is prime.", "La classe de k est inversible dans ℤ/nℤ ssi pgcd(k, n) = 1. En particulier ℤ/nℤ est un corps ⟺ n est premier."],
    i: ["Bézout: ku + nv = 1 ⟹ k̄ · ū = 1̄.", "Bézout : ku + nv = 1 ⟹ k̄ · ū = 1̄."],
    on: ["z-mod-n"],
    pr: [[["ℤ/pℤ with p prime", "ℤ/pℤ avec p premier"], "finite-field"]], uses: ["bezout", "congruence-compat"] },
  { id: "fermat", topic: "arith", kind: "theorem", prepa: "MPSI",
    n: ["Fermat's little theorem", "Petit théorème de Fermat"],
    s: ["If p is prime and p ∤ a, then a^{p−1} ≡ 1 (mod p); hence aᵖ ≡ a (mod p) for every integer a.", "Si p est premier et p ∤ a, alors a^{p−1} ≡ 1 (mod p) ; donc aᵖ ≡ a (mod p) pour tout entier a."],
    i: ["Multiplication by a permutes the nonzero classes of ℤ/pℤ; compare the products.", "La multiplication par a permute les classes non nulles de ℤ/pℤ ; comparer les produits."],
    on: ["z-mod-n", "finite-field", "nu-prime"], uses: ["units-zmodn"] },
  { id: "crt", topic: "arith", kind: "theorem",
    n: ["Chinese remainder theorem", "Lemme chinois"],
    s: ["If gcd(m, n) = 1, then ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ as rings.", "Si pgcd(m, n) = 1, alors ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ comme anneaux."],
    i: ["x ↦ (x mod m, x mod n) is a ring morphism, injective by Gauss, hence bijective by cardinality.", "x ↦ (x mod m, x mod n) est un morphisme d'anneaux injectif (Gauss), donc bijectif par cardinal."],
    on: ["z-mod-n"],
    pr: [[["x ↦ (x mod m, x mod n)", "x ↦ (x mod m, x mod n)"], "mo-isomorphism"]], uses: ["gauss-lemma"] },

  // ===================== linear algebra & reduction =====================
  { id: "subspace-criterion", topic: "linalg", kind: "proposition", prepa: "MPSI",
    n: ["Subspace criterion", "Caractérisation des sous-espaces vectoriels"],
    s: ["F ⊆ E is a vector subspace iff 0 ∈ F and ∀x, y ∈ F, ∀λ, μ ∈ K, λx + μy ∈ F.", "F ⊆ E est un sous-espace vectoriel ssi 0 ∈ F et ∀x, y ∈ F, ∀λ, μ ∈ K, λx + μy ∈ F."],
    i: ["The axioms are inherited from E.", "Les axiomes sont hérités de E."],
    on: ["vector-space", "mo-vector-subspace"],
    pr: [[["F ⊆ E with 0 ∈ F and λx + μy ∈ F", "F ⊆ E avec 0 ∈ F et λx + μy ∈ F"], "vector-space"]] },
  { id: "basis-theorem", topic: "linalg", kind: "theorem", prepa: "MPSI",
    n: ["Incomplete basis theorem", "Théorème de la base incomplète"],
    s: ["In a finite-dimensional vector space, every linearly independent family extends to a basis and every spanning family contains a basis; all bases have the same cardinality (the dimension).", "Dans un espace vectoriel de dimension finie, toute famille libre se complète en une base et toute famille génératrice contient une base ; toutes les bases ont même cardinal (la dimension)."],
    i: ["Add vectors outside the span one at a time; the Steinitz exchange lemma bounds the size.", "Ajouter un vecteur hors du sous-espace engendré ; le lemme d'échange de Steinitz borne la taille."],
    on: [["vector-space", FIN]] },
  { id: "grassmann", topic: "linalg", kind: "theorem", prepa: "MPSI",
    n: ["Grassmann's formula", "Formule de Grassmann"],
    s: ["For subspaces F, G of a finite-dimensional space, dim(F + G) = dim F + dim G − dim(F ∩ G). Hence the sum F + G is direct ⟺ F ∩ G = {0} ⟺ dim(F + G) = dim F + dim G.", "Pour des sous-espaces F, G d'un espace de dimension finie, dim(F + G) = dim F + dim G − dim(F ∩ G). Donc la somme F + G est directe ⟺ F ∩ G = {0} ⟺ dim(F + G) = dim F + dim G."],
    i: ["Complete a basis of F ∩ G into bases of F and of G.", "Compléter une base de F ∩ G en des bases de F et de G."],
    on: [["vector-space", FIN], "mo-vector-subspace"], uses: ["basis-theorem"] },
  { id: "rank-nullity", topic: "linalg", kind: "theorem", prepa: "MPSI",
    n: ["Rank–nullity theorem", "Théorème du rang"],
    s: ["If E is finite-dimensional and u ∈ L(E, F), then dim E = dim ker u + rg u.", "Si E est de dimension finie et u ∈ L(E, F), alors dim E = dim ker u + rg u."],
    i: ["Complete a basis of ker u; the images of the added vectors form a basis of im u.", "Compléter une base de ker u ; les images des vecteurs ajoutés forment une base de im u."],
    on: [["vector-space", FIN], "mo-linear-map", "mx-endomorphism"], uses: ["basis-theorem"] },
  { id: "iso-criterion", topic: "linalg", kind: "proposition", prepa: "MPSI",
    n: ["Injective ⟺ surjective in equal finite dimension", "Injectif ⟺ surjectif en dimension finie égale"],
    s: ["If dim E = dim F < ∞ and u ∈ L(E, F), then u injective ⟺ u surjective ⟺ u bijective. In particular for an endomorphism of a finite-dimensional space.", "Si dim E = dim F < ∞ et u ∈ L(E, F), alors u injectif ⟺ u surjectif ⟺ u bijectif. En particulier pour un endomorphisme en dimension finie."],
    i: ["Rank–nullity: ker u = {0} ⟺ rg u = dim E = dim F.", "Théorème du rang : ker u = {0} ⟺ rg u = dim E = dim F."],
    on: [["vector-space", FIN], "mx-endomorphism", "mx-automorphism-lin"],
    pr: [[["an injective endomorphism of a finite-dimensional space", "un endomorphisme injectif d'un espace de dimension finie"], "mx-automorphism-lin"]], uses: ["rank-nullity"] },
  { id: "matrix-correspondence", topic: "linalg", kind: "theorem", prepa: "MPSI",
    n: ["Matrices represent linear maps", "Représentation matricielle des applications linéaires"],
    s: ["Once bases are chosen, u ↦ Mat(u) is an isomorphism L(E, F) → M_{n,p}(K) which turns composition into matrix product; for E = F it is an isomorphism of algebras L(E) → Mₙ(K).", "Une fois des bases choisies, u ↦ Mat(u) est un isomorphisme L(E, F) → M_{n,p}(K) qui transforme la composition en produit matriciel ; pour E = F, c'est un isomorphisme d'algèbres L(E) → Mₙ(K)."],
    i: ["A linear map is determined by the images of a basis, i.e. by a matrix.", "Une application linéaire est déterminée par les images d'une base, c'est-à-dire par une matrice."],
    on: ["endomorphism-algebra", "matrix-ring", "mx-matrix"],
    pr: [[["u ↦ Mat_B(u), from L(E) to Mₙ(K)", "u ↦ Mat_B(u), de L(E) dans Mₙ(K)"], "mo-isomorphism"]] },
  { id: "linear-system-structure", topic: "linalg", kind: "proposition", prepa: "MPSI",
    n: ["Solutions of a linear system", "Structure des solutions d'un système linéaire"],
    s: ["The solutions of AX = 0 form the subspace ker A. If AX = B has a solution X₀, its solution set is the affine subspace X₀ + ker A.", "Les solutions de AX = 0 forment le sous-espace ker A. Si AX = B admet une solution X₀, l'ensemble de ses solutions est le sous-espace affine X₀ + ker A."],
    i: ["AX = B and AX₀ = B ⟺ A(X − X₀) = 0.", "AX = B et AX₀ = B ⟺ A(X − X₀) = 0."],
    on: ["mx-linear-system", "mx-homogeneous-system"],
    pr: [[["{X : AX = 0}", "{X : AX = 0}"], "vector-space"], [["{X : AX = B}, if nonempty", "{X : AX = B}, s'il est non vide"], "affine-space"]] },
  { id: "det-invertible", topic: "linalg", kind: "theorem", prepa: "MPSI",
    n: ["Determinant and invertibility", "Déterminant et inversibilité"],
    s: ["A ∈ Mₙ(K) is invertible ⟺ det A ≠ 0 ⟺ rg A = n. Moreover det(AB) = det A · det B and A⁻¹ = (1 / det A) · ᵗcom(A).", "A ∈ Mₙ(K) est inversible ⟺ det A ≠ 0 ⟺ rg A = n. De plus det(AB) = det A · det B et A⁻¹ = (1 / det A) · ᵗcom(A)."],
    i: ["The determinant is the unique alternating n-linear form with det(Iₙ) = 1; expand along a column for the cofactor formula.", "Le déterminant est l'unique forme n-linéaire alternée valant 1 sur Iₙ ; développement selon une colonne pour la formule de la comatrice."],
    on: ["mx-determinant", "mx-invertible-matrix", "general-linear-group", "matrix-ring"],
    pr: [[["A with det A ≠ 0", "A avec det A ≠ 0"], "mx-invertible-matrix"]] },
  { id: "eigen-roots", topic: "linalg", kind: "proposition", prepa: "MP",
    n: ["Eigenvalues and the characteristic polynomial", "Valeurs propres et polynôme caractéristique"],
    s: ["For u ∈ L(E), E finite-dimensional: λ is an eigenvalue of u ⟺ χᵤ(λ) = 0 ⟺ u − λ·Id is not invertible. Eigenvectors for distinct eigenvalues are linearly independent: the eigenspaces are in direct sum.", "Pour u ∈ L(E), E de dimension finie : λ est valeur propre de u ⟺ χᵤ(λ) = 0 ⟺ u − λ·Id n'est pas inversible. Des vecteurs propres associés à des valeurs propres distinctes sont libres : les sous-espaces propres sont en somme directe."],
    i: ["Induction on the number of eigenvalues for the independence.", "Récurrence sur le nombre de valeurs propres pour l'indépendance."],
    on: ["mx-endomorphism"], uses: ["det-invertible"] },
  { id: "kernel-lemma", topic: "linalg", kind: "theorem", prepa: "MP",
    n: ["Kernel lemma", "Lemme des noyaux"],
    s: ["If P = P₁ ⋯ P_k with pairwise coprime Pᵢ, then ker P(u) = ker P₁(u) ⊕ ⋯ ⊕ ker P_k(u).", "Si P = P₁ ⋯ P_k avec des Pᵢ deux à deux premiers entre eux, alors ker P(u) = ker P₁(u) ⊕ ⋯ ⊕ ker P_k(u)."],
    i: ["Bézout in K[X] gives the projectors as polynomials in u.", "Bézout dans K[X] fournit les projecteurs comme polynômes en u."],
    on: ["endomorphism-algebra", "poly-ring"], uses: ["ideals-principal"] },
  { id: "cayley-hamilton", topic: "linalg", kind: "theorem", prepa: "MP",
    n: ["Cayley–Hamilton theorem", "Théorème de Cayley–Hamilton"],
    s: ["For u ∈ L(E), E finite-dimensional, χᵤ(u) = 0. Equivalently, every square matrix annihilates its characteristic polynomial.", "Pour u ∈ L(E), E de dimension finie, χᵤ(u) = 0. De façon équivalente, toute matrice carrée annule son polynôme caractéristique."],
    i: ["Check on each cyclic subspace Vect(x, u(x), u²(x), …), whose characteristic polynomial divides χᵤ.", "Vérifier sur chaque sous-espace cyclique Vect(x, u(x), u²(x), …), dont le polynôme caractéristique divise χᵤ."],
    on: ["endomorphism-algebra", "mx-endomorphism"], uses: ["eigen-roots"] },
  { id: "diag-criteria", topic: "linalg", kind: "theorem", prepa: "MP",
    n: ["Diagonalizability criteria", "Critères de diagonalisabilité"],
    s: ["u is diagonalizable ⟺ E = ⊕ E_λ(u) ⟺ χᵤ is split and dim E_λ = multiplicity of λ for each λ ⟺ u has a split annihilating polynomial with simple roots.", "u est diagonalisable ⟺ E = ⊕ E_λ(u) ⟺ χᵤ est scindé et dim E_λ = multiplicité de λ pour tout λ ⟺ u admet un polynôme annulateur scindé à racines simples."],
    i: ["Apply the kernel lemma to a split annihilating polynomial with simple roots.", "Appliquer le lemme des noyaux à un polynôme annulateur scindé à racines simples."],
    on: ["mx-endomorphism", "mx-diagonalizable"],
    pr: [[["u with a split annihilating polynomial with simple roots", "u admettant un polynôme annulateur scindé à racines simples"], "mx-diagonalizable"]], uses: ["kernel-lemma", "eigen-roots"] },
  { id: "trigonalisation", topic: "linalg", kind: "theorem", prepa: "MP",
    n: ["Triangularization", "Trigonalisation"],
    s: ["u ∈ L(E) is triangularizable ⟺ χᵤ is split over K. Over an algebraically closed field, every endomorphism is triangularizable.", "u ∈ L(E) est trigonalisable ⟺ χᵤ est scindé sur K. Sur un corps algébriquement clos, tout endomorphisme est trigonalisable."],
    i: ["Induction on dim E using one eigenvector and the quotient space.", "Récurrence sur dim E avec un vecteur propre et l'espace quotient."],
    on: ["mx-triangularizable", "algebraically-closed-field"],
    pr: [[["an endomorphism of a finite-dimensional ℂ-vector space", "un endomorphisme d'un ℂ-espace vectoriel de dimension finie"], "mx-triangularizable"]], uses: ["eigen-roots", "dalembert"] },

  // ===================== Euclidean & Hermitian spaces =====================
  { id: "cauchy-schwarz", topic: "euclid", kind: "inequality", prepa: "MP",
    n: ["Cauchy–Schwarz inequality", "Inégalité de Cauchy–Schwarz"],
    s: ["In an inner product space, |⟨x, y⟩| ≤ ‖x‖ ‖y‖, with equality ⟺ x and y are linearly dependent. Consequently ‖x‖ = √⟨x, x⟩ satisfies the triangle inequality and is a norm.", "Dans un espace préhilbertien, |⟨x, y⟩| ≤ ‖x‖ ‖y‖, avec égalité ⟺ x et y sont liés. Par conséquent ‖x‖ = √⟨x, x⟩ vérifie l'inégalité triangulaire et est une norme."],
    i: ["The quadratic t ↦ ⟨x + ty, x + ty⟩ is nonnegative: its discriminant is ≤ 0.", "Le trinôme t ↦ ⟨x + ty, x + ty⟩ est positif : son discriminant est ≤ 0."],
    on: ["inner-product-space", "complex-inner-product-space"],
    pr: [[["(E, ⟨·,·⟩) with ‖x‖ = √⟨x, x⟩", "(E, ⟨·,·⟩) avec ‖x‖ = √⟨x, x⟩"], "normed-space"]] },
  { id: "gram-schmidt", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Gram–Schmidt orthonormalization", "Orthonormalisation de Gram–Schmidt"],
    s: ["From any basis (e₁, …, eₙ) of a Euclidean or Hermitian space one builds an orthonormal basis (ε₁, …, εₙ) with Vect(e₁, …, eₖ) = Vect(ε₁, …, εₖ) for all k. In particular orthonormal bases exist.", "À partir de toute base (e₁, …, eₙ) d'un espace euclidien ou hermitien on construit une base orthonormée (ε₁, …, εₙ) avec Vect(e₁, …, eₖ) = Vect(ε₁, …, εₖ) pour tout k. En particulier les bases orthonormées existent."],
    i: ["Subtract the orthogonal projection onto the span of the previous vectors, then normalize.", "Retrancher la projection orthogonale sur le sous-espace engendré par les précédents, puis normaliser."],
    on: ["euclidean-space", "hermitian-space"] },
  { id: "orth-complement", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Orthogonal complement and best approximation", "Supplémentaire orthogonal et meilleure approximation"],
    s: ["If F is a finite-dimensional subspace of an inner product space E, then E = F ⊕ F^⊥. The orthogonal projection p_F satisfies d(x, F) = ‖x − p_F(x)‖: p_F(x) is the unique closest point of F.", "Si F est un sous-espace de dimension finie d'un espace préhilbertien E, alors E = F ⊕ F^⊥. Le projecteur orthogonal p_F vérifie d(x, F) = ‖x − p_F(x)‖ : p_F(x) est l'unique point de F le plus proche de x."],
    i: ["Write x = p_F(x) + (x − p_F(x)) and apply Pythagoras.", "Écrire x = p_F(x) + (x − p_F(x)) et appliquer Pythagore."],
    on: ["inner-product-space", "euclidean-space"], uses: ["gram-schmidt"] },
  { id: "riesz-fd", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Riesz representation (finite dimension)", "Représentation de Riesz (dimension finie)"],
    s: ["In a Euclidean space E, every linear form is x ↦ ⟨a, x⟩ for a unique a ∈ E; the map a ↦ ⟨a, ·⟩ is an isomorphism E → E*.", "Dans un espace euclidien E, toute forme linéaire s'écrit x ↦ ⟨a, x⟩ pour un unique a ∈ E ; l'application a ↦ ⟨a, ·⟩ est un isomorphisme E → E*."],
    i: ["Injective by definiteness; equal dimensions.", "Injective par caractère défini ; dimensions égales."],
    on: ["euclidean-space"],
    pr: [[["a ↦ ⟨a, ·⟩, from E to E*", "a ↦ ⟨a, ·⟩, de E dans E*"], "mo-isomorphism"]], uses: ["iso-criterion"] },
  { id: "orth-characterization", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Characterization of orthogonal endomorphisms", "Caractérisation des endomorphismes orthogonaux"],
    s: ["For u ∈ L(E), E Euclidean, TFAE: u preserves the inner product; u preserves the norm; u maps an (every) orthonormal basis to an orthonormal basis; its matrix A in an orthonormal basis satisfies ᵗAA = Iₙ. Such endomorphisms form a group O(E).", "Pour u ∈ L(E), E euclidien, il y a équivalence entre : u conserve le produit scalaire ; u conserve la norme ; u envoie une (toute) base orthonormée sur une base orthonormée ; sa matrice A dans une base orthonormée vérifie ᵗAA = Iₙ. Ces endomorphismes forment un groupe O(E)."],
    i: ["Polarization identity: the norm determines the inner product.", "Identité de polarisation : la norme détermine le produit scalaire."],
    on: ["euclidean-space", "orthogonal-group", "mx-orthogonal-matrix", "mo-isometry"],
    pr: [[["{u ∈ L(E) : ᵗAA = Iₙ}", "{u ∈ L(E) : ᵗAA = Iₙ}"], "orthogonal-group"]], uses: ["gram-schmidt"] },
  { id: "spectral-real", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Spectral theorem (real symmetric)", "Théorème spectral (symétrique réel)"],
    s: ["Every symmetric endomorphism of a Euclidean space is diagonalizable in an orthonormal basis: for A ∈ Sₙ(ℝ) there is P ∈ Oₙ(ℝ) with ᵗPAP diagonal.", "Tout endomorphisme symétrique d'un espace euclidien est diagonalisable en base orthonormée : pour A ∈ Sₙ(ℝ), il existe P ∈ Oₙ(ℝ) telle que ᵗPAP soit diagonale."],
    i: ["Eigenvalues are real, eigenspaces are orthogonal, and the orthogonal of a stable subspace is stable.", "Les valeurs propres sont réelles, les sous-espaces propres orthogonaux, et l'orthogonal d'un sous-espace stable est stable."],
    on: ["euclidean-space", "mx-symmetric-matrix"],
    pr: [[["a symmetric endomorphism of a Euclidean space", "un endomorphisme symétrique d'un espace euclidien"], "mx-diagonalizable"]], uses: ["diag-criteria", "orth-complement"] },
  { id: "spectral-hermitian", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Spectral theorem (Hermitian, normal)", "Théorème spectral (hermitien, normal)"],
    s: ["A Hermitian (more generally normal) endomorphism of a Hermitian space is diagonalizable in an orthonormal basis; the eigenvalues are real in the Hermitian case and of modulus 1 in the unitary case.", "Un endomorphisme hermitien (plus généralement normal) d'un espace hermitien est diagonalisable en base orthonormée ; ses valeurs propres sont réelles dans le cas hermitien et de module 1 dans le cas unitaire."],
    i: ["Same scheme as the real case, over ℂ where eigenvalues always exist.", "Même schéma que le cas réel, sur ℂ où les valeurs propres existent toujours."],
    on: ["hermitian-space", "mx-hermitian-matrix", "mx-unitary-matrix", "unitary-group"],
    pr: [[["a Hermitian endomorphism of a Hermitian space", "un endomorphisme hermitien d'un espace hermitien"], "mx-diagonalizable"]], uses: ["trigonalisation", "spectral-real"] },
  { id: "isometry-reduction", topic: "euclid", kind: "theorem", prepa: "MP",
    n: ["Reduction of orthogonal endomorphisms", "Réduction des endomorphismes orthogonaux"],
    s: ["In a suitable orthonormal basis, an orthogonal endomorphism has a block-diagonal matrix with blocks 1, −1 and plane rotations R(θ). In dimension 2, O₂(ℝ) consists of rotations and reflections; in dimension 3 an element of SO₃(ℝ) is a rotation about an axis.", "Dans une base orthonormée adaptée, la matrice d'un endomorphisme orthogonal est diagonale par blocs, avec des blocs 1, −1 et des rotations planes R(θ). En dimension 2, O₂(ℝ) est formé de rotations et de réflexions ; en dimension 3, un élément de SO₃(ℝ) est une rotation d'axe donné."],
    i: ["Find a stable line or plane and use that its orthogonal is stable.", "Trouver une droite ou un plan stable et utiliser la stabilité de son orthogonal."],
    on: ["orthogonal-group", "special-orthogonal-group"], uses: ["orth-characterization"] },

  // ===================== topology of normed spaces =====================
  { id: "normed-metric", topic: "topo", kind: "proposition", prepa: "MP",
    n: ["A norm induces a distance", "Une norme induit une distance"],
    s: ["If ‖·‖ is a norm on E, then d(x, y) = ‖x − y‖ is a distance on E. Open balls, open and closed sets, limits and continuity are all defined through it.", "Si ‖·‖ est une norme sur E, alors d(x, y) = ‖x − y‖ est une distance sur E. Boules, ouverts, fermés, limites et continuité s'en déduisent."],
    i: ["The three axioms of d are the three axioms of the norm.", "Les trois axiomes de d sont ceux de la norme."],
    on: ["normed-space"],
    pr: [[["(E, d), d(x, y) = ‖x − y‖", "(E, d), d(x, y) = ‖x − y‖"], "metric-space"]] },
  { id: "equivalent-norms", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Equivalence of norms in finite dimension", "Équivalence des normes en dimension finie"],
    s: ["On a finite-dimensional real or complex vector space all norms are equivalent. Hence convergence, open sets, compactness and continuity do not depend on the norm.", "Sur un espace vectoriel réel ou complexe de dimension finie, toutes les normes sont équivalentes. Convergence, ouverts, compacité et continuité ne dépendent donc pas de la norme."],
    i: ["Compare any norm with ‖·‖∞ using the compactness of its unit sphere.", "Comparer toute norme à ‖·‖∞ grâce à la compacité de sa sphère unité."],
    on: [["normed-space", FIN]], uses: ["bolzano-weierstrass"] },
  { id: "compact-fd", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Compact sets in finite dimension", "Parties compactes en dimension finie"],
    s: ["In a finite-dimensional normed space, a subset is compact ⟺ it is closed and bounded.", "Dans un espace normé de dimension finie, une partie est compacte ⟺ elle est fermée et bornée."],
    i: ["Bolzano–Weierstrass in the sup-norm, then equivalence of norms.", "Bolzano–Weierstrass pour la norme infinie, puis équivalence des normes."],
    on: [["normed-space", FIN], "compact-space"],
    pr: [[["a closed bounded subset of a finite-dimensional normed space", "une partie fermée bornée d'un espace normé de dimension finie"], "compact-space"]], uses: ["bolzano-weierstrass", "equivalent-norms"] },
  { id: "fd-complete", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Finite-dimensional normed spaces are complete", "Les espaces normés de dimension finie sont complets"],
    s: ["Every finite-dimensional normed space is complete (a Banach space).", "Tout espace normé de dimension finie est complet (espace de Banach)."],
    i: ["Equivalence of norms, then completeness of ℝ and ℂ coordinate by coordinate.", "Équivalence des normes, puis complétude de ℝ et ℂ coordonnée par coordonnée."],
    on: [["normed-space", FIN], "complete-metric-space"],
    pr: [[["a finite-dimensional normed space", "un espace normé de dimension finie"], "banach-space"]], uses: ["equivalent-norms", "cauchy-criterion"] },
  { id: "extreme-value", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Continuous image of a compact set", "Image continue d'un compact"],
    s: ["The continuous image of a compact set is compact. In particular a continuous real function on a compact set is bounded and attains its bounds.", "L'image continue d'un compact est compacte. En particulier une fonction réelle continue sur un compact est bornée et atteint ses bornes."],
    i: ["From a sequence in f(K), extract a convergent subsequence of preimages.", "À partir d'une suite de f(K), extraire une sous-suite convergente de ses antécédents."],
    on: ["compact-space", "an-continuous"],
    pr: [[["f(K), K compact, f continuous", "f(K), K compact, f continue"], "compact-space"]] },
  { id: "heine", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Heine's theorem", "Théorème de Heine"],
    s: ["Every continuous function on a compact set is uniformly continuous.", "Toute fonction continue sur un compact est uniformément continue."],
    i: ["Otherwise take sequences xₙ, yₙ with d(xₙ, yₙ) → 0 and |f(xₙ) − f(yₙ)| ≥ ε, extract, and contradict continuity.", "Sinon, prendre xₙ, yₙ avec d(xₙ, yₙ) → 0 et |f(xₙ) − f(yₙ)| ≥ ε, extraire, contredire la continuité."],
    on: ["compact-space", "an-uniformly-continuous"],
    pr: [[["f continuous on a compact set", "f continue sur un compact"], "an-uniformly-continuous"]] },
  { id: "image-arcs", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Continuous image of a path-connected set", "Image continue d'une partie connexe par arcs"],
    s: ["The continuous image of a path-connected set is path-connected. In ℝ the path-connected sets are exactly the intervals, which gives the intermediate value theorem.", "L'image continue d'une partie connexe par arcs est connexe par arcs. Dans ℝ les parties connexes par arcs sont exactement les intervalles, d'où le théorème des valeurs intermédiaires."],
    i: ["Compose a path with f.", "Composer un chemin avec f."],
    on: ["path-connected-space", "an-continuous"],
    pr: [[["f(A), A path-connected, f continuous", "f(A), A connexe par arcs, f continue"], "path-connected-space"]] },
  { id: "linear-continuity", topic: "topo", kind: "theorem", prepa: "MP",
    n: ["Continuity of linear maps", "Continuité des applications linéaires"],
    s: ["A linear map u between normed spaces is continuous ⟺ ∃C, ∀x, ‖u(x)‖ ≤ C‖x‖. If the source is finite-dimensional, every linear map is continuous.", "Une application linéaire u entre espaces normés est continue ⟺ ∃C, ∀x, ‖u(x)‖ ≤ C‖x‖. Si la source est de dimension finie, toute application linéaire est continue."],
    i: ["Linearity reduces continuity at 0 to a bound on the unit ball; in finite dimension use a basis and equivalence of norms.", "La linéarité ramène la continuité en 0 à une borne sur la boule unité ; en dimension finie, utiliser une base et l'équivalence des normes."],
    on: ["normed-space", "mo-linear-map", "mo-continuous-map"],
    pr: [[["u linear on a finite-dimensional normed space", "u linéaire sur un espace normé de dimension finie"], "mo-continuous-map"]], uses: ["equivalent-norms"] },

  // ===================== real analysis =====================
  { id: "bolzano-weierstrass", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Bolzano–Weierstrass theorem", "Théorème de Bolzano–Weierstrass"],
    s: ["Every bounded real (or complex) sequence has a convergent subsequence.", "Toute suite réelle (ou complexe) bornée admet une sous-suite convergente."],
    i: ["Every real sequence has a monotone subsequence; a bounded monotone one converges.", "Toute suite réelle admet une sous-suite monotone ; si elle est bornée, elle converge."],
    on: ["an-bounded-seq", "an-sequence"],
    pr: [[["a subsequence of a bounded sequence", "une sous-suite d'une suite bornée"], "an-convergent-seq"]], uses: ["monotone-limit"] },
  { id: "monotone-limit", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Monotone limit theorem", "Théorème de la limite monotone"],
    s: ["An increasing sequence bounded above converges (to its supremum); an increasing sequence not bounded above tends to +∞. Symmetrically for decreasing sequences.", "Une suite croissante majorée converge (vers sa borne supérieure) ; une suite croissante non majorée tend vers +∞. De même pour les suites décroissantes."],
    i: ["The supremum exists by the least upper bound property of ℝ.", "La borne supérieure existe par la propriété de la borne supérieure de ℝ."],
    on: ["an-monotone-seq"], 
    pr: [[["a monotone bounded real sequence", "une suite réelle monotone bornée"], "an-convergent-seq"]] },
  { id: "adjacent", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Adjacent sequences theorem", "Théorème des suites adjacentes"],
    s: ["If (uₙ) is increasing, (vₙ) decreasing and vₙ − uₙ → 0, both converge to the same limit ℓ and uₙ ≤ ℓ ≤ vₙ for all n.", "Si (uₙ) est croissante, (vₙ) décroissante et vₙ − uₙ → 0, elles convergent vers la même limite ℓ et uₙ ≤ ℓ ≤ vₙ pour tout n."],
    i: ["Both are monotone and bounded by each other.", "Elles sont monotones et bornées l'une par l'autre."],
    on: ["an-adjacent-seq", "an-monotone-seq"],
    pr: [[["adjacent sequences", "des suites adjacentes"], "an-convergent-seq"]], uses: ["monotone-limit"] },
  { id: "cauchy-criterion", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Cauchy criterion in ℝ and ℂ", "Critère de Cauchy dans ℝ et ℂ"],
    s: ["A real or complex sequence converges ⟺ it is a Cauchy sequence. Hence ℝ and ℂ are complete.", "Une suite réelle ou complexe converge ⟺ elle est de Cauchy. Ainsi ℝ et ℂ sont complets."],
    i: ["A Cauchy sequence is bounded, so it has a convergent subsequence (Bolzano–Weierstrass), and then converges.", "Une suite de Cauchy est bornée, donc admet une sous-suite convergente (Bolzano–Weierstrass), puis converge."],
    on: ["an-cauchy-seq", "an-convergent-seq"],
    pr: [[["ℝ and ℂ", "ℝ et ℂ"], "complete-metric-space"], [["a Cauchy sequence of reals", "une suite de Cauchy de réels"], "an-convergent-seq"]], uses: ["bolzano-weierstrass"] },
  { id: "weierstrass-bounds", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Extreme value theorem on a segment", "Théorème des bornes atteintes"],
    s: ["A continuous real function on a segment [a, b] is bounded and attains its bounds; its image is a segment.", "Une fonction réelle continue sur un segment [a, b] est bornée et atteint ses bornes ; son image est un segment."],
    i: ["Take a sequence approaching the supremum, extract (Bolzano–Weierstrass), pass to the limit.", "Prendre une suite tendant vers la borne supérieure, extraire (Bolzano–Weierstrass), passer à la limite."],
    on: ["an-continuous", "an-bounded"],
    pr: [[["f continuous on [a, b]", "f continue sur [a, b]"], "an-bounded"]], uses: ["bolzano-weierstrass"] },
  { id: "ivt", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Intermediate value theorem", "Théorème des valeurs intermédiaires"],
    s: ["If f is continuous on an interval I, then f(I) is an interval. In particular if f(a) f(b) < 0 then f vanishes between a and b.", "Si f est continue sur un intervalle I, alors f(I) est un intervalle. En particulier si f(a) f(b) < 0, f s'annule entre a et b."],
    i: ["Dichotomy: nested segments on which f changes sign (adjacent sequences).", "Dichotomie : segments emboîtés sur lesquels f change de signe (suites adjacentes)."],
    on: ["an-continuous", "path-connected-space"], uses: ["adjacent"] },
  { id: "bijection-theorem", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Continuous strictly monotone bijection", "Théorème de la bijection"],
    s: ["If f is continuous and strictly monotone on an interval I, it is a bijection from I onto the interval f(I), and f⁻¹ is continuous and strictly monotone in the same direction.", "Si f est continue et strictement monotone sur un intervalle I, c'est une bijection de I sur l'intervalle f(I), et f⁻¹ est continue et strictement monotone de même sens."],
    i: ["Surjectivity from the intermediate value theorem; continuity of f⁻¹ because it maps an interval to an interval monotonically.", "Surjectivité par les valeurs intermédiaires ; continuité de f⁻¹ car elle est monotone d'image un intervalle."],
    on: ["an-continuous", "an-monotone", "an-bijective"],
    pr: [[["f continuous and strictly monotone on an interval", "f continue et strictement monotone sur un intervalle"], "an-homeomorphism"]], uses: ["ivt"] },
  { id: "differentiable-continuous", topic: "analysis", kind: "proposition", prepa: "MPSI",
    n: ["Differentiable implies continuous", "Dérivable implique continue"],
    s: ["If f is differentiable at a, then f is continuous at a. The converse is false (x ↦ |x| at 0).", "Si f est dérivable en a, alors f est continue en a. La réciproque est fausse (x ↦ |x| en 0)."],
    i: ["f(a + h) − f(a) = h · (f(a + h) − f(a))/h → 0 · f′(a).", "f(a + h) − f(a) = h · (f(a + h) − f(a))/h → 0 · f′(a)."],
    on: ["an-differentiable"],
    pr: [[["f differentiable at a", "f dérivable en a"], "an-continuous"]] },
  { id: "rolle-mvt", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Rolle's theorem and the mean value theorem", "Théorème de Rolle et théorème des accroissements finis"],
    s: ["Rolle: f continuous on [a, b], differentiable on ]a, b[ and f(a) = f(b) ⟹ ∃c ∈ ]a, b[, f′(c) = 0. Mean value theorem: ∃c, f(b) − f(a) = f′(c)(b − a). Hence |f′| ≤ M ⟹ |f(b) − f(a)| ≤ M |b − a| (inequality of finite increments).", "Rolle : f continue sur [a, b], dérivable sur ]a, b[ et f(a) = f(b) ⟹ ∃c ∈ ]a, b[, f′(c) = 0. Accroissements finis : ∃c, f(b) − f(a) = f′(c)(b − a). Donc |f′| ≤ M ⟹ |f(b) − f(a)| ≤ M |b − a| (inégalité des accroissements finis)."],
    i: ["An extremum in the open interval has zero derivative; the MVT applies Rolle to f minus its chord.", "Un extremum à l'intérieur a une dérivée nulle ; les accroissements finis appliquent Rolle à f moins sa corde."],
    on: ["an-differentiable", "an-continuous"],
    pr: [[["f differentiable with |f′| ≤ M", "f dérivable avec |f′| ≤ M"], "an-lipschitz"]], uses: ["weierstrass-bounds"] },
  { id: "monotone-derivative", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Sign of the derivative", "Signe de la dérivée et monotonie"],
    s: ["For f differentiable on an interval: f is increasing ⟺ f′ ≥ 0; f is strictly increasing ⟺ f′ ≥ 0 and f′ does not vanish identically on any subinterval; f is constant ⟺ f′ = 0.", "Pour f dérivable sur un intervalle : f est croissante ⟺ f′ ≥ 0 ; f est strictement croissante ⟺ f′ ≥ 0 et f′ ne s'annule identiquement sur aucun sous-intervalle ; f est constante ⟺ f′ = 0."],
    i: ["Mean value theorem.", "Théorème des accroissements finis."],
    on: ["an-differentiable", "an-monotone"],
    pr: [[["f with f′ ≥ 0", "f avec f′ ≥ 0"], "an-monotone"]], uses: ["rolle-mvt"] },
  { id: "taylor", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Taylor formulas", "Formules de Taylor"],
    s: ["For f of class Cⁿ⁺¹ and Tₙ its Taylor polynomial at a: integral remainder f(b) = Tₙ(b) + ∫ₐᵇ ((b − t)ⁿ/n!) f^{(n+1)}(t) dt; Taylor–Lagrange |f(b) − Tₙ(b)| ≤ M |b − a|ⁿ⁺¹/(n + 1)! with M = sup|f^{(n+1)}|; Taylor–Young f(x) = Tₙ(x) + o((x − a)ⁿ) for f n times differentiable at a.", "Pour f de classe Cⁿ⁺¹ et Tₙ son polynôme de Taylor en a : reste intégral f(b) = Tₙ(b) + ∫ₐᵇ ((b − t)ⁿ/n!) f^{(n+1)}(t) dt ; Taylor–Lagrange |f(b) − Tₙ(b)| ≤ M |b − a|ⁿ⁺¹/(n + 1)! avec M = sup|f^{(n+1)}| ; Taylor–Young f(x) = Tₙ(x) + o((x − a)ⁿ) pour f n fois dérivable en a."],
    i: ["Induction on n with integration by parts.", "Récurrence sur n avec des intégrations par parties."],
    on: ["an-ck", "an-cinf", "an-analytic"], uses: ["ftc"] },
  { id: "convex-derivative", topic: "analysis", kind: "theorem", prepa: "MP",
    n: ["Convexity and derivatives", "Convexité et dérivées"],
    s: ["For f differentiable: f is convex ⟺ f′ is increasing. For f twice differentiable: f is convex ⟺ f″ ≥ 0. A convex function lies above its tangents and below its chords.", "Pour f dérivable : f est convexe ⟺ f′ est croissante. Pour f deux fois dérivable : f est convexe ⟺ f″ ≥ 0. Une fonction convexe est au-dessus de ses tangentes et en dessous de ses cordes."],
    i: ["Slopes of chords increase with their endpoints; apply the mean value theorem.", "Les pentes des cordes croissent avec leurs extrémités ; appliquer les accroissements finis."],
    on: ["an-convex"], uses: ["monotone-derivative"] },
  { id: "ftc", topic: "analysis", kind: "theorem", prepa: "MPSI",
    n: ["Fundamental theorem of calculus", "Théorème fondamental de l'analyse"],
    s: ["If f is continuous on an interval I and a ∈ I, then F : x ↦ ∫ₐˣ f(t) dt is the unique primitive of f vanishing at a; it is of class C¹ with F′ = f. Hence ∫ₐᵇ f = G(b) − G(a) for any primitive G.", "Si f est continue sur un intervalle I et a ∈ I, alors F : x ↦ ∫ₐˣ f(t) dt est l'unique primitive de f s'annulant en a ; elle est de classe C¹ et F′ = f. Donc ∫ₐᵇ f = G(b) − G(a) pour toute primitive G."],
    i: ["(F(x + h) − F(x))/h is the mean of f on [x, x + h], which tends to f(x) by continuity.", "(F(x + h) − F(x))/h est la moyenne de f sur [x, x + h], qui tend vers f(x) par continuité."],
    on: ["an-continuous", "an-c1"],
    pr: [[["x ↦ ∫ₐˣ f(t) dt, f continuous", "x ↦ ∫ₐˣ f(t) dt, f continue"], "an-c1"]] },
  { id: "multivar-c1", topic: "analysis", kind: "theorem", prepa: "MP",
    n: ["C¹ implies differentiable (several variables)", "Classe C¹ ⟹ différentiable (plusieurs variables)"],
    s: ["If all partial derivatives of f exist and are continuous on an open set U (f is C¹), then f is differentiable on U and df_a(h) = Σᵢ ∂ᵢf(a) hᵢ. Mere existence of partial derivatives is not enough.", "Si toutes les dérivées partielles de f existent et sont continues sur un ouvert U (f est de classe C¹), alors f est différentiable sur U et df_a(h) = Σᵢ ∂ᵢf(a) hᵢ. La seule existence des dérivées partielles ne suffit pas."],
    i: ["Move one coordinate at a time and apply the mean value theorem.", "Faire varier une coordonnée à la fois et appliquer les accroissements finis."],
    on: ["an-partial-derivatives", "an-c1-multivar"],
    pr: [[["f with continuous partial derivatives", "f à dérivées partielles continues"], "an-differentiable-multivar"]], uses: ["rolle-mvt"] },
  { id: "chain-rule", topic: "analysis", kind: "theorem", prepa: "MP",
    n: ["Chain rule", "Règle de la chaîne"],
    s: ["If f is differentiable at a and g at f(a), then g ∘ f is differentiable at a and d(g ∘ f)ₐ = dg_{f(a)} ∘ dfₐ; in coordinates the Jacobian matrices multiply.", "Si f est différentiable en a et g en f(a), alors g ∘ f est différentiable en a et d(g ∘ f)ₐ = dg_{f(a)} ∘ dfₐ ; en coordonnées, les matrices jacobiennes se multiplient."],
    i: ["Compose the first-order expansions of f and g.", "Composer les développements limités à l'ordre 1 de f et g."],
    on: ["an-differentiable-multivar"],
    pr: [[["g ∘ f", "g ∘ f"], "an-differentiable-multivar"]] },
  { id: "schwarz", topic: "analysis", kind: "theorem", prepa: "MP",
    n: ["Schwarz's theorem", "Théorème de Schwarz"],
    s: ["If f is of class C² on an open set, then ∂ᵢ∂ⱼf = ∂ⱼ∂ᵢf; hence its Hessian matrix is symmetric.", "Si f est de classe C² sur un ouvert, alors ∂ᵢ∂ⱼf = ∂ⱼ∂ᵢf ; sa matrice hessienne est donc symétrique."],
    i: ["Compare two expressions of the same second difference with the mean value theorem.", "Comparer deux écritures d'une même différence seconde avec les accroissements finis."],
    on: ["an-c1-multivar"],
    pr: [[["the Hessian matrix of a C² function", "la hessienne d'une fonction C²"], "mx-symmetric-matrix"]], uses: ["multivar-c1"] },
  { id: "critical-point", topic: "analysis", kind: "proposition", prepa: "MP",
    n: ["Necessary condition for an extremum", "Condition nécessaire d'extremum"],
    s: ["If f : U → ℝ (U open) is differentiable and has a local extremum at a, then df_a = 0, i.e. ∇f(a) = 0.", "Si f : U → ℝ (U ouvert) est différentiable et admet un extremum local en a, alors df_a = 0, c'est-à-dire ∇f(a) = 0."],
    i: ["Apply the one-variable result to t ↦ f(a + tv) for each direction v.", "Appliquer le résultat à une variable à t ↦ f(a + tv) pour chaque direction v."],
    on: ["an-differentiable-multivar"], uses: ["rolle-mvt"] },

  // ===================== series & sequences of functions =====================
  { id: "abs-conv", topic: "series", kind: "theorem", prepa: "MPSI",
    n: ["Absolute convergence implies convergence", "Convergence absolue ⟹ convergence"],
    s: ["If Σ|uₙ| converges then Σuₙ converges and |Σuₙ| ≤ Σ|uₙ| (in ℝ, ℂ, and any finite-dimensional normed space).", "Si Σ|uₙ| converge alors Σuₙ converge et |Σuₙ| ≤ Σ|uₙ| (dans ℝ, ℂ et tout espace normé de dimension finie)."],
    i: ["Cauchy criterion for the partial sums.", "Critère de Cauchy pour les sommes partielles."],
    on: ["an-abs-convergent-series", "an-convergent-series"],
    pr: [[["an absolutely convergent series", "une série absolument convergente"], "an-convergent-series"]], uses: ["cauchy-criterion"] },
  { id: "alternating", topic: "series", kind: "theorem", prepa: "MPSI",
    n: ["Alternating series test", "Critère spécial des séries alternées"],
    s: ["If (uₙ) decreases to 0, then Σ(−1)ⁿuₙ converges, the sum S lies between consecutive partial sums, and the remainder satisfies |Rₙ| ≤ uₙ₊₁.", "Si (uₙ) décroît vers 0, alors Σ(−1)ⁿuₙ converge, sa somme S est comprise entre deux sommes partielles consécutives, et le reste vérifie |Rₙ| ≤ uₙ₊₁."],
    i: ["The even and odd partial sums are adjacent sequences.", "Les sommes partielles paires et impaires sont adjacentes."],
    on: ["an-convergent-series", "an-conditionally-convergent"],
    pr: [[["Σ(−1)ⁿuₙ with uₙ ↓ 0", "Σ(−1)ⁿuₙ avec uₙ ↓ 0"], "an-convergent-series"]], uses: ["adjacent"] },
  { id: "series-comparison", topic: "series", kind: "theorem", prepa: "MPSI",
    n: ["Comparison theorems for series", "Théorèmes de comparaison pour les séries"],
    s: ["For nonnegative terms: uₙ ≤ vₙ and Σvₙ converges ⟹ Σuₙ converges; uₙ ∼ vₙ ⟹ Σuₙ and Σvₙ have the same nature. Riemann series: Σ1/nᵅ converges ⟺ α > 1.", "Pour des termes positifs : uₙ ≤ vₙ et Σvₙ converge ⟹ Σuₙ converge ; uₙ ∼ vₙ ⟹ Σuₙ et Σvₙ sont de même nature. Séries de Riemann : Σ1/nᵅ converge ⟺ α > 1."],
    i: ["Partial sums are increasing, hence bounded ⟺ convergent.", "Les sommes partielles sont croissantes, donc bornées ⟺ convergentes."],
    on: ["an-series", "an-convergent-series"], uses: ["monotone-limit"] },
  { id: "summable-fubini", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Summable families: rearrangement and Fubini", "Familles sommables : sommation par paquets et Fubini"],
    s: ["The sum of a summable family does not depend on the order; it can be computed by packets. For a doubly indexed summable family, Σ_{(i,j)} aᵢⱼ = Σᵢ(Σⱼ aᵢⱼ) = Σⱼ(Σᵢ aᵢⱼ). The Cauchy product of two absolutely convergent series converges to the product of the sums.", "La somme d'une famille sommable ne dépend pas de l'ordre ; on peut sommer par paquets. Pour une famille doublement indexée sommable, Σ_{(i,j)} aᵢⱼ = Σᵢ(Σⱼ aᵢⱼ) = Σⱼ(Σᵢ aᵢⱼ). Le produit de Cauchy de deux séries absolument convergentes converge vers le produit des sommes."],
    i: ["Reduce to nonnegative families, where every order gives the supremum of finite sums.", "Se ramener aux familles positives, où tout ordre donne la borne supérieure des sommes finies."],
    on: ["an-summable-family"], uses: ["abs-conv"] },
  { id: "normal-uniform", topic: "series", kind: "proposition", prepa: "MP",
    n: ["Normal ⟹ uniform ⟹ simple convergence", "Convergence normale ⟹ uniforme ⟹ simple"],
    s: ["If Σ‖fₙ‖∞ < ∞, then Σfₙ converges uniformly (hence simply and absolutely). Uniform convergence implies simple convergence.", "Si Σ‖fₙ‖∞ < ∞, alors Σfₙ converge uniformément (donc simplement et absolument). La convergence uniforme entraîne la convergence simple."],
    i: ["Bound the remainder by the tail of a convergent numerical series.", "Majorer le reste par le reste d'une série numérique convergente."],
    on: ["an-normal-conv", "an-uniform-conv"],
    pr: [[["a normally convergent series of functions", "une série de fonctions normalement convergente"], "an-uniform-conv"]], uses: ["abs-conv"] },
  { id: "uniform-limit", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Uniform limits: continuity and integration", "Limites uniformes : continuité et intégration"],
    s: ["If fₙ → f uniformly and every fₙ is continuous, then f is continuous. If moreover the fₙ are continuous on a segment [a, b], then ∫ₐᵇ fₙ → ∫ₐᵇ f. The same holds for sums of uniformly convergent series (termwise integration).", "Si fₙ → f uniformément et si chaque fₙ est continue, alors f est continue. Si de plus les fₙ sont continues sur un segment [a, b], alors ∫ₐᵇ fₙ → ∫ₐᵇ f. Même résultat pour les sommes de séries uniformément convergentes (intégration terme à terme)."],
    i: ["The ε/3 argument; for integrals, |∫(fₙ − f)| ≤ (b − a)‖fₙ − f‖∞.", "Argument en ε/3 ; pour les intégrales, |∫(fₙ − f)| ≤ (b − a)‖fₙ − f‖∞."],
    on: ["an-uniform-conv"],
    pr: [[["the uniform limit f of continuous functions fₙ", "la limite uniforme f de fonctions continues fₙ"], "an-continuous"]] },
  { id: "termwise-derivation", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Termwise differentiation theorem", "Théorème de dérivation terme à terme"],
    s: ["If the fₙ are C¹ on an interval I, (fₙ) converges simply and (fₙ′) converges uniformly on every segment of I, then f = lim fₙ is C¹ and f′ = lim fₙ′.", "Si les fₙ sont de classe C¹ sur un intervalle I, si (fₙ) converge simplement et (fₙ′) converge uniformément sur tout segment de I, alors f = lim fₙ est de classe C¹ et f′ = lim fₙ′."],
    i: ["Write fₙ(x) = fₙ(a) + ∫ₐˣ fₙ′ and pass to the limit with the integration theorem.", "Écrire fₙ(x) = fₙ(a) + ∫ₐˣ fₙ′ et passer à la limite avec le théorème d'intégration."],
    on: ["an-uniform-conv", "an-c1"],
    pr: [[["f = lim fₙ when (fₙ′) converges uniformly", "f = lim fₙ lorsque (fₙ′) converge uniformément"], "an-c1"]], uses: ["uniform-limit", "ftc"] },
  { id: "dominated-convergence", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Dominated convergence theorem", "Théorème de convergence dominée"],
    s: ["If fₙ → f simply (with f piecewise continuous) and |fₙ| ≤ φ with φ integrable on I, then f is integrable and ∫ fₙ → ∫ f. Series version: if Σ∫|fₙ| < ∞ then ∫ Σfₙ = Σ∫ fₙ.", "Si fₙ → f simplement (f continue par morceaux) et |fₙ| ≤ φ avec φ intégrable sur I, alors f est intégrable et ∫ fₙ → ∫ f. Version séries : si Σ∫|fₙ| < ∞ alors ∫ Σfₙ = Σ∫ fₙ."],
    i: ["Admitted in the programme; the proof uses the Lebesgue integral.", "Admis au programme ; la preuve utilise l'intégrale de Lebesgue."],
    on: ["an-pointwise-conv"] },
  { id: "param-integral", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Integrals depending on a parameter", "Intégrales à paramètre"],
    s: ["If f(x, t) is continuous in x, piecewise continuous in t, and |f(x, t)| ≤ φ(t) with φ integrable, then F(x) = ∫ f(x, t) dt is continuous. If moreover ∂ₓf exists, is continuous in x and dominated, then F is C¹ and F′(x) = ∫ ∂ₓf(x, t) dt (Leibniz rule).", "Si f(x, t) est continue en x, continue par morceaux en t, avec |f(x, t)| ≤ φ(t), φ intégrable, alors F(x) = ∫ f(x, t) dt est continue. Si de plus ∂ₓf existe, est continue en x et dominée, F est de classe C¹ et F′(x) = ∫ ∂ₓf(x, t) dt (règle de Leibniz)."],
    i: ["Dominated convergence applied along sequences xₙ → x.", "Convergence dominée le long de suites xₙ → x."],
    on: ["an-continuous", "an-c1"],
    pr: [[["F(x) = ∫ f(x, t) dt under domination", "F(x) = ∫ f(x, t) dt sous domination"], "an-continuous"]], uses: ["dominated-convergence"] },
  { id: "abel-radius", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Radius of convergence (Abel's lemma)", "Rayon de convergence (lemme d'Abel)"],
    s: ["For a power series Σaₙzⁿ there is R ∈ [0, +∞] such that it converges absolutely for |z| < R and diverges for |z| > R; it converges normally on every disc |z| ≤ r < R.", "Pour une série entière Σaₙzⁿ, il existe R ∈ [0, +∞] tel qu'elle converge absolument pour |z| < R et diverge pour |z| > R ; elle converge normalement sur tout disque |z| ≤ r < R."],
    i: ["If (aₙz₀ⁿ) is bounded, compare with a geometric series for |z| < |z₀|.", "Si (aₙz₀ⁿ) est bornée, comparer à une série géométrique pour |z| < |z₀|."],
    on: ["an-power-series"],
    pr: [[["Σaₙzⁿ on |z| ≤ r < R", "Σaₙzⁿ sur |z| ≤ r < R"], "an-normal-conv"]] },
  { id: "power-series-smooth", topic: "series", kind: "theorem", prepa: "MP",
    n: ["Regularity of the sum of a power series", "Régularité de la somme d'une série entière"],
    s: ["On ]−R, R[ the sum S(x) = Σaₙxⁿ is C∞; it can be differentiated and integrated termwise (same radius), and aₙ = S⁽ⁿ⁾(0)/n!.", "Sur ]−R, R[ la somme S(x) = Σaₙxⁿ est de classe C∞ ; on peut la dériver et l'intégrer terme à terme (même rayon), et aₙ = S⁽ⁿ⁾(0)/n!."],
    i: ["Normal convergence on [−r, r] and the termwise differentiation theorem; the derived series has the same radius.", "Convergence normale sur [−r, r] et théorème de dérivation terme à terme ; la série dérivée a même rayon."],
    on: ["an-power-series", "an-cinf"],
    pr: [[["x ↦ Σaₙxⁿ on ]−R, R[", "x ↦ Σaₙxⁿ sur ]−R, R["], "an-cinf"]], uses: ["abel-radius", "termwise-derivation"] },

  // ===================== differential equations =====================
  { id: "linear-ode-structure", topic: "diffeq", kind: "theorem", prepa: "MPSI",
    n: ["Solutions of linear scalar ODEs", "Solutions des équations différentielles linéaires scalaires"],
    s: ["For y′ + a(x)y = b(x) with a, b continuous on an interval I, every Cauchy problem has a unique solution, defined on I. The homogeneous solutions form a line, and the solutions of the full equation form an affine line y_p + ℝ·e^{−A(x)}. For order 2 with constant coefficients the homogeneous solutions form a plane, described by the roots of the characteristic polynomial.", "Pour y′ + a(x)y = b(x) avec a, b continues sur un intervalle I, tout problème de Cauchy a une unique solution, définie sur I. Les solutions homogènes forment une droite, et celles de l'équation complète une droite affine y_p + ℝ·e^{−A(x)}. À l'ordre 2 à coefficients constants, les solutions homogènes forment un plan, décrit par les racines du polynôme caractéristique."],
    i: ["Variation of the constant for order 1; the characteristic equation for order 2.", "Variation de la constante à l'ordre 1 ; équation caractéristique à l'ordre 2."],
    on: ["an-ode-linear-1st", "an-ode-linear-2nd"],
    pr: [[["the solutions of y′ + a(x)y = 0", "les solutions de y′ + a(x)y = 0"], "vector-space"], [["the solutions of y′ + a(x)y = b(x)", "les solutions de y′ + a(x)y = b(x)"], "affine-space"]], uses: ["ftc"] },
  { id: "cauchy-lipschitz-linear", topic: "diffeq", kind: "theorem", prepa: "MP",
    n: ["Linear Cauchy–Lipschitz theorem", "Théorème de Cauchy–Lipschitz linéaire"],
    s: ["For X′ = A(t)X + B(t) with A, B continuous on an interval I, every Cauchy problem X(t₀) = X₀ has a unique solution, defined on all of I. The homogeneous solutions form a vector space of dimension n, isomorphic to Kⁿ via X ↦ X(t₀).", "Pour X′ = A(t)X + B(t) avec A, B continues sur un intervalle I, tout problème de Cauchy X(t₀) = X₀ admet une unique solution, définie sur tout I. Les solutions homogènes forment un espace vectoriel de dimension n, isomorphe à Kⁿ via X ↦ X(t₀)."],
    i: ["Admitted in general; for constant A the exponential gives it explicitly.", "Admis en général ; pour A constante, l'exponentielle le donne explicitement."],
    on: ["an-ode-system"],
    pr: [[["{X : X′ = A(t)X}", "{X : X′ = A(t)X}"], "vector-space"], [["X ↦ X(t₀) on that space", "X ↦ X(t₀) sur cet espace"], "mo-isomorphism"]] },
  { id: "exp-matrix", topic: "diffeq", kind: "theorem", prepa: "MP",
    n: ["Matrix exponential and constant systems", "Exponentielle de matrice et systèmes à coefficients constants"],
    s: ["For A ∈ Mₙ(K) the series e^A = Σ Aᵏ/k! converges normally, and the solution of X′ = AX, X(0) = X₀ is X(t) = e^{tA}X₀. If A = PDP⁻¹ then e^{tA} = P e^{tD} P⁻¹.", "Pour A ∈ Mₙ(K) la série e^A = Σ Aᵏ/k! converge normalement, et la solution de X′ = AX, X(0) = X₀ est X(t) = e^{tA}X₀. Si A = PDP⁻¹ alors e^{tA} = P e^{tD} P⁻¹."],
    i: ["‖Aᵏ‖ ≤ ‖A‖ᵏ gives normal convergence; differentiate termwise.", "‖Aᵏ‖ ≤ ‖A‖ᵏ donne la convergence normale ; dériver terme à terme."],
    on: ["an-ode-system", "matrix-ring", "mx-diagonalizable"], uses: ["diag-criteria", "termwise-derivation"] },

  // ===================== probability =====================
  { id: "total-probability", topic: "proba", kind: "theorem", prepa: "MPSI",
    n: ["Law of total probability", "Formule des probabilités totales"],
    s: ["If (Aᵢ) is a complete system of events (finite or countable), then P(B) = Σᵢ P(B ∩ Aᵢ) = Σᵢ P(B | Aᵢ) P(Aᵢ).", "Si (Aᵢ) est un système complet d'événements (fini ou dénombrable), alors P(B) = Σᵢ P(B ∩ Aᵢ) = Σᵢ P(B | Aᵢ) P(Aᵢ)."],
    i: ["B is the disjoint union of the B ∩ Aᵢ; use additivity.", "B est la réunion disjointe des B ∩ Aᵢ ; additivité."],
    on: ["pr-complete-system", "probability-space"] },
  { id: "bayes", topic: "proba", kind: "theorem", prepa: "MPSI",
    n: ["Bayes' formula", "Formule de Bayes"],
    s: ["If P(A) > 0 and P(B) > 0, then P(A | B) = P(B | A) P(A) / P(B). With a complete system (Aⱼ): P(Aᵢ | B) = P(B | Aᵢ) P(Aᵢ) / Σⱼ P(B | Aⱼ) P(Aⱼ).", "Si P(A) > 0 et P(B) > 0, alors P(A | B) = P(B | A) P(A) / P(B). Avec un système complet (Aⱼ) : P(Aᵢ | B) = P(B | Aᵢ) P(Aᵢ) / Σⱼ P(B | Aⱼ) P(Aⱼ)."],
    i: ["P(A ∩ B) computed two ways, then the law of total probability for the denominator.", "P(A ∩ B) calculé de deux façons, puis les probabilités totales pour le dénominateur."],
    on: ["pr-complete-system"], uses: ["total-probability"] },
  { id: "continuity-probability", topic: "proba", kind: "theorem", prepa: "MP",
    n: ["Continuity of probability", "Continuité monotone d'une probabilité"],
    s: ["If (Aₙ) is increasing, P(⋃ₙ Aₙ) = lim P(Aₙ); if it is decreasing, P(⋂ₙ Aₙ) = lim P(Aₙ). Consequently P(⋃ₙ Aₙ) ≤ Σₙ P(Aₙ) (σ-subadditivity).", "Si (Aₙ) est croissante, P(⋃ₙ Aₙ) = lim P(Aₙ) ; si elle est décroissante, P(⋂ₙ Aₙ) = lim P(Aₙ). Par suite P(⋃ₙ Aₙ) ≤ Σₙ P(Aₙ) (sous-additivité)."],
    i: ["Write the union as a disjoint union of the increments Aₙ∖Aₙ₋₁ and use σ-additivity.", "Écrire la réunion comme réunion disjointe des Aₙ∖Aₙ₋₁ et utiliser la σ-additivité."],
    on: ["probability-space"] },
  { id: "linearity-expectation", topic: "proba", kind: "theorem", prepa: "MPSI",
    n: ["Linearity of expectation", "Linéarité de l'espérance"],
    s: ["E(aX + bY) = aE(X) + bE(Y) whenever X and Y have finite expectation; E(X) ≥ 0 if X ≥ 0. So the random variables with finite expectation form a vector space on which E is a positive linear form.", "E(aX + bY) = aE(X) + bE(Y) dès que X et Y sont d'espérance finie ; E(X) ≥ 0 si X ≥ 0. Les variables aléatoires d'espérance finie forment donc un espace vectoriel sur lequel E est une forme linéaire positive."],
    i: ["Summation of families: linearity of sums of absolutely convergent series.", "Sommation de familles : linéarité des sommes de séries absolument convergentes."],
    on: ["pr-random-variable", "pr-discrete-rv"],
    pr: [[["{X : E(|X|) < ∞}", "{X : E(|X|) < ∞}"], "vector-space"]], uses: ["summable-fubini"] },
  { id: "koenig-huygens", topic: "proba", kind: "theorem", prepa: "MPSI",
    n: ["König–Huygens formula", "Formule de König–Huygens"],
    s: ["Var(X) = E(X²) − E(X)², and Var(aX + b) = a² Var(X).", "Var(X) = E(X²) − E(X)², et Var(aX + b) = a² Var(X)."],
    i: ["Expand E((X − E X)²) using linearity.", "Développer E((X − E X)²) par linéarité."],
    on: ["pr-discrete-rv"], uses: ["linearity-expectation"] },
  { id: "independence-expectation", topic: "proba", kind: "theorem", prepa: "MPSI",
    n: ["Independence and expectation", "Indépendance et espérance"],
    s: ["If X, Y are independent with finite expectation, E(XY) = E(X) E(Y). With finite second moments, Cov(X, Y) = 0 and Var(X + Y) = Var X + Var Y (Bienaymé). The converse is false: uncorrelated does not imply independent.", "Si X, Y sont indépendantes d'espérance finie, E(XY) = E(X) E(Y). Avec des moments d'ordre 2 finis, Cov(X, Y) = 0 et Var(X + Y) = Var X + Var Y (Bienaymé). La réciproque est fausse : non corrélées n'entraîne pas indépendantes."],
    i: ["Factor the joint law and sum over the product of supports.", "Factoriser la loi conjointe et sommer sur le produit des supports."],
    on: ["pr-independence", "pr-discrete-rv"], uses: ["linearity-expectation"] },
  { id: "markov-chebyshev", topic: "proba", kind: "inequality", prepa: "MPSI",
    n: ["Markov and Bienaymé–Chebyshev inequalities", "Inégalités de Markov et de Bienaymé–Tchebychev"],
    s: ["Markov: X ≥ 0 and a > 0 ⟹ P(X ≥ a) ≤ E(X)/a. Bienaymé–Chebyshev: P(|X − E(X)| ≥ ε) ≤ Var(X)/ε² for ε > 0.", "Markov : X ≥ 0 et a > 0 ⟹ P(X ≥ a) ≤ E(X)/a. Bienaymé–Tchebychev : P(|X − E(X)| ≥ ε) ≤ Var(X)/ε² pour ε > 0."],
    i: ["a · 1_{X ≥ a} ≤ X, take expectations; Chebyshev is Markov applied to (X − E X)².", "a · 1_{X ≥ a} ≤ X, prendre l'espérance ; Tchebychev est Markov appliqué à (X − E X)²."],
    on: ["pr-random-variable"], uses: ["linearity-expectation"] },
  { id: "weak-lln", topic: "proba", kind: "theorem", prepa: "MP",
    n: ["Weak law of large numbers", "Loi faible des grands nombres"],
    s: ["If X₁, X₂, … are pairwise independent with the same mean m and variance σ², then for every ε > 0, P(|(X₁ + ⋯ + Xₙ)/n − m| ≥ ε) ≤ σ²/(nε²) → 0.", "Si X₁, X₂, … sont deux à deux indépendantes, de même espérance m et même variance σ², alors pour tout ε > 0, P(|(X₁ + ⋯ + Xₙ)/n − m| ≥ ε) ≤ σ²/(nε²) → 0."],
    i: ["Bienaymé gives the variance σ²/n of the mean; apply Chebyshev.", "Bienaymé donne la variance σ²/n de la moyenne ; appliquer Tchebychev."],
    on: ["pr-random-vector", "pr-independence"], uses: ["markov-chebyshev", "independence-expectation"] },
  { id: "binomial-sum", topic: "proba", kind: "proposition", prepa: "MPSI",
    n: ["Sum of independent Bernoulli variables", "Somme de variables de Bernoulli indépendantes"],
    s: ["If X₁, …, Xₙ are independent Bernoulli(p) variables, then X₁ + ⋯ + Xₙ follows the binomial law B(n, p); its expectation is np and its variance np(1 − p).", "Si X₁, …, Xₙ sont des variables de Bernoulli(p) indépendantes, alors X₁ + ⋯ + Xₙ suit la loi binomiale B(n, p) ; son espérance est np et sa variance np(1 − p)."],
    i: ["Count the k-subsets of successes: C(n, k) pᵏ(1 − p)ⁿ⁻ᵏ.", "Dénombrer les k-parties de succès : C(n, k) pᵏ(1 − p)ⁿ⁻ᵏ."],
    on: ["pr-bernoulli", "pr-binomial"],
    pr: [[["X₁ + ⋯ + Xₙ, Xᵢ independent Bernoulli(p)", "X₁ + ⋯ + Xₙ, Xᵢ de Bernoulli(p) indépendantes"], "pr-binomial"]], uses: ["counting"] },
  { id: "poisson-sum", topic: "proba", kind: "proposition", prepa: "MP",
    n: ["Sum of independent Poisson variables", "Somme de variables de Poisson indépendantes"],
    s: ["If X ∼ 𝒫(λ) and Y ∼ 𝒫(μ) are independent, then X + Y ∼ 𝒫(λ + μ).", "Si X ∼ 𝒫(λ) et Y ∼ 𝒫(μ) sont indépendantes, alors X + Y ∼ 𝒫(λ + μ)."],
    i: ["Compute the convolution with the binomial theorem, or multiply the generating functions.", "Calculer la convolution avec la formule du binôme, ou multiplier les fonctions génératrices."],
    on: ["pr-poisson"],
    pr: [[["X + Y with X ∼ 𝒫(λ), Y ∼ 𝒫(μ) independent", "X + Y avec X ∼ 𝒫(λ), Y ∼ 𝒫(μ) indépendantes"], "pr-poisson"]], uses: ["binomial", "generating-function"] },
  { id: "generating-function", topic: "proba", kind: "theorem", prepa: "MP",
    n: ["Generating functions", "Fonctions génératrices"],
    s: ["For X with values in ℕ, G_X(t) = E(tˣ) = Σ P(X = n) tⁿ has radius ≥ 1 and determines the law of X; G_{X+Y} = G_X G_Y for independent X, Y; X has finite expectation ⟺ G_X is differentiable at 1, and then E(X) = G_X′(1).", "Pour X à valeurs dans ℕ, G_X(t) = E(tˣ) = Σ P(X = n) tⁿ a un rayon ≥ 1 et caractérise la loi de X ; G_{X+Y} = G_X G_Y pour X, Y indépendantes ; X est d'espérance finie ⟺ G_X est dérivable en 1, et alors E(X) = G_X′(1)."],
    i: ["Uniqueness of power series coefficients; the product of series is the Cauchy product.", "Unicité des coefficients d'une série entière ; le produit de séries est le produit de Cauchy."],
    on: ["pr-discrete-rv", "an-power-series"], uses: ["power-series-smooth", "summable-fubini"] },

  // ===================== sets & counting =====================
  { id: "equiv-partition", topic: "comb", kind: "theorem", prepa: "MPSI",
    n: ["Equivalence relations and partitions", "Relations d'équivalence et partitions"],
    s: ["The equivalence classes of an equivalence relation on E form a partition of E; conversely every partition of E defines an equivalence relation (being in the same block).", "Les classes d'équivalence d'une relation d'équivalence sur E forment une partition de E ; réciproquement toute partition de E définit une relation d'équivalence (être dans le même bloc)."],
    i: ["Two classes are equal or disjoint, by transitivity.", "Deux classes sont égales ou disjointes, par transitivité."],
    on: ["equivalence-relation", "quotient-set"] },
  { id: "well-ordering", topic: "comb", kind: "theorem", prepa: "MPSI",
    n: ["ℕ is well ordered (induction)", "ℕ est bien ordonné (récurrence)"],
    s: ["Every nonempty subset of ℕ has a least element; equivalently, simple and strong induction hold.", "Toute partie non vide de ℕ admet un plus petit élément ; de façon équivalente, la récurrence simple et forte est valide."],
    i: ["Take a minimal counterexample.", "Prendre un contre-exemple minimal."],
    on: ["well-order", "nu-N"],
    pr: [[["(ℕ, ≤)", "(ℕ, ≤)"], "well-order"]] },
  { id: "counting", topic: "comb", kind: "theorem", prepa: "MPSI",
    n: ["Counting formulas", "Formules de dénombrement"],
    s: ["For finite sets with |E| = n and |F| = p: |E × F| = np, |F^E| = pⁿ, the number of injections E → F is p!/(p − n)!, the number of bijections of E is n!, and the number of k-subsets of E is C(n, k) = n!/(k!(n − k)!). Pascal: C(n, k) = C(n−1, k−1) + C(n−1, k).", "Pour des ensembles finis avec |E| = n et |F| = p : |E × F| = np, |F^E| = pⁿ, le nombre d'injections E → F est p!/(p − n)!, le nombre de bijections de E est n!, et le nombre de parties à k éléments de E est C(n, k) = n!/(k!(n − k)!). Pascal : C(n, k) = C(n−1, k−1) + C(n−1, k)."],
    i: ["Bijections between the sets counted, and induction.", "Bijections entre les ensembles dénombrés, et récurrence."],
    on: ["nu-finite-set", "nu-permutation", "nu-arrangement", "nu-combination", "nu-binomial-coeff"] },
  { id: "binomial", topic: "comb", kind: "theorem", prepa: "MPSI",
    n: ["Binomial theorem", "Formule du binôme de Newton"],
    s: ["If a and b commute in a ring A, then (a + b)ⁿ = Σₖ C(n, k) aᵏ bⁿ⁻ᵏ.", "Si a et b commutent dans un anneau A, alors (a + b)ⁿ = Σₖ C(n, k) aᵏ bⁿ⁻ᵏ."],
    i: ["Induction with Pascal's rule, or count the ways to choose k factors a among n.", "Récurrence avec la formule de Pascal, ou dénombrer les choix de k facteurs a parmi n."],
    on: ["nu-binomial-coeff", "comm-ring", "ring"], uses: ["counting"] },
  { id: "countability", topic: "comb", kind: "theorem", prepa: "MP",
    n: ["Countability of ℕ², ℚ and non-countability of ℝ", "Dénombrabilité de ℕ², ℚ et non-dénombrabilité de ℝ"],
    s: ["ℕ × ℕ and ℚ are countable; a countable union of countable sets is countable; ℝ is not countable (Cantor's diagonal argument).", "ℕ × ℕ et ℚ sont dénombrables ; une réunion dénombrable d'ensembles dénombrables est dénombrable ; ℝ n'est pas dénombrable (argument diagonal de Cantor)."],
    i: ["(p, q) ↦ 2ᵖ3^q is injective into ℕ; for ℝ, build a number differing from the n-th listed one in its n-th decimal.", "(p, q) ↦ 2ᵖ3^q est injective dans ℕ ; pour ℝ, construire un réel qui diffère du n-ième listé par sa n-ième décimale."],
    on: ["nu-countable", "nu-countably-infinite", "nu-uncountable"],
    pr: [[["ℚ", "ℚ"], "nu-countable"]] },
];


// ---- indices over the theorem database ----
const NODE_LOC = {}; // node id -> tree key
DOMAINS.forEach((d) => d.nodes.forEach((n) => (NODE_LOC[n.id] = d.key)));
const nodeObj = (id) => domainByKey[NODE_LOC[id]].byId[id];
const THM_BY_ID = Object.fromEntries(THEOREMS.map((t) => [t.id, t]));
const thmOnIds = (t) => t.on.map((e) => (typeof e === "string" ? e : e[0]));
const THM_ON = {}; // node id -> theorems that hold on it
const THM_PROVES = {}; // node id -> theorems that prove something IS this structure
const THM_USED_BY = {}; // theorem id -> theorems relying on it
THEOREMS.forEach((t) => {
  thmOnIds(t).forEach((id) => {
    THM_ON[id] = THM_ON[id] || [];
    if (!THM_ON[id].includes(t.id)) THM_ON[id].push(t.id);
  });
  (t.pr || []).forEach(([, is]) => {
    THM_PROVES[is] = THM_PROVES[is] || [];
    if (!THM_PROVES[is].includes(t.id)) THM_PROVES[is].push(t.id);
  });
  (t.uses || []).forEach((u) => (THM_USED_BY[u] = THM_USED_BY[u] || []).push(t.id));
});
// A theorem proved for a structure also holds for its specializations — but only where the tree is a hierarchy
// (not for ℕ ⊂ ℤ ⊂ ℚ …, which are embeddings).
const THM_INHERIT = { algebra: true, analysis: true, matrices: true, probability: true, morphisms: true, numbers: false };
const foldText = (s) => s.normalize("NFD").replace(/[\u0300-\u036f]/g, "").toLowerCase(); // "Bézout" ~ "bezout"
// text searched in the theorem list: names and statements in both languages + names of the linked structures
const THM_HAY = Object.fromEntries(
  THEOREMS.map((t) => {
    const linked = [...thmOnIds(t), ...(t.pr || []).map(([, is]) => is)].map((id) => nodeObj(id).name + " " + (FR_NODES[id] ? FR_NODES[id][0] : ""));
    return [t.id, foldText([t.n[0], t.n[1], t.s[0], t.s[1], ...linked].join(" "))];
  })
);

// ---------------------------------------------------------------------------
// Language: remembered in localStorage once the user picks one; before that, inferred from the browser.
// Storage can throw (private mode, sandboxed iframes, quota) — every access is guarded and falls back to memory.
// ---------------------------------------------------------------------------
const LANG_KEY = "mathmap.lang";
const LANGS = ["en", "fr"];
function readStoredLang() {
  try {
    const v = window.localStorage.getItem(LANG_KEY);
    return LANGS.includes(v) ? v : null;
  } catch (e) {
    return null;
  }
}
function writeStoredLang(v) {
  try {
    window.localStorage.setItem(LANG_KEY, v);
  } catch (e) {
    /* storage unavailable: the choice simply lasts for this session */
  }
}
// first supported language in the browser's preference order ("de-DE", "fr" → "fr"); English if none
function browserLang() {
  if (typeof navigator === "undefined") return "en";
  const prefs = navigator.languages && navigator.languages.length ? navigator.languages : [navigator.language || ""];
  for (const l of prefs) {
    const base = String(l).toLowerCase().split("-")[0];
    if (LANGS.includes(base)) return base;
  }
  return "en";
}
function detectInitialLang() {
  if (typeof window === "undefined") return "en";
  return readStoredLang() || browserLang();
}

const DEFAULT_SELECTION = {
  algebra: "comm-ring",
  analysis: "an-continuous",
  numbers: "nu-Z",
  matrices: "mx-square-matrix",
  probability: "pr-random-variable",
  morphisms: "mo-morphism",
};

export default function MathMap() {
  const [lang, setLang] = useState(detectInitialLang);
  // only an explicit choice is saved (the inferred default is not), so an unset user keeps following the browser
  const chooseLang = (code) => {
    setLang(code);
    writeStoredLang(code);
  };
  // keep several open tabs in step
  useEffect(() => {
    const onStorage = (e) => {
      if (e.key === LANG_KEY && LANGS.includes(e.newValue)) setLang(e.newValue);
    };
    window.addEventListener("storage", onStorage);
    return () => window.removeEventListener("storage", onStorage);
  }, []);
  const t = UI[lang];
  const isMobile = useIsMobile();
  const [panelOpen, setPanelOpen] = useState(false); // mobile only: full-screen info panel
  const panelRef = useRef(null);
  const searchRef = useRef(null);
  const panelOpenerRef = useRef(null);
  const wasPanelOpenRef = useRef(false);
  const closePanel = useCallback(() => setPanelOpen(false), []);

  const [axOpen, setAxOpen] = useState(false); // folded "complete axioms" section

  // leaving the mobile layout (rotate / resize) closes the overlay
  useEffect(() => {
    if (!isMobile) setPanelOpen(false);
  }, [isMobile]);
  useEffect(() => {
    if (!isMobile || !panelOpen) {
      if (wasPanelOpenRef.current) {
        wasPanelOpenRef.current = false;
        const opener = panelOpenerRef.current;
        if (opener?.isConnected) opener.focus?.();
        else searchRef.current?.focus?.();
        panelOpenerRef.current = null;
      }
      return;
    }
    const justOpened = !wasPanelOpenRef.current;
    wasPanelOpenRef.current = true;
    const panel = panelRef.current;
    const focusable = () => Array.from(panel?.querySelectorAll('button:not([disabled]), a[href], input:not([disabled]), select:not([disabled]), textarea:not([disabled]), summary, [contenteditable="true"], [tabindex]:not([tabindex="-1"])') || []).filter((el) => (el.tagName === "SUMMARY" || !el.closest("details:not([open])")) && !el.closest("[hidden]") && el.getClientRects().length > 0);
    if (justOpened) focusable()[0]?.focus();
    const onKey = (e) => {
      if (e.key === "Escape") {
        e.preventDefault();
        closePanel();
      } else if (e.key === "Tab") {
        const items = Array.from(focusable());
        if (!items.length) { e.preventDefault(); panel?.focus(); return; }
        const firstItem = items[0];
        const lastItem = items[items.length - 1];
        if (e.shiftKey && (document.activeElement === firstItem || !panel.contains(document.activeElement))) {
          e.preventDefault(); lastItem.focus();
        } else if (!e.shiftKey && (document.activeElement === lastItem || !panel.contains(document.activeElement))) {
          e.preventDefault(); firstItem.focus();
        }
      }
    };
    document.addEventListener("keydown", onKey);
    return () => document.removeEventListener("keydown", onKey);
  }, [isMobile, panelOpen, closePanel]);
  const [activeDomainKey, setActiveDomainKey] = useState("algebra");
  const domain = domainByKey[activeDomainKey];
  const [selected, setSelected] = useState(DEFAULT_SELECTION[activeDomainKey]);
  const [hoveredBranch, setHoveredBranch] = useState(null);
  const [search, setSearch] = useState("");
  const [programmeOnly, setProgrammeOnly] = useState(false);
  const [view, setView] = useState("tree"); // "tree" | "theorems"
  const [selThm, setSelThm] = useState(THEOREMS[0].id);
  const [thmTopic, setThmTopic] = useState("");
  const [thmSecOpen, setThmSecOpen] = useState(false); // folded "Theorems" section of the node pane
  const [focusId, setFocusId] = useState(null); // node to scroll into view after a jump
  const [dims, setDims] = useState({ w: 1600, h: 1200 });

  // ---- zoom ----
  const [scale, setScale] = useState(1);
  const scaleRef = useRef(1);
  scaleRef.current = scale;
  const paneRef = useRef(null);
  const anchorRef = useRef(null); // content point that must stay under a given pane point

  // Zoom by `factor`, keeping the content under `focal` (client coords) fixed; default = pane centre.
  const zoomBy = useCallback((factor, focal) => {
    const el = paneRef.current;
    const next = clampZoom(scaleRef.current * factor);
    if (!el || next === scaleRef.current) return;
    const rect = el.getBoundingClientRect();
    const px = focal ? focal.x - rect.left : el.clientWidth / 2;
    const py = focal ? focal.y - rect.top : el.clientHeight / 2;
    anchorRef.current = {
      x0: (el.scrollLeft + px - PAD_L) / scaleRef.current,
      y0: (el.scrollTop + py - PAD_T) / scaleRef.current,
      px,
      py,
    };
    setScale(next);
  }, []);

  // after the SVG has been resized, re-scroll so the anchor point did not move on screen
  useLayoutEffect(() => {
    const a = anchorRef.current;
    const el = paneRef.current;
    if (!a || !el) return;
    el.scrollLeft = PAD_L + a.x0 * scale - a.px;
    el.scrollTop = PAD_T + a.y0 * scale - a.py;
    anchorRef.current = null;
  }, [scale]);

  // Ctrl/⌘ + wheel (this is also how trackpad pinch arrives) and the +, -, 0 keys.
  // Native listener: React's onWheel is passive, so it cannot preventDefault the page zoom.
  useEffect(() => {
    const el = paneRef.current;
    if (!el) return;
    const onWheel = (e) => {
      if (!(e.ctrlKey || e.metaKey)) return; // plain scroll stays plain scroll
      e.preventDefault();
      const d = Math.max(-60, Math.min(60, e.deltaY));
      zoomBy(Math.exp(-d * 0.005), { x: e.clientX, y: e.clientY });
    };
    const onKey = (e) => {
      if (e.ctrlKey || e.metaKey || e.altKey) return;
      const tag = (e.target && e.target.tagName) || "";
      if (tag === "INPUT" || tag === "TEXTAREA" || (e.target && e.target.isContentEditable)) return;
      if (e.key === "+" || e.key === "=") zoomBy(1.2);
      else if (e.key === "-" || e.key === "_") zoomBy(1 / 1.2);
      else if (e.key === "0") zoomBy(1 / scaleRef.current);
    };
    el.addEventListener("wheel", onWheel, { passive: false });
    window.addEventListener("keydown", onKey);
    return () => {
      el.removeEventListener("wheel", onWheel);
      window.removeEventListener("keydown", onKey);
    };
  }, [zoomBy, view]);

  // Two-finger pinch on touch screens (one finger keeps scrolling natively via touch-action: pan-x pan-y).
  useEffect(() => {
    const el = paneRef.current;
    if (!el) return;
    let start = null;
    const dist = (t) => Math.hypot(t[0].clientX - t[1].clientX, t[0].clientY - t[1].clientY);
    const mid = (t) => ({ x: (t[0].clientX + t[1].clientX) / 2, y: (t[0].clientY + t[1].clientY) / 2 });
    const onStart = (e) => {
      start = e.touches.length === 2 ? { d: dist(e.touches), s: scaleRef.current } : null;
    };
    const onMove = (e) => {
      if (!start || e.touches.length !== 2) return;
      if (e.cancelable) e.preventDefault();
      const target = clampZoom((start.s * dist(e.touches)) / start.d);
      zoomBy(target / scaleRef.current, mid(e.touches));
    };
    const onEnd = (e) => {
      if (e.touches.length < 2) start = null;
    };
    el.addEventListener("touchstart", onStart, { passive: true });
    el.addEventListener("touchmove", onMove, { passive: false });
    el.addEventListener("touchend", onEnd);
    el.addEventListener("touchcancel", onEnd);
    return () => {
      el.removeEventListener("touchstart", onStart);
      el.removeEventListener("touchmove", onMove);
      el.removeEventListener("touchend", onEnd);
      el.removeEventListener("touchcancel", onEnd);
    };
  }, [zoomBy, view]);

  function fitToView() {
    const el = paneRef.current;
    if (!el) return;
    const s = clampZoom(Math.min((el.clientWidth - PAD_L - PAD_R) / dims.w, (el.clientHeight - PAD_T - PAD_B) / dims.h, 1));
    anchorRef.current = null;
    setScale(s);
    requestAnimationFrame(() => {
      el.scrollLeft = 0;
      el.scrollTop = 0;
    });
  }

  const { nodes, byId, branches: BRANCHES } = domain;
  const fr = lang === "fr";
  // --- translation helpers (layout never depends on language) ---
  const nodeName = (n) => (fr && FR_NODES[n.id] && FR_NODES[n.id][0]) || n.name;
  const nodeBlurb = (n) => (fr && FR_NODES[n.id] && FR_NODES[n.id][1]) || n.blurb;
  const nodeDelta = (n) => (fr && FR_NODES[n.id] && FR_NODES[n.id][2]) || n.delta;
  // subtitle = the "other" language: French term in EN mode, English name in FR mode
  const nodeSub = (n) => (fr ? n.name : n.fr && n.fr.replace(/\s*\(approfondi en MP\*\)|\s*\(MP\*\)/g, ""));
  const domLabel = (d) => (fr ? FR_DOMAINS[d.key].label : d.label);
  const branchLabel = (b) => (fr ? FR_BRANCHES[activeDomainKey][b] : BRANCHES[b].label);
  const upLabel = fr ? FR_DOMAINS[activeDomainKey].up : domain.upLabel;
  const downLabel = fr ? FR_DOMAINS[activeDomainKey].down : domain.downLabel;
  const branchOrder = Object.keys(BRANCHES);
  const colWidth = 196;
  const rowHeight = 54;
  const leftPad = 236;
  const topPad = 70;

  const depthMemo = useMemo(() => computeDepths(byId, nodes), [byId, nodes]);

  const byBranch = useMemo(() => {
    const m = {};
    branchOrder.forEach((b) => (m[b] = []));
    nodes.forEach((n) => m[n.branch] && m[n.branch].push(n));
    return m;
  }, [nodes]);

  const positions = useMemo(() => {
    const pos = {};
    let yCursor = topPad;
    const rankOf = Object.fromEntries(branchOrder.map((b, i) => [b, i]));
    branchOrder.forEach((b, rank) => {
      const nodesInBranch = byBranch[b];
      if (!nodesInBranch || !nodesInBranch.length) return;
      const { rowOf, rows } = layoutBranchRows(nodesInBranch, nodes, byId, depthMemo, rankOf, rank, colWidth, rowHeight);
      nodesInBranch.forEach((n) => {
        pos[n.id] = { x: leftPad + depthMemo[n.id] * colWidth, y: yCursor + rowOf[n.id] * rowHeight };
      });
      yCursor += rows * rowHeight + 56;
    });
    return pos;
  }, [byBranch, byId, depthMemo, nodes]);

  useEffect(() => {
    const depthVals = Object.values(depthMemo);
    const maxDepth = depthVals.length ? Math.max(...depthVals) : 0;
    const posVals = Object.values(positions);
    const maxX = leftPad + (maxDepth + 1) * colWidth + 40;
    const maxY = (posVals.length ? Math.max(...posVals.map((p) => p.y)) : topPad) + 100;
    setDims({ w: maxX, h: maxY });
  }, [positions, depthMemo]);

  function switchDomain(key, selectId) {
    setActiveDomainKey(key);
    setSelected(selectId || DEFAULT_SELECTION[key]);
    setSearch("");
    setHoveredBranch(null);
    if (selectId) setFocusId(selectId);
  }
  function openNode(domainKey, id) {
    setView("tree");
    switchDomain(domainKey, id);
  }
  function openTheorem(id) {
    setSelThm(id);
    setView("theorems");
    setSearch("");
    setHoveredBranch(null);
  }
  function pickTheorem(id) {
    setSelThm(id);
    if (isMobile) setPanelOpen(true);
  }

  // after a jump, bring the target node to the middle of the graph pane
  useLayoutEffect(() => {
    if (!focusId || view !== "tree") return;
    const el = paneRef.current;
    const p = positions[focusId];
    if (!el || !p) return;
    el.scrollLeft = Math.max(0, PAD_L + p.x * scale - el.clientWidth / 2);
    el.scrollTop = Math.max(0, PAD_T + p.y * scale - el.clientHeight / 2);
    setFocusId(null);
  }, [focusId, view, positions, activeDomainKey, scale]);

  const ancestors = useMemo(() => getAncestors(byId, selected), [byId, selected]);
  const descendants = useMemo(() => getDescendants(nodes, selected), [nodes, selected]);
  const selNode = byId[selected];

  const searchMatch = foldText(search.trim());
  const matchedIds = useMemo(() => {
    if (!searchMatch) return null;
    return new Set(
      nodes
        .filter((n) => {
          const frName = FR_NODES[n.id] ? foldText(FR_NODES[n.id][0]) : "";
          const frTerm = n.fr && nodeSub(n);
          return foldText(n.name).includes(searchMatch) || frName.includes(searchMatch) || (frTerm && foldText(frTerm).includes(searchMatch));
        })
        .map((n) => n.id)
    );
  }, [searchMatch, nodes]);

  function isDimmed(id) {
    if (matchedIds) return !matchedIds.has(id);
    if (fr && programmeOnly && !byId[id].prepa) return true;
    if (hoveredBranch) return byId[id].branch !== hoveredBranch;
    return false;
  }
  function isHighlighted(id) {
    return id === selected || ancestors.has(id) || descendants.has(id);
  }

  // =========================== theorem database UI ===========================
  const SERIF = "'Iowan Old Style','Georgia',serif";
  const MONO = "'JetBrains Mono', monospace";
  const L = lang === "fr" ? 1 : 0;
  const thmName = (th) => th.n[L];

  // clickable chip pointing at a node of one of the trees
  const nodeChip = (id, cond) => {
    const n = nodeObj(id);
    const dom = domainByKey[NODE_LOC[id]];
    const color = dom.branches[n.branch].color;
    return (
      <button
        key={id + (cond ? cond[0] : "")}
        data-node={id}
        onClick={() => openNode(NODE_LOC[id], id)}
        title={`${t.openInTree} — ${domLabel(dom)}`}
        style={{ fontFamily: SERIF, fontSize: 13, padding: "4px 9px", border: `1px solid ${color}`, borderRadius: 4, background: "#fff", color: "#2a2a26", cursor: "pointer", textAlign: "left" }}
      >
        <span style={{ color, fontWeight: 700 }}>●</span> {nodeName(n)}
        {cond ? <span style={{ color: "#8a8578", fontStyle: "italic" }}> ({cond[L]})</span> : null} ↗
      </button>
    );
  };
  const thmRow = (tid, extra) => {
    const th = THM_BY_ID[tid];
    return (
      <button
        type="button"
        key={tid}
        data-thm-link={tid}
        onClick={() => openTheorem(tid)}
        style={{ width: "100%", textAlign: "left", font: "inherit", color: "inherit", background: "transparent", border: 0, cursor: "pointer", padding: "6px 0", borderTop: "1px solid #f0ebdd", display: "flex", gap: 8, alignItems: "baseline", appearance: "none" }}
      >
        {fr && <span style={{ width: 8, height: 8, borderRadius: "50%", flexShrink: 0, background: th.prepa ? PREPA_COLORS[th.prepa] : "#d8d2c2" }} />}
        <span style={{ fontSize: 13.5, fontWeight: 600, color: THM_TOPICS[th.topic].color }}>{thmName(th)}</span>
        {extra ? <span style={{ fontSize: 11.5, fontFamily: MONO, color: "#8a8578" }}>{extra}</span> : null}
      </button>
    );
  };

  // ---- the "Theorems" section of a node's info pane ----
  const nodeThmSection = (() => {
    if (!selNode) return null;
    const direct = THM_ON[selNode.id] || [];
    const proves = THM_PROVES[selNode.id] || [];
    const inherited = [];
    if (THM_INHERIT[activeDomainKey]) {
      const seen = new Set(direct);
      [...ancestors]
        .sort((a, b) => depthMemo[b] - depthMemo[a]) // closest ancestor first
        .forEach((a) => (THM_ON[a] || []).forEach((tid) => { if (!seen.has(tid)) { seen.add(tid); inherited.push({ tid, from: a }); } }));
    }
    const total = new Set([...direct, ...proves, ...inherited.map((x) => x.tid)]).size;
    if (!total) return null;
    const group = (title, items) =>
      items.length ? (
        <div style={{ padding: "2px 14px 8px" }}>
          <div style={{ fontFamily: MONO, fontSize: 11, color: "#8a8578", margin: "8px 0 2px" }}>{title} ({items.length})</div>
          {items}
        </div>
      ) : null;
    return (
      <details
        data-section="theorems"
        open={thmSecOpen}
        onToggle={(e) => setThmSecOpen(e.currentTarget.open)}
        style={{ marginBottom: 16, border: "1px solid #d8d2c2", borderRadius: 4, background: "#fff" }}
      >
        <summary style={{ cursor: "pointer", padding: "9px 12px", fontFamily: MONO, fontSize: 12, fontWeight: 600, color: "#4a4638", userSelect: "none" }}>
          {t.theorems} ({total})
        </summary>
        {group(t.thmOnThis, direct.map((tid) => thmRow(tid)))}
        {group(t.thmProvesThis, proves.map((tid) => thmRow(tid)))}
        {group(t.thmInherited, inherited.map(({ tid, from }) => thmRow(tid, `${t.thmVia} ${nodeName(byId[from])}`)))}
      </details>
    );
  })();

  // ---- theorem detail (right pane / full-screen panel on phones) ----
  const thmDetail = (() => {
    const th = THM_BY_ID[selThm];
    if (!th) return null;
    const tp = THM_TOPICS[th.topic];
    const label = (txt) => <div style={{ fontFamily: MONO, fontSize: 11, color: "#8a8578", margin: "16px 0 6px" }}>{txt}</div>;
    const uses = th.uses || [];
    const usedBy = THM_USED_BY[th.id] || [];
    return (
      <>
        <div style={{ display: "flex", gap: 8, marginBottom: 10, flexWrap: "wrap" }}>
          <div style={{ fontSize: 11, fontFamily: MONO, color: tp.color, border: `1px solid ${tp.color}`, borderRadius: 3, padding: "2px 7px" }}>{tp[lang]}</div>
          <div style={{ fontSize: 11, fontFamily: MONO, color: "#4a4638", border: "1px solid #c9c2ae", borderRadius: 3, padding: "2px 7px" }}>{THM_KINDS[th.kind][lang]}</div>
          {fr && th.prepa && (
            <div style={{ fontSize: 11, fontFamily: MONO, color: "#fff", background: PREPA_COLORS[th.prepa], borderRadius: 3, padding: "2px 7px" }}>{th.prepa === "MPSI" ? t.mpsi : t.mp}</div>
          )}
        </div>
        <h2 style={{ margin: "0 0 2px", fontSize: 20 }}>{th.n[L]}</h2>
        <div style={{ fontSize: 13.5, fontStyle: "italic", color: "#8a8578", marginBottom: 12 }}>{th.n[1 - L]}</div>
        <div data-field="statement" style={{ fontSize: 14.5, lineHeight: 1.6, color: "#2a2a26", background: "#fff", border: "1px solid #d8d2c2", borderRadius: 4, padding: "11px 13px" }}>{th.s[L]}</div>

        {label(t.thmIdea)}
        <p data-field="idea" style={{ margin: 0, fontSize: 13.5, lineHeight: 1.55, color: "#3a3730" }}>{th.i[L]}</p>

        {label(t.thmHolds)}
        <div style={{ display: "flex", flexWrap: "wrap", gap: 6 }}>{th.on.map((e) => (typeof e === "string" ? nodeChip(e) : nodeChip(e[0], e[1])))}</div>

        {th.pr && th.pr.length > 0 && (
          <>
            {label(t.thmProves)}
            {th.pr.map(([of, is], i) => (
              <div key={i} data-field="proves" style={{ display: "flex", flexWrap: "wrap", gap: 7, alignItems: "center", padding: "5px 0" }}>
                <span style={{ fontFamily: MONO, fontSize: 12.5, background: "#eee8d8", borderRadius: 3, padding: "3px 7px" }}>{of[L]}</span>
                <span style={{ fontSize: 12.5, color: "#8a8578" }}>{t.thmIs}</span>
                {nodeChip(is)}
              </div>
            ))}
          </>
        )}

        {uses.length > 0 && (<>{label(t.thmUses)}{uses.map((id) => thmRow(id))}</>)}
        {usedBy.length > 0 && (<>{label(t.thmUsedBy)}{usedBy.map((id) => thmRow(id))}</>)}
      </>
    );
  })();

  // ---- the list ----
  const thmQ = foldText(search.trim());
  const filteredThms = THEOREMS.filter((th) => (!thmTopic || th.topic === thmTopic) && (!fr || !programmeOnly || th.prepa) && (!thmQ || THM_HAY[th.id].includes(thmQ)));
  const thmGroups = Object.keys(THM_TOPICS).map((k) => [k, filteredThms.filter((th) => th.topic === k)]).filter(([, l]) => l.length);
  const topicChips = [["", t.thmAllTopics, "#4a4638", THEOREMS.length], ...Object.entries(THM_TOPICS).map(([k, v]) => [k, v[lang], v.color, THEOREMS.filter((th) => th.topic === k).length])].map(([k, lab, color, cnt]) => (
    <button
      type="button"
      key={k || "all"}
      data-topic={k || "all"}
      aria-pressed={thmTopic === k}
      onClick={() => setThmTopic(k)}
      style={{ flexShrink: 0, whiteSpace: "nowrap", display: "flex", alignItems: "center", gap: 7, cursor: "pointer", fontSize: 12, fontFamily: MONO, color: "#4a4638", padding: "3px 8px", border: 0, borderRadius: 3, fontWeight: thmTopic === k ? 700 : 500, background: thmTopic === k ? "#eae4d4" : "transparent" }}
    >
      <span style={{ width: 10, height: 10, borderRadius: "50%", background: color, display: "inline-block" }} />
      {lab} <span style={{ opacity: 0.55 }}>{cnt}</span>
    </button>
  ));
  const thmListEl = (
    <div style={{ flex: 1, minWidth: 0, position: "relative" }}>
      <div style={{ position: "absolute", inset: 0, overflowY: "auto", overscrollBehavior: "contain", padding: isMobile ? "12px 12px 40px" : "20px 26px 60px" }}>
        <div data-field="count" style={{ fontFamily: MONO, fontSize: 12, color: "#8a8578", marginBottom: 6 }}>{t.thmCount(filteredThms.length)}</div>
        {filteredThms.length === 0 && <div style={{ fontStyle: "italic", color: "#8a8578", padding: "20px 0" }}>{t.thmNone}</div>}
        {thmGroups.map(([k, list]) => (
          <section key={k} data-topic-section={k} style={{ marginBottom: 22 }}>
            <div style={{ fontFamily: MONO, fontSize: 12, fontWeight: 600, letterSpacing: "0.04em", color: THM_TOPICS[k].color, margin: "10px 0 8px" }}>{THM_TOPICS[k][lang].toUpperCase()}</div>
            <div style={{ display: "grid", gridTemplateColumns: "repeat(auto-fill, minmax(270px, 1fr))", gap: 10 }}>
              {list.map((th) => {
                const sel = th.id === selThm;
                return (
                  <button
                    type="button"
                    key={th.id}
                    data-thm={th.id}
                    aria-pressed={sel}
                    onClick={(e) => { if (isMobile) panelOpenerRef.current = e.currentTarget; pickTheorem(th.id); }}
                    style={{ width: "100%", textAlign: "left", color: "inherit", font: "inherit", cursor: "pointer", padding: "9px 11px 10px", borderRadius: 4, background: sel ? "#fff" : "#fdfbf6", borderStyle: "solid", borderWidth: "1px 1px 1px 4px", borderColor: `${sel ? "#2a2a26" : "#e2dccb"} ${sel ? "#2a2a26" : "#e2dccb"} ${sel ? "#2a2a26" : "#e2dccb"} ${THM_TOPICS[th.topic].color}`, boxShadow: sel ? "0 1px 5px rgba(0,0,0,0.12)" : "none" }}
                  >
                    <span style={{ display: "flex", gap: 8, alignItems: "baseline", justifyContent: "space-between" }}>
                      <span style={{ fontSize: 14, fontWeight: 700, lineHeight: 1.3 }}>{thmName(th)}</span>
                      {fr && th.prepa && <span title={th.prepa === "MPSI" ? t.mpsi : t.mp} style={{ width: 9, height: 9, borderRadius: "50%", flexShrink: 0, background: PREPA_COLORS[th.prepa] }} />}
                    </span>
                    <span style={{ display: "block", fontFamily: MONO, fontSize: 10.5, color: "#8a8578", margin: "2px 0 4px" }}>{THM_KINDS[th.kind][lang]}{th.pr && th.pr.length ? " · ⟹" : ""}</span>
                    <span style={{ fontSize: 12.5, lineHeight: 1.45, color: "#4a4638", display: "-webkit-box", WebkitLineClamp: 3, WebkitBoxOrient: "vertical", overflow: "hidden" }}>{th.s[L]}</span>
                  </button>
                );
              })}
            </div>
          </section>
        ))}
      </div>
    </div>
  );

  const prepaCount = nodes.filter((n) => n.prepa).length;
  const totalNodes = DOMAINS.reduce((s, d) => s + d.nodes.length, 0);

  return (
    <div className="mm-root" style={{ fontFamily: "'Iowan Old Style','Georgia',serif", background: "#f7f4ee", color: "#2a2a26", display: "flex", flexDirection: "column", overflow: "hidden" }}>
      <style>{`.mm-root,.mm-panel-m{height:100vh;height:100dvh}.mm-scroll-x{scrollbar-width:none}.mm-scroll-x::-webkit-scrollbar{display:none}.mm-sr-only{position:absolute;width:1px;height:1px;padding:0;margin:-1px;overflow:hidden;clip:rect(0,0,0,0);white-space:nowrap;border:0}.mm-root :focus-visible{outline:3px solid #b8562f!important;outline-offset:3px!important}.mm-node:focus-visible rect{stroke:#b8562f;stroke-width:3}`}</style>
      <div style={{ padding: isMobile ? "10px 12px 8px" : "22px 36px 14px", borderBottom: "1px solid #d8d2c2", background: "#f7f4ee", flexShrink: 0 }}>
        <div style={{ display: "flex", flexDirection: "column", alignItems: "stretch", gap: isMobile ? 8 : 10, marginBottom: isMobile ? 8 : 14 }}>
          <div>
            <h1 style={{ margin: 0, fontSize: isMobile ? 17 : 23, fontWeight: 700, letterSpacing: "-0.01em" }}>{t.title}</h1>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: isMobile ? 10 : 11.5, color: "#7a7568", marginTop: isMobile ? 2 : 4 }}>
              {t.subtitle(totalNodes, DOMAINS.length, THEOREMS.length)}
            </div>
          </div>
          <div style={{ display: "flex", gap: isMobile ? 8 : 10, alignItems: "center", width: "100%", flexWrap: "wrap" }}>
            <div role="group" aria-label={t.language} style={{ display: "flex", border: "1px solid #c9c2ae", borderRadius: 3, overflow: "hidden" }}>
              {[["en", "EN"], ["fr", "FR"]].map(([code, label]) => (
                <button
                  key={code}
                  onClick={() => chooseLang(code)}
                  aria-pressed={lang === code}
                  style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 12, fontWeight: lang === code ? 700 : 500, padding: "8px 12px", border: "none", background: lang === code ? "#2a2a26" : "#fff", color: lang === code ? "#f7f4ee" : "#4a4638", cursor: "pointer" }}
                >
                  {label}
                </button>
              ))}
            </div>
            {fr && <button
              onClick={() => setProgrammeOnly((v) => !v)}
              style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 12, padding: "8px 12px", border: `1px solid ${programmeOnly ? "#b8305f" : "#c9c2ae"}`, borderRadius: 3, background: programmeOnly ? "#b8305f" : "#fff", color: programmeOnly ? "#fff" : "#4a4638", cursor: "pointer" }}
            >
              {programmeOnly ? (isMobile ? t.highlightShortOn : t.highlightOn) : isMobile ? t.highlightShort : t.highlight}
            </button>}
            <input
              ref={searchRef}
              id="mm-search"
              type="search"
              aria-label={view === "theorems" ? t.searchThm : t.search}
              value={search}
              onChange={(e) => setSearch(e.target.value)}
              placeholder={view === "theorems" ? t.searchThm : t.search}
              style={{ fontFamily: "inherit", fontSize: isMobile ? 16 : 14, padding: isMobile ? "6px 10px" : "8px 14px", border: "1px solid #c9c2ae", borderRadius: 3, background: "#fff", outline: "none", ...(isMobile ? { flex: "1 1 0", minWidth: 0 } : { minWidth: 190 }) }}
            />
          </div>
        </div>

        {/* Domain tabs */}
        <div className={isMobile ? "mm-scroll-x" : undefined} style={isMobile ? { display: "flex", gap: 6, flexWrap: "nowrap", overflowX: "auto", marginBottom: 8, paddingBottom: 2 } : { display: "flex", gap: 8, flexWrap: "wrap", marginBottom: 12 }}>
          {DOMAINS.map((d) => (
            <button
              key={d.key}
              onClick={() => { setView("tree"); switchDomain(d.key); }}
              style={{
                fontFamily: "'Iowan Old Style','Georgia',serif",
                fontSize: 13.5,
                fontWeight: (view === "tree" && d.key === activeDomainKey) ? 700 : 500,
                padding: isMobile ? "6px 12px" : "7px 14px",
                flexShrink: 0,
                whiteSpace: "nowrap",
                borderRadius: 16,
                border: (view === "tree" && d.key === activeDomainKey) ? "1px solid #2a2a26" : "1px solid #d8d2c2",
                background: (view === "tree" && d.key === activeDomainKey) ? "#2a2a26" : "#fff",
                color: (view === "tree" && d.key === activeDomainKey) ? "#f7f4ee" : "#4a4638",
                cursor: "pointer",
              }}
            >
              {domLabel(d)} <span style={{ opacity: 0.6, fontSize: 11.5 }}>· {d.nodes.length}</span>
            </button>
          ))}
          <button
            data-tab="theorems"
            onClick={() => { setView("theorems"); setSearch(""); setHoveredBranch(null); }}
            style={{
              fontFamily: SERIF,
              fontSize: 13.5,
              fontWeight: view === "theorems" ? 700 : 500,
              padding: isMobile ? "6px 12px" : "7px 14px",
              marginLeft: isMobile ? 4 : 10,
              flexShrink: 0,
              whiteSpace: "nowrap",
              borderRadius: 16,
              border: view === "theorems" ? "1px solid #b8562f" : "1px dashed #b8562f",
              background: view === "theorems" ? "#b8562f" : "#fff",
              color: view === "theorems" ? "#fff" : "#b8562f",
              cursor: "pointer",
            }}
          >
            ∴ {t.thmTab} <span style={{ opacity: 0.7, fontSize: 11.5 }}>· {THEOREMS.length}</span>
          </button>
        </div>

        <div className={isMobile ? "mm-scroll-x" : undefined} style={isMobile ? { display: "flex", gap: 6, flexWrap: "nowrap", overflowX: "auto" } : { display: "flex", gap: 16, flexWrap: "wrap" }}>
          {view === "theorems" ? topicChips : branchOrder.map((b) => (
            <button
              type="button"
              key={b}
              aria-pressed={hoveredBranch === b}
              // hover isolates a branch on desktop; on touch screens a tap toggles it
              onMouseEnter={isMobile ? undefined : () => setHoveredBranch(b)}
              onMouseLeave={isMobile ? undefined : () => setHoveredBranch(null)}
              onClick={() => setHoveredBranch((h) => (isMobile && h === b ? null : b))}
              style={{ flexShrink: 0, whiteSpace: "nowrap", display: "flex", alignItems: "center", gap: 7, cursor: "pointer", fontSize: 12, fontFamily: "'JetBrains Mono', monospace", color: "#4a4638", padding: "3px 8px", border: 0, borderRadius: 3, background: hoveredBranch === b ? "#eae4d4" : "transparent" }}
            >
              <span style={{ width: 10, height: 10, borderRadius: "50%", background: BRANCHES[b].color, display: "inline-block" }} />
              {branchLabel(b)}
            </button>
          ))}
        </div>
      </div>

      <div style={{ display: "flex", flex: 1, minHeight: 0, overflow: "hidden" }}>
        {view === "tree" ? (
        <div style={{ flex: 1, minWidth: 0, position: "relative" }}>
          <div ref={paneRef} style={{ position: "absolute", inset: 0, overflow: "auto", overscrollBehavior: "contain", touchAction: "pan-x pan-y", padding: `${PAD_T}px ${PAD_R}px ${PAD_B}px ${PAD_L}px` }}>
          <svg width={dims.w * scale} height={dims.h * scale} viewBox={`0 0 ${dims.w} ${dims.h}`} style={{ display: "block", ...(isMobile ? { userSelect: "none", WebkitUserSelect: "none", WebkitTapHighlightColor: "transparent" } : {}) }}>
            {branchOrder.map((b) => {
              const nodesInBranch = byBranch[b];
              if (!nodesInBranch || !nodesInBranch.length) return null;
              const minY = Math.min(...nodesInBranch.map((n) => positions[n.id].y));
              return (
                <text key={"label-" + b} x={16} y={minY - 28} fontSize={12} fontFamily="'JetBrains Mono', monospace" fontWeight={600} fill={BRANCHES[b].color} opacity={hoveredBranch && hoveredBranch !== b ? 0.25 : 0.85}>
                  {branchLabel(b).toUpperCase()}
                </text>
              );
            })}

            {nodes.map((n) =>
              n.parents.map((p) => {
                const a = positions[p];
                const c = positions[n.id];
                if (!a || !c) return null;
                const active = (isHighlighted(n.id) && isHighlighted(p)) || (selected === n.id && ancestors.has(p)) || (selected === p && descendants.has(n.id));
                const dim = isDimmed(n.id) || isDimmed(p);
                const midX = (a.x + c.x) / 2;
                return (
                  <path
                    key={p + "->" + n.id}
                    d={`M ${a.x + 84} ${a.y} C ${midX} ${a.y}, ${midX} ${c.y}, ${c.x - 84} ${c.y}`}
                    fill="none"
                    stroke={active ? "#b8562f" : "#c9c2ae"}
                    strokeWidth={active ? 2.2 : 1}
                    opacity={dim ? 0.1 : active ? 0.9 : 0.5}
                  />
                );
              })
            )}

            {nodes.map((n) => {
              const p = positions[n.id];
              if (!p) return null;
              const dim = isDimmed(n.id);
              const hl = isHighlighted(n.id);
              const isSel = n.id === selected;
              const color = BRANCHES[n.branch].color;
              return (
                <g key={n.id} className="mm-node" transform={`translate(${p.x - 84}, ${p.y - 16})`} onClick={() => setSelected(n.id)} onKeyDown={(e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); setSelected(n.id); } }} role="button" tabIndex={0} focusable="true" aria-label={`${nodeName(n)}${isSel ? ", selected" : ""}`} aria-pressed={isSel} style={{ cursor: "pointer" }} opacity={dim ? 0.18 : 1}>
                  <rect width={168} height={32} rx={4} fill={isSel ? color : "#fff"} stroke={color} strokeWidth={isSel ? 0 : hl ? 2 : 1.2} />
                  {fr && n.prepa && <circle cx={162} cy={6} r={4.5} fill={isSel ? "#fff" : PREPA_COLORS[n.prepa]} stroke={isSel ? PREPA_COLORS[n.prepa] : "none"} strokeWidth={1.5} />}
                  <title>{nodeName(n)}</title>
                  {(() => {
                    const lines = wrapName(nodeName(n));
                    const two = lines.length > 1;
                    return (
                      <text textAnchor="middle" fontSize={two ? 10 : 11} fontFamily="'Iowan Old Style','Georgia',serif" fontWeight={isSel ? 700 : 500} fill={isSel ? "#fff" : "#2a2a26"}>
                        {lines.map((ln, i) => (
                          <tspan key={i} x={84} y={two ? 14 + i * 12 : 20}>{ln}</tspan>
                        ))}
                      </text>
                    );
                  })()}
                </g>
              );
            })}
          </svg>
          </div>

          <div style={{ position: "absolute", left: isMobile ? 10 : 16, bottom: isMobile ? 14 : 22, display: "flex", alignItems: "center", gap: 6, pointerEvents: "none" }}>
            <div style={{ display: "flex", alignItems: "center", background: "#fff", border: "1px solid #c9c2ae", borderRadius: 4, boxShadow: "0 1px 4px rgba(0,0,0,0.12)", overflow: "hidden", pointerEvents: "auto" }}>
              {[
                { label: "−", title: t.zoomOut, onClick: () => zoomBy(1 / 1.2), disabled: scale <= ZOOM_MIN + 1e-6 },
                { label: Math.round(scale * 100) + "%", title: t.zoomReset, onClick: () => zoomBy(1 / scale), wide: true },
                { label: "+", title: t.zoomIn, onClick: () => zoomBy(1.2), disabled: scale >= ZOOM_MAX - 1e-6 },
                { label: "⤢", title: t.zoomFit, onClick: fitToView },
              ].map((b, i) => (
                <button
                  key={i}
                  onClick={b.onClick}
                  disabled={b.disabled}
                  title={b.title}
                  aria-label={b.title}
                  style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: b.wide ? 11.5 : 15, minWidth: b.wide ? 52 : isMobile ? 40 : 34, height: isMobile ? 40 : 32, padding: "0 6px", border: "none", borderLeft: i ? "1px solid #e4dfd0" : "none", background: "#fff", color: b.disabled ? "#c9c2ae" : "#2a2a26", cursor: b.disabled ? "default" : "pointer" }}
                >
                  {b.label}
                </button>
              ))}
            </div>
            {!isMobile && (
              <span style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 10.5, color: "#a39d8c", background: "rgba(247,244,238,0.85)", padding: "2px 5px", borderRadius: 3 }}>{t.zoomHint}</span>
            )}
          </div>

          {/* mobile: floating button that opens the full-screen info panel */}
          {isMobile && selNode && (
            <button
              onClick={(e) => { panelOpenerRef.current = e.currentTarget; setPanelOpen(true); }}
              title={t.openInfo}
              aria-label={t.openInfo}
              style={{ position: "absolute", right: 10, bottom: 14, maxWidth: "calc(100% - 200px)", height: 40, padding: "0 14px", display: "flex", alignItems: "center", gap: 6, border: "none", borderRadius: 20, background: "#2a2a26", color: "#f7f4ee", boxShadow: "0 2px 6px rgba(0,0,0,0.28)", fontFamily: "'Iowan Old Style','Georgia',serif", fontSize: 13.5, fontWeight: 600, cursor: "pointer" }}
            >
              <span aria-hidden="true">ⓘ</span>
              <span style={{ overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap" }}>{nodeName(selNode)}</span>
            </button>
          )}
        </div>
        ) : thmListEl}

        {(!isMobile || panelOpen) && (
        <div
          ref={isMobile ? panelRef : undefined}
          className={isMobile ? "mm-panel-m" : undefined}
          role={isMobile ? "dialog" : undefined}
          aria-modal={isMobile ? "true" : undefined}
          aria-label={isMobile ? (view === "theorems" ? thmName(THM_BY_ID[selThm]) : selNode ? nodeName(selNode) : t.openInfo) : undefined}
          tabIndex={isMobile ? -1 : undefined}
          style={isMobile
            ? { position: "fixed", top: 0, left: 0, right: 0, zIndex: 50, background: "#fbf9f4", overflowY: "auto", overscrollBehavior: "contain" }
            : { width: 360, flexShrink: 0, borderLeft: "1px solid #d8d2c2", padding: "24px 22px", background: "#fbf9f4", overflowY: "auto", overscrollBehavior: "contain" }}
        >
          {isMobile && (
            <div style={{ position: "sticky", top: 0, zIndex: 1, background: "#fbf9f4", borderBottom: "1px solid #d8d2c2", padding: "10px 12px" }}>
              <button
                onClick={closePanel}
                aria-label={view === "theorems" ? t.backToList : t.backToTree}
                style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 13, padding: "10px 14px", border: "1px solid #c9c2ae", borderRadius: 4, background: "#fff", color: "#2a2a26", cursor: "pointer" }}
              >
                {view === "theorems" ? t.backToList : t.backToTree}
              </button>
            </div>
          )}
          <div style={isMobile ? { padding: "16px 18px 56px" } : undefined}>
          {view === "theorems" ? thmDetail : selNode && (
            <>
              <div style={{ display: "flex", gap: 8, marginBottom: 10, flexWrap: "wrap" }}>
                <div style={{ display: "inline-block", fontSize: 11, fontFamily: "'JetBrains Mono', monospace", color: BRANCHES[selNode.branch].color, border: `1px solid ${BRANCHES[selNode.branch].color}`, borderRadius: 3, padding: "2px 7px" }}>
                  {branchLabel(selNode.branch)}
                </div>
                {fr && selNode.prepa && (
                  <div style={{ display: "inline-block", fontSize: 11, fontFamily: "'JetBrains Mono', monospace", color: "#fff", background: PREPA_COLORS[selNode.prepa], borderRadius: 3, padding: "2px 7px" }}>
                    {selNode.prepa === "MPSI" ? t.mpsi : t.mp}
                  </div>
                )}
              </div>
              <h2 style={{ margin: "0 0 2px", fontSize: 20 }}>{nodeName(selNode)}</h2>
              {nodeSub(selNode) && <div style={{ fontSize: 13.5, fontStyle: "italic", color: "#8a8578", marginBottom: 10 }}>{nodeSub(selNode)}</div>}
              {nodeBlurb(selNode) && <p style={{ fontSize: 14, lineHeight: 1.55, color: "#3a3730", margin: "0 0 14px" }}>{nodeBlurb(selNode)}</p>}

              {nodeDelta(selNode) && (
                <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 12.5, background: "#eee8d8", border: "1px solid #d8d2c2", borderRadius: 4, padding: "10px 12px", marginBottom: 16, color: "#4a4638" }}>
                  {nodeDelta(selNode)}
                </div>
              )}

              {AXIOMS[selNode.id] && (() => {
                const ids = [...new Set(AXIOMS[selNode.id])];
                const pick = (v) => (typeof v === "string" ? v : v[lang]);
                return (
                  <details
                    open={axOpen}
                    onToggle={(e) => setAxOpen(e.currentTarget.open)}
                    style={{ marginBottom: 16, border: "1px solid #d8d2c2", borderRadius: 4, background: "#fff" }}
                  >
                    <summary style={{ cursor: "pointer", padding: "9px 12px", fontFamily: "'JetBrains Mono', monospace", fontSize: 12, fontWeight: 600, color: "#4a4638", userSelect: "none" }}>
                      {t.axioms} ({ids.length})
                    </summary>
                    {ids.length === 0 ? (
                      <div style={{ padding: "2px 14px 12px", fontSize: 13.5, fontStyle: "italic", color: "#8a8578" }}>{t.axiomsNone}</div>
                    ) : (
                      <ol style={{ margin: 0, padding: "2px 14px 10px 34px", fontSize: 13.5, color: "#3a3730" }}>
                        {ids.map((id) => (
                          <li key={id} style={{ padding: "6px 0", borderTop: "1px solid #f0ebdd" }}>
                            <div style={{ fontWeight: 600 }}>{AX[id][lang]}</div>
                            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 12, color: "#4a4638", background: "#f6f2e6", borderRadius: 3, padding: "4px 7px", marginTop: 3, overflowWrap: "anywhere" }}>{pick(AX[id].f)}</div>
                          </li>
                        ))}
                      </ol>
                    )}
                  </details>
                );
              })()}

              {nodeThmSection}

              {fr && !selNode.prepa && (
                <div style={{ fontSize: 12.5, color: "#8a8578", marginBottom: 16, fontStyle: "italic" }}>{t.notInProgramme}</div>
              )}

              {selNode.seeAlso && selNode.seeAlso.length > 0 && (
                <div style={{ marginBottom: 16 }}>
                  <div style={{ fontSize: 11, fontFamily: "'JetBrains Mono', monospace", color: "#8a8578", marginBottom: 6 }}>{t.alsoSee}</div>
                  <div style={{ display: "flex", flexWrap: "wrap", gap: 6 }}>
                    {selNode.seeAlso.map((sa, i) => {
                      const targetDomain = domainByKey[sa.domain];
                      const targetNode = targetDomain && targetDomain.byId[sa.id];
                      if (!targetNode) return null;
                      return (
                        <button
                          key={i}
                          onClick={() => switchDomain(sa.domain, sa.id)}
                          style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 11.5, padding: "5px 9px", borderRadius: 3, border: "1px solid #c9c2ae", background: "#fff", color: "#4a4638", cursor: "pointer" }}
                        >
                          ↗ {nodeName(targetNode)} <span style={{ opacity: 0.55 }}>({domLabel(targetDomain)})</span>
                        </button>
                      );
                    })}
                  </div>
                </div>
              )}

              {selNode.parents.length > 0 && (
                <div style={{ marginBottom: 16 }}>
                  <div style={{ fontSize: 11, fontFamily: "'JetBrains Mono', monospace", color: "#8a8578", marginBottom: 6 }}>{upLabel}</div>
                  {selNode.parents.map((p) => (
                    <button type="button" key={p} onClick={() => setSelected(p)} style={{ display: "block", width: "100%", textAlign: "left", font: "inherit", background: "transparent", border: 0, cursor: "pointer", fontSize: 14, padding: "5px 0", color: BRANCHES[byId[p].branch].color, fontWeight: 600 }}>
                      ↑ {nodeName(byId[p])}
                    </button>
                  ))}
                </div>
              )}

              {(() => {
                const children = nodes.filter((n) => n.parents.includes(selected));
                if (!children.length) return null;
                return (
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, fontFamily: "'JetBrains Mono', monospace", color: "#8a8578", marginBottom: 6 }}>{downLabel} ({children.length})</div>
                    {children.map((c) => (
                      <button type="button" key={c.id} onClick={() => setSelected(c.id)} style={{ display: "block", width: "100%", textAlign: "left", font: "inherit", background: "transparent", border: 0, cursor: "pointer", fontSize: 14, padding: "5px 0", color: BRANCHES[c.branch].color, fontWeight: 600 }}>
                        ↓ {nodeName(c)}
                      </button>
                    ))}
                  </div>
                );
              })()}

              <div style={{ fontSize: 11, fontFamily: "'JetBrains Mono', monospace", color: "#8a8578", marginTop: 20 }}>
                {t.ancestors(ancestors.size)} · {t.descendants(descendants.size)}
              </div>
            </>
          )}
          </div>
        </div>
        )}
      </div>
    </div>
  );
}
