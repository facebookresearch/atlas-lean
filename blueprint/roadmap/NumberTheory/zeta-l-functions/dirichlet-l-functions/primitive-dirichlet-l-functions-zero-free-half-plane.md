# Primitive Dirichlet L-functions have no zero of real part greater than 1/2

For every primitive Dirichlet character $\chi$ and every complex number $s$ with
$\operatorname{Re} s > 1/2$, $L(s, \chi) \ne 0$; for the trivial character modulo $1$, whose
L-function is the Riemann zeta function, the pole $s = 1$ is excluded.

This node is still to be broken down into statements with published proofs. Its proof, listed
under Sources, derives the statement from one-sided growth bounds for weighted sums, over families
of characters, of smoothed Chebyshev functions twisted by those characters. That step uses
[Landau's theorem on Dirichlet integrals with non-negative integrands](analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-integrals.md),
with two theorems that Mathlib proves for Dirichlet characters: their L-functions are entire for
nontrivial characters, and do not vanish on $\operatorname{Re} s \ge 1$. The first is the case of
the finite-order Hecke characters of $\mathbb{Q}$ of the
[meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md), and
the second, on the line $\operatorname{Re} s = 1$, that of the
[non-vanishing of Hecke L-functions on the line Re s = 1](hecke-l-function-nonvanishing-on-re-one.md);
to the right of the line the Euler product gives it. Besides that step, the proof uses:

- Green's description of the cuspidal irreducible characters of $\mathrm{GL}_n(\mathbb{F}_p)$, $p$
  prime: their degrees and their values on the classes whose characteristic polynomial is
  irreducible;
- identities between theta integrals for unitary dual pairs, used alongside Howe duality and the
  Siegel–Weil formula at this step;
- a partial local Langlands correspondence for $\mathrm{GL}_n$ over $p$-adic fields, constructed
  from cuspidal parameters, with a local Artin map built from the global Artin map and compatible
  with it;
- Galois representations and Galois cohomology, through a bound over specified subfields of cyclotomic fields, a sum over primes $\ell$, weighted by
  $\log \ell$, of the lengths of Tate–Shafarevich groups of Tate twists of
  $\mathbb{Q}_\ell/\mathbb{Z}_\ell$;
- a bound for a covolume, assembled from resolution of singularities and principalization in
  characteristic $0$, the Poincaré–Lelong formula, an arithmetic Hilbert–Samuel theorem, Siegel
  toroidal compactifications and further inputs from the geometry of abelian schemes.

A good expansion replaces this page by pages for these inputs and for the steps that combine
them, each with a precise statement and a published source, and keeps the dependence of the
[half-plane form for all characters](grh-dirichlet-half-plane.md) on the primitive case. Steps of
that proof without a published account get pages once one exists.

Green's description is the page
[Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md),
in its prime-field case, and the partial correspondence uses the reciprocal map of the global Artin map of
[the global reciprocity law](../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), with the properties of
[the global Artin map on the Galois group of the maximal abelian extension](../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/artin-map-on-the-maximal-abelian-extension.md).
The other inputs are the following pages; those that are nodes are themselves still to be broken down:
[the Stone–von Neumann theorem](../../../RepresentationTheory/automorphic-representations/theta-correspondence/stone-von-neumann-theorem.md),
[the metaplectic group and the local Weil representation](../../../RepresentationTheory/automorphic-representations/theta-correspondence/metaplectic-group-and-local-weil-representation.md),
[the global Weil representation and theta functions](../../../RepresentationTheory/automorphic-representations/theta-correspondence/global-weil-representation-and-theta-functions.md),
[the Weil representation of unitary dual pairs](../../../RepresentationTheory/automorphic-representations/theta-correspondence/weil-representation-of-unitary-dual-pairs.md),
[the unramified theta correspondence](../../../RepresentationTheory/automorphic-representations/theta-correspondence/unramified-theta-correspondence.md),
[the duality for compact dual pairs](../../../RepresentationTheory/automorphic-representations/theta-correspondence/howe-duality-for-compact-dual-pairs.md),
[Howe duality over the reals](../../../RepresentationTheory/automorphic-representations/theta-correspondence/howe-duality-over-the-reals.md),
[global theta lifts](../../../RepresentationTheory/automorphic-representations/theta-correspondence/global-theta-lifts.md),
[Weil's convergence criterion for theta integrals](../../../RepresentationTheory/automorphic-representations/theta-correspondence/weil-convergence-criterion.md),
[Siegel Eisenstein series on unitary groups](../../../RepresentationTheory/automorphic-representations/theta-correspondence/siegel-eisenstein-series-on-unitary-groups.md),
[the Siegel–Weil formula in Weil's convergent range](../../../RepresentationTheory/automorphic-representations/theta-correspondence/siegel-weil-formula-convergent-range.md),
[the Rallis inner product formula](../../../RepresentationTheory/automorphic-representations/theta-correspondence/rallis-inner-product-formula.md),
[the doubling method](../../../RepresentationTheory/automorphic-representations/theta-correspondence/doubling-method.md),
[automorphic forms and automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md),
[reduction theory for adelic groups](../../algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md),
[the rapid decay of cusp forms](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md),
[Harish-Chandra's finiteness theorem](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/harish-chandra-finiteness-theorem.md),
[the discreteness of the cuspidal spectrum](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md),
[the tensor product theorem](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/tensor-product-theorem.md),
[multiplicity one for GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/multiplicity-one-for-gl-n.md),
[the Jacquet–Shalika classification](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/jacquet-shalika-classification.md),
[the Jacquet–Shalika bounds](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/jacquet-shalika-bounds.md),
[algebraic automorphic representations and Clozel's purity lemma](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/algebraic-automorphic-representations-and-clozel-purity.md),
[the endoscopic classification and base change for unitary groups](../../../RepresentationTheory/automorphic-representations/endoscopic-classification-and-base-change-for-unitary-groups.md),
[admissible representations of real reductive groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md),
[Harish-Chandra modules](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md),
[the continuous extension of (g, K)-maps into smooth Fréchet representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/extension-of-gk-maps-to-smooth-frechet-representations.md),
[the Dixmier–Malliavin theorem](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/dixmier-malliavin-theorem.md),
[discrete series representations and formal degrees](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md),
[Harish-Chandra's classification of the discrete series](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-discrete-series-classification.md),
[Jacquet's embedding theorem](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md),
[finite length of parabolically induced representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md),
[Zelevinsky's classification](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/zelevinsky-classification.md),
[the Langlands classification for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md),
[uniqueness of cuspidal support](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/uniqueness-of-cuspidal-support.md),
[depth under parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/depth-under-parabolic-induction-and-jacquet-functors.md),
[Galois cohomology and p-adic Hodge theory](../../algebraic-number-theory/galois-representations/galois-cohomology-and-p-adic-hodge-theory.md),
[vanishing theorems and resolution of singularities in characteristic zero](../../../AlgebraicGeometry/birational-geometry/vanishing-theorems-and-resolution-in-characteristic-zero.md),
[arithmetic intersection theory, heights and arithmetic volumes](../../../AlgebraicGeometry/arakelov-geometry/arithmetic-intersection-theory-heights-and-volumes.md)
and [abelian schemes and their moduli](../../../AlgebraicGeometry/abelian-varieties/abelian-schemes-and-their-moduli.md).

## Proof depends on

- [Landau's theorem on Dirichlet integrals with non-negative integrands](analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-integrals.md), for the step from the growth bounds to the zero-free half-plane
- [Meromorphic continuation of Hecke L-functions](hecke-l-function-meromorphic-continuation.md), for its case of the finite-order Hecke characters of $\mathbb{Q}$ that correspond to nontrivial primitive Dirichlet characters, whose L-functions are entire
- [Non-vanishing of Hecke L-functions on the line Re s = 1](hecke-l-function-nonvanishing-on-re-one.md), for the same case
- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field
- [Stone–von Neumann theorem for Heisenberg groups over local fields](../../../RepresentationTheory/automorphic-representations/theta-correspondence/stone-von-neumann-theorem.md)
- [Metaplectic group and the local Weil representation](../../../RepresentationTheory/automorphic-representations/theta-correspondence/metaplectic-group-and-local-weil-representation.md)
- [Global Weil representation and theta functions](../../../RepresentationTheory/automorphic-representations/theta-correspondence/global-weil-representation-and-theta-functions.md)
- [Splitting characters and the Weil representation of unitary dual pairs](../../../RepresentationTheory/automorphic-representations/theta-correspondence/weil-representation-of-unitary-dual-pairs.md)
- [Unramified theta correspondence](../../../RepresentationTheory/automorphic-representations/theta-correspondence/unramified-theta-correspondence.md)
- [Duality for compact dual pairs and the (GLₙ, GLₘ)-duality](../../../RepresentationTheory/automorphic-representations/theta-correspondence/howe-duality-for-compact-dual-pairs.md)
- [Howe duality for reductive dual pairs in real symplectic groups](../../../RepresentationTheory/automorphic-representations/theta-correspondence/howe-duality-over-the-reals.md)
- [Global theta lifts of cusp forms](../../../RepresentationTheory/automorphic-representations/theta-correspondence/global-theta-lifts.md)
- [Weil's convergence criterion for theta integrals](../../../RepresentationTheory/automorphic-representations/theta-correspondence/weil-convergence-criterion.md)
- [Siegel Eisenstein series on unitary groups](../../../RepresentationTheory/automorphic-representations/theta-correspondence/siegel-eisenstein-series-on-unitary-groups.md)
- [Siegel–Weil formula for unitary groups in Weil's convergent range](../../../RepresentationTheory/automorphic-representations/theta-correspondence/siegel-weil-formula-convergent-range.md)
- [Rallis inner product formula in Weil's convergent range](../../../RepresentationTheory/automorphic-representations/theta-correspondence/rallis-inner-product-formula.md)
- [Doubling method and standard L-functions of unitary groups](../../../RepresentationTheory/automorphic-representations/theta-correspondence/doubling-method.md)
- [Automorphic forms, cusp forms and automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md)
- [Siegel sets and reduction theory for adelic groups](../../algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md)
- [Rapid decay of cusp forms](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md)
- [Harish-Chandra's finiteness theorem for automorphic forms](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/harish-chandra-finiteness-theorem.md)
- [Discreteness of the cuspidal spectrum](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md)
- [Tensor product theorem for automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/tensor-product-theorem.md)
- [Multiplicity one for GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/multiplicity-one-for-gl-n.md)
- [Jacquet–Shalika classification of automorphic representations of GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/jacquet-shalika-classification.md)
- [Jacquet–Shalika bounds on Satake parameters](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/jacquet-shalika-bounds.md)
- [Algebraic automorphic representations and Clozel's purity lemma](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/algebraic-automorphic-representations-and-clozel-purity.md)
- [Endoscopic classification and base change for unitary groups](../../../RepresentationTheory/automorphic-representations/endoscopic-classification-and-base-change-for-unitary-groups.md)
- [Admissible representations of real reductive groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for Harish-Chandra's admissibility theorem for the irreducible unitary representations of the groups $\mathrm{U}(p, q)$, with the smoothness, $\mathfrak{g}$-stability and density of their $K$-finite vectors (not the analyticity of the orbit maps of $K$-finite vectors, which the library's form also asserts)
- [Harish-Chandra modules](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the Harish-Chandra modules of the irreducible unitary representations of the groups $\mathrm{U}(p, q)$, the correspondence between their submodules and the closed invariant subspaces, and the coincidence of infinitesimal and unitary equivalence (not the analyticity of the orbit maps of $K$-finite vectors, which the library's form also asserts)
- [Continuous extension of (g, K)-maps into smooth Fréchet representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/extension-of-gk-maps-to-smooth-frechet-representations.md), for the extension of $(\mathfrak{g}, K)$-maps from the Harish-Chandra modules of irreducible unitary representations of the groups $\mathrm{U}(p, q)$ to continuous $G$-maps, with closed image, into any smooth Fréchet representation of moderate growth
- [Dixmier–Malliavin theorem](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/dixmier-malliavin-theorem.md), for item 1 there, the factorization of compactly supported smooth functions on a Lie group as finite sums of convolutions with prescribed supports (Dixmier–Malliavin's Théorème 3.1)
- [Discrete series representations and formal degrees](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md), for the square-integrable representations of the groups $\mathrm{U}(p, q)$, whose centre is compact, and the Schur orthogonality relations for all vectors with the formal degree
- [Harish-Chandra's classification of the discrete series](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-discrete-series-classification.md), for the discrete series of the groups $\mathrm{U}(p, q)$ with prescribed Harish-Chandra parameters, obtained from those of $\mathrm{SU}(p, q)$, and their lowest $K$-types
- [Cuspidal representations and Jacquet's embedding theorem](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for the cuspidal supports and the admissibility of irreducible representations used in the partial local Langlands correspondence constructed from cuspidal parameters
- [Finite length of parabolically induced representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md), for the finite length of the products of representations of the groups $\mathrm{GL}_n$ used in that partial correspondence
- [Zelevinsky's classification of the irreducible representations of GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/zelevinsky-classification.md), for the segments and the polynomial structure of the Grothendieck ring used in that partial correspondence
- [Langlands classification for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), for the extension of that partial correspondence from cuspidal representations to all irreducible representations through multisets of segments, with the uniqueness of the multiset, the contragredients and the composition factor $L(a + b)$ of $L(a) \times L(b)$
- [Uniqueness of cuspidal support](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/uniqueness-of-cuspidal-support.md), for the uniqueness of the support of an irreducible representation of $\mathrm{GL}_n$, by which that partial correspondence compares the cuspidal supports it uses
- [Depth under parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/depth-under-parabolic-induction-and-jacquet-functors.md), for the depth of the members of a cuspidal support (Moy–Prasad), by which every member of the support of a representation of $\mathrm{GL}_n$ with nonzero vectors fixed by the principal congruence subgroup has such vectors too, used in that partial correspondence for its depth-zero representations
- [Global reciprocity law](../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the global Artin map, whose reciprocal is used to construct the compatible local Artin map in the partial correspondence
- [The global Artin map on the Galois group of the maximal abelian extension](../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/artin-map-on-the-maximal-abelian-extension.md), for the surjectivity, openness, kernel and local properties of that reciprocal map, which the partial correspondence uses
- [Galois cohomology and p-adic Hodge theory](../../algebraic-number-theory/galois-representations/galois-cohomology-and-p-adic-hodge-theory.md)
- [Vanishing theorems and resolution of singularities in characteristic zero](../../../AlgebraicGeometry/birational-geometry/vanishing-theorems-and-resolution-in-characteristic-zero.md)
- [Arithmetic intersection theory, heights and arithmetic volumes](../../../AlgebraicGeometry/arakelov-geometry/arithmetic-intersection-theory-heights-and-volumes.md)
- [Abelian schemes and their moduli](../../../AlgebraicGeometry/abelian-varieties/abelian-schemes-and-their-moduli.md)

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) whose five main theorems are two forms of the Riemann hypothesis (`riemannHypothesis`, `riemannZeta_eq_zero_re`) and three forms of the generalized Riemann hypothesis for Dirichlet L-functions (`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>. The statement of this page is not among those five theorems: in the library it is the internal proposition `ZeroFreeAll`, used through `UpperTheory.Top.imprimitive`; it has no exception at $s = 1$ because Mathlib gives $\zeta(1)$ a finite non-zero value. The step from the growth bounds is `Formalism.HC.Landau.zero_free_of_Chebyshev_growth`, through `landau_family`, in `TotientGaloisClasses/Landau.lean`. The inputs listed above are, in the library, `green_of_regular` with `Published.GreenRegularCharacters`; `ThetaIntegralsAgree` and `LocalMatching` beside Howe duality and Siegel–Weil in `SiegelEisensteinSecondTermHypotheses.lean`; `RecTExists`, constructed in `LocalCentralUnits/RecTExists.lean`, whose local Artin map `localArtinExists_holds` builds from the global Artin map of `globalArtinReciprocity_holds` (`InertiaEigenvalues/LocalArtinExistsHolds.lean`, lines 56–69); the window bound `VWin` of `CharacterBoxes/ExistsPageN.lean`, derived from `Row0b`; and the covolume bound assembled by `topCovolSlim2_use_alt_alt`.
