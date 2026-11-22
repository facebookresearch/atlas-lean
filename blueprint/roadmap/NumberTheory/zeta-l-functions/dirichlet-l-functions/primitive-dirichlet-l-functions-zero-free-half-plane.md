# Primitive Dirichlet L-functions have no zero of real part greater than 1/2

For every primitive Dirichlet character $\chi$ and every complex number $s$ with
$\operatorname{Re} s > 1/2$, $L(s, \chi) \ne 0$; for the trivial character modulo $1$, whose
L-function is the Riemann zeta function, the pole $s = 1$ is excluded.

This node is still to be broken down into statements with published proofs. Its proof, listed
under Sources, uses, besides results on Dirichlet L-functions:

- Green's description of the cuspidal irreducible characters of $\mathrm{GL}_n(\mathbb{F}_p)$, $p$
  prime: their degrees and their values on the classes whose characteristic polynomial is
  irreducible;
- identities between theta integrals for unitary dual pairs, used alongside Howe duality and the
  Siegel–Weil formula at this step;
- a partial local Langlands correspondence for $\mathrm{GL}_n$ over $p$-adic fields, constructed
  from cuspidal parameters, with global reciprocity entering one uniqueness statement;
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
[Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md).
The other inputs belong to eight nodes that are themselves still to be broken down:
[the theta correspondence for unitary dual pairs](../../../RepresentationTheory/automorphic-representations/theta-correspondence-for-unitary-dual-pairs.md),
[automorphic representations of GLₙ and unitary groups](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n-and-unitary-groups.md),
[representations of U(p, q)](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-u-p-q.md),
[smooth representations of p-adic GLₙ and the local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/smooth-representations-of-p-adic-gl-n-and-local-langlands.md),
[Galois cohomology and p-adic Hodge theory](../../galois-representations/galois-cohomology-and-p-adic-hodge-theory.md),
[vanishing theorems and resolution of singularities in characteristic zero](../../../AlgebraicGeometry/birational-geometry/vanishing-theorems-and-resolution-in-characteristic-zero.md),
[arithmetic intersection theory, heights and arithmetic volumes](../../../AlgebraicGeometry/arakelov-geometry/arithmetic-intersection-theory-heights-and-volumes.md)
and [abelian schemes and their moduli](../../../AlgebraicGeometry/abelian-varieties/abelian-schemes-and-their-moduli.md).

## Proof depends on

- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md)
- [Theta correspondence for unitary dual pairs](../../../RepresentationTheory/automorphic-representations/theta-correspondence-for-unitary-dual-pairs.md)
- [Automorphic representations of GLₙ and unitary groups](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n-and-unitary-groups.md)
- [Representations of U(p, q)](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-u-p-q.md)
- [Smooth representations of p-adic GLₙ and the local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/smooth-representations-of-p-adic-gl-n-and-local-langlands.md)
- [Galois cohomology and p-adic Hodge theory](../../galois-representations/galois-cohomology-and-p-adic-hodge-theory.md)
- [Vanishing theorems and resolution of singularities in characteristic zero](../../../AlgebraicGeometry/birational-geometry/vanishing-theorems-and-resolution-in-characteristic-zero.md)
- [Arithmetic intersection theory, heights and arithmetic volumes](../../../AlgebraicGeometry/arakelov-geometry/arithmetic-intersection-theory-heights-and-volumes.md)
- [Abelian schemes and their moduli](../../../AlgebraicGeometry/abelian-varieties/abelian-schemes-and-their-moduli.md)

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) whose five main theorems are two forms of the Riemann hypothesis (`riemannHypothesis`, `riemannZeta_eq_zero_re`) and three forms of the generalized Riemann hypothesis for Dirichlet L-functions (`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>. The statement of this page is not among those five theorems: in the library it is the internal proposition `ZeroFreeAll`, used through `UpperTheory.Top.imprimitive`; it has no exception at $s = 1$ because Mathlib gives $\zeta(1)$ a finite non-zero value. The inputs listed above are, in the library, `green_of_regular` with `Published.GreenRegularCharacters`; `ThetaIntegralsAgree` and `LocalMatching` beside Howe duality and Siegel–Weil in `SiegelEisensteinSecondTermHypotheses.lean`; `RecTExists`, constructed in `LocalCentralUnits/RecTExists.lean`; the window bound `VWin` of `CharacterBoxes/ExistsPageN.lean`, derived from `Row0b`; and the covolume bound assembled by `topCovolSlim2_use_alt_alt`.
