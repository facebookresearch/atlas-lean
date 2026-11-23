# Covolume bound for the families of characters

This node is still to be broken down. It covers a bound for covolumes that the
[definite-side hypotheses](../../RepresentationTheory/automorphic-representations/definite-side-hypotheses-for-character-families.md)
use: for every family in a class of families of auxiliary number fields attached to scales (the
families of the
[window bounds for weighted Chebyshev sums](../../NumberTheory/zeta-l-functions/dirichlet-l-functions/chebyshev-window-bounds-for-cyclic-character-families.md)),
there is a constant $C_0 \ge 0$ such that, at all the points of the family beyond some scale, an
inequality for the covolume of a lattice that the argument attaches to the point holds for every
constant $C \ge C_0$. Its proof is an argument in arithmetic geometry: it is assembled from
resolution of singularities and principalization in characteristic $0$, vanishing theorems, the
Poincaré–Lelong formula, arithmetic Hilbert–Samuel theorems and arithmetic volumes, heights of
cycles, toroidal compactifications of Siegel moduli spaces and further inputs from the geometry of
abelian schemes and $p$-divisible groups.

It is not yet stated as a page because the families, the points and the lattices attached to them
are specific to this proof and defined through many auxiliary notions; a reviewable statement needs
those notions stated and checked first.

A good expansion has definition pages for the points of the families and their lattices, a page for
the bound, and pages for the steps of its proof, linking the published results it uses: those of the
pages below, among them Fargues's integral Hodge–Tate sequence for $p$-divisible groups, from the node
on Galois cohomology and $p$-adic Hodge theory; and pages, still to be added, for the integrality of
Siegel toroidal compactifications and the Kodaira–Spencer isomorphism on them, the seminegativity of
the Lie algebras of semi-abelian schemes, the Hodge filtration of prismatic Dieudonné modules, Serre's
theorem on holomorphic sections, Landherr's theorem, the simplicity of induced Weyl modules in the
lowest alcove, the existence of Chow forms, and Green's generic irreducible characters of
$\mathrm{GL}_N(\mathbb{F}_p)$ attached to polynomials, with their degrees, which extend the cuspidal case.

## Proof depends on

- [Vanishing theorems and resolution of singularities in characteristic zero](../birational-geometry/vanishing-theorems-and-resolution-in-characteristic-zero.md), for resolution of singularities and principalization in characteristic $0$, the Poincaré–Lelong formula, the Kawamata–Viehweg and Nadel vanishing theorems with the separation of points that Nadel's theorem gives, Riemann–Roch and volumes for nef line bundles, and $L^2$ extension
- [Arithmetic intersection theory, heights and arithmetic volumes](arithmetic-intersection-theory-heights-and-volumes.md), for the arithmetic Hilbert–Samuel theorem, Moriwaki's bigness criterion, arithmetic degrees, Chern–Weil forms and heights of cycles
- [Abelian schemes and their moduli](../abelian-varieties/abelian-schemes-and-their-moduli.md), for toroidal compactifications of Siegel moduli spaces, semistable reduction, Zarhin's trick, duality and the sections of principal polarizations, multiplication by $n$, Grothendieck–Messing deformation theory, the de Rham cohomology of abelian schemes, Grothendieck's existence theorem and extensions of homomorphisms of semi-abelian schemes
- [Galois cohomology and p-adic Hodge theory](../../NumberTheory/galois-representations/galois-cohomology-and-p-adic-hodge-theory.md), for Fargues's integral Hodge–Tate sequence of $p$-divisible groups
- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field, from which the generic irreducible characters attached to polynomials are obtained
- [Existence theorem of global class field theory](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/global-existence-theorem.md), for the ray class fields
- [Hasse norm theorem for cyclic extensions](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/hasse-norm-theorem.md)
- [Strong approximation for special unitary groups](../../NumberTheory/quadratic-forms-sums-of-squares/strong-approximation-special-unitary.md)

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it, with `.../ThirdPlaceSeries/` for `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`). The bound is `GlobalTheory.CovTop.CovolumeBoundOfX` (`.../ThirdPlaceSeries/LiftLambdaBound.lean`, lines 17–19 and 60–61), for the families `FamHyp` and the points `Pt` of the library. The library proves it as `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` (`.../ThirdPlaceSeries/TopCovolSlim2Use.lean`, line 16), and it is consumed by the definite-side hypotheses at `.../ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, lines 44 and 65. The inputs are consumed as the arguments of `topCovolSlim2_use_alt_alt` at `.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, line 812, and as the fields of the bundle `GlobalTheory.CovTop.PublishedHodgeBundleTheorems` (`published_results_arithmetic`, lines 781–809 there): resolution of singularities and principalization (`ResolutionCharZero`, `PrincipalisationCharZero`, lines 555–558; fields `q16`, line 808), the Poincaré–Lelong formula (`PoincareLelongInv`, lines 553–554), the vanishing theorems, separation of points, nef line bundles and $L^2$ extension (`PointSeparationPair`, line 471, `NefRR`, line 551; fields `p2`, `p3`, `q6`, `q7`, `q8` and `q15`, lines 783–784, 800–802 and 807), the arithmetic Hilbert–Samuel theorem and Moriwaki's criterion (`PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright` and `moriwakiBig_outright`; field `q9`, line 803), arithmetic degrees, Chern–Weil forms and heights of cycles (`ArDegree`, lines 251–252; fields `p4`, `p16` and `q11`, lines 785, 791 and 805), the results on abelian schemes (`ZarhinStatement`, lines 547–548, `SiegelToroidalIntegral`, `ToroidalForFanKS`, `SemiAbelianLieSeminegative`, lines 499, 509 and 523, `GrothendieckDeformation`, lines 405–406; fields `p1`, `p5`, `p12`, `p22`, `p25`, `p26`, `q1` and `q18`, lines 782, 786, 788, 794, 796–798 and 809), Fargues's sequence (`FarguesExact`, lines 549–550), the prismatic Dieudonné statement (field `q4`, line 799), Green's generic characters (field `p14`, line 790, with `green_series_st_of_literature`, lines 401–402, obtained from Green's cuspidal description), the ray class fields (field `p8`, line 787), the Hasse norm theorem (field `p20`, line 793), strong approximation (field `p13`, line 789), Landherr's theorem (field `p19`, line 792), induced Weyl modules (field `p23`, line 795), Chow forms (field `q10`, line 804) and Serre's theorem on holomorphic sections (field `q13`, line 806).
