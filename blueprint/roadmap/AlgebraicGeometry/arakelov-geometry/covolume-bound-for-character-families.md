# Covolume bound for the families of characters

This node is still to be broken down. It covers a bound for covolumes that the
[definite-side hypotheses](../../RepresentationTheory/automorphic-representations/definite-side-hypotheses-for-character-families.md)
use: for every family in a class of families of auxiliary number fields attached to scales (the
families of the
[window bounds for weighted Chebyshev sums](../../NumberTheory/zeta-l-functions/dirichlet-l-functions/chebyshev-window-bounds-for-cyclic-character-families.md)),
there is a constant $C_0 \ge 0$ such that, at every point of the family beyond some scale that
satisfies the point conditions and the tie condition of the argument, an inequality for the covolume
of a lattice that the argument attaches to the point holds for every constant $C \ge C_0$. Points
that fail these conditions are not constrained. Its proof is an argument in arithmetic geometry: it
is assembled from resolution of singularities and principalization in characteristic $0$, vanishing
theorems, the Poincaré–Lelong formula, arithmetic Hilbert–Samuel theorems and arithmetic degrees,
heights of cycles, toroidal compactifications of Siegel moduli spaces and further inputs from the
geometry of abelian schemes and $p$-divisible groups.

It is not yet stated as a page because the families, the points, their conditions and the lattices
attached to them are specific to this proof and defined through many auxiliary notions; a reviewable
statement needs those notions stated and checked first.

A good expansion has definition pages for the points of the families, their conditions and their
lattices, a page for the bound, and pages for the steps of its proof, linking the published results
it uses: those of the pages below, among them Fargues's integral Hodge–Tate sequence for
$p$-divisible groups, from the node on Galois cohomology and $p$-adic Hodge theory; and pages, still
to be added, for the integrality of Siegel toroidal compactifications and the Kodaira–Spencer
isomorphism on them, the seminegativity of the Lie algebras of semi-abelian schemes, the Hodge
filtration of prismatic Dieudonné modules, Serre's theorem on holomorphic sections, the existence of
Chow forms, Mumford's proportionality for toroidal compactifications, and Green's generic irreducible
characters of $\mathrm{GL}_N(\mathbb{F}_p)$ attached to polynomials, which extend the cuspidal case. The
bundle of published results that the library passes to this proof also contains results that no step
of it uses, which the page does not list: volumes of line bundles, semistable reduction, strong
approximation for special unitary groups, Green's series, the Hasse norm theorem, Landherr's theorem,
the simplicity of induced Weyl modules in the lowest alcove, the sections of principal polarizations
and multiplication by $n$ on abelian schemes.

## Proof depends on

- [Vanishing theorems and resolution of singularities in characteristic zero](../birational-geometry/vanishing-theorems-and-resolution-in-characteristic-zero.md), for resolution of singularities and principalization in characteristic $0$, the Poincaré–Lelong formula, the Kawamata–Viehweg and Nadel vanishing theorems with the separation of points that Nadel's theorem gives, Riemann–Roch and the numerics of nef line bundles, and $L^2$ extension
- [Arithmetic intersection theory, heights and arithmetic volumes](arithmetic-intersection-theory-heights-and-volumes.md), for the arithmetic Hilbert–Samuel theorem, Moriwaki's bigness criterion, arithmetic degrees, Chern–Weil forms and heights of cycles
- [Abelian schemes and their moduli](../abelian-varieties/abelian-schemes-and-their-moduli.md), for toroidal compactifications of Siegel moduli spaces, Zarhin's trick, Grothendieck–Messing deformation theory, the de Rham cohomology of abelian schemes, Grothendieck's existence theorem and extensions of homomorphisms of semi-abelian schemes
- [Galois cohomology and p-adic Hodge theory](../../NumberTheory/galois-representations/galois-cohomology-and-p-adic-hodge-theory.md), for Fargues's integral Hodge–Tate sequence of $p$-divisible groups
- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field, from which the generic irreducible characters attached to polynomials are obtained
- [Existence theorem of global class field theory](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/global-existence-theorem.md), for the ray class fields

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it, with `TPL/` for `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/`). The bound is `GlobalTheory.CovTop.CovolumeBoundOfX` (`TPL/ThirdPlaceSeries/LiftLambdaBound.lean`, lines 60–61), for the families `FamHyp` and the points `Pt` of the library, quantified through `EventuallyAtAllPoints` (lines 18–19) over the points that satisfy `RowsTAlt` (line 17): the point conditions `PointConditions'` and the tie condition `RecTied`. The library proves it as `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` (`TPL/ThirdPlaceSeries/TopCovolSlim2Use.lean`, lines 16–22), and it is consumed by the definite-side hypotheses at `TPL/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, lines 44 and 65. Its fifteen arguments are supplied at `TPL/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, line 812, and consumed in `TopCovolSlim2Use.lean`: resolution, principalization, the Poincaré–Lelong formula, the Hilbert–Samuel and bigness statements, Fargues's sequence (`HT.FarguesExact`), Zarhin's trick and `NefRR` by `PositivityTheory.HtPt.Ah.deep_slim_use` at line 22; Green's description through `GlobalTheory.GreenBridge.green_of_regular` at line 18, with `ToroidalForFanKS`, `SemiAbelianLieSeminegative` and `PointSeparationPair`; `SiegelToroidalIntegral` and `ArDegree` at line 20; `GrothendieckDeformation` and the bundle `GlobalTheory.CovTop.PublishedHodgeBundleTheorems` (`published_results_arithmetic`, lines 781–809 of `EveryCharacterOfLiteratureOfVWin.lean`; structure in `TPL/HodgeBundleWeights/ToKnownTheoremsOf.lean`, lines 7–35) at line 21. Of that bundle's fields, line 21 projects `q6` (Kawamata–Viehweg), `q7` (nef numerics), `q8` ($L^2$ extension), `q10` (Chow forms) and `q13` (Serre's theorem), and the steps below project the others that the page lists: `p1` (toroidal compactifications) at `TPL/HodgeBundleWeights/WeilHeightArchimedeanContribution.lean`, line 39; `p4` (arithmetic degrees) at `TPL/HodgeBundleWeights/VolumeLeSelfIntersection.lean`, line 58; `p5` (de Rham cohomology), `q1` (Grothendieck–Messing) and `q18` (Grothendieck's existence theorem) at `TPL/HodgeBundleWeights/RefExpPadicValLeShiftOfWeightFree.lean`, line 21; `p8` (ray class fields) at `TPL/HodgeBundleWeights/ExistsUnramifiedCurveOverField.lean`, line 15; `p16` (Chern–Weil forms, through Mumford's proportionality) at `TPL/HodgeBundleWeights/ProportionalityOfLocalCharts.lean`, line 62; `p22` (homomorphisms of semi-abelian schemes) at `TPL/HodgeBundleWeights/HodgeLineBundleBignessOnShimuraVariety.lean`, line 24; `q4` (prismatic Dieudonné modules) at `TPL/HodgeBundleWeights/FlatDegreeStatement.lean`, line 13; `q9` (arithmetic Hilbert–Samuel) at `TPL/HodgeBundleWeights/VolumeLineBundleLe.lean`, line 18; `q11` (heights of cycles) at `TPL/HodgeBundleWeights/ExistsNefModelOfImage.lean`, line 29; and `q15` (Nadel vanishing) and `q16` (principalization) at `TPL/ThirdPlaceSeries/RankGrowthBoundSmallScale.lean`, line 76. The fields `p2`, `p3`, `p12`, `p13`, `p14`, `p19`, `p20`, `p23`, `p25` and `p26` are only copied into the record `GlobalTheory.CovTop.Hypotheses''` (`TPL/HodgeBundleWeights/ToKnownTheoremsOf.lean`, lines 39–46), whose corresponding fields no step projects.
