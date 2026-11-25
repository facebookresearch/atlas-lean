# Galois representations attached to polarized regular algebraic cuspidal representations over CM fields

This node is still to be broken down. It covers the existence of $\ell$-adic Galois representations
attached to cuspidal automorphic representations, in the form that the
[window bound for Tate–Shafarevich groups](tate-shafarevich-window-bound-over-cyclotomic-subfields.md)
and the
[definite-side hypotheses](../../../RepresentationTheory/automorphic-representations/definite-side-hypotheses-for-character-families.md)
use. Let $E$ be a CM field with maximal totally real subfield $E^+$ and complex conjugation $c$, $\ell$
a prime and $\iota \colon \overline{\mathbb{Q}}_\ell \to \mathbb{C}$ an isomorphism. Let $a \ge 1$, let $\pi$
be a cuspidal automorphic representation of $\mathrm{GL}_a(\mathbb{A}_E)$ that is regular algebraic, and
let $\chi$ be a Hecke character of $E^+$ that polarizes $\pi$: $\chi_v(-1) = (-1)^a$ at every infinite
place $v$ of $E^+$, and $\pi^c \cong \pi^\vee \otimes (\chi \circ N_{E/E^+} \circ \det)$. Then there are a
continuous semisimple representation
$r \colon \operatorname{Gal}(\bar E/E) \to \mathrm{GL}_a(\overline{\mathbb{Q}}_\ell)$, an integer $w$ and, for
each embedding $\tau \colon E \to \overline{\mathbb{Q}}_\ell$, a multiset $\mathrm{HT}_\tau$ of integers,
with the following properties. In them $\sigma$ is the local component of $\pi$ at a finite place $v$,
$\mathrm{rc}$ is any map with the laws of the
[partial local Langlands correspondence for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/partial-local-langlands-correspondence-for-gl-n.md)
at $v$, and $\rho = \mathrm{rc}(\sigma \otimes |\det|_v^{(1-a)/2})$.

- $\mathrm{HT}_\tau$ consists of the numbers $(a - 1)/2 - z$, for $z$ running over the infinitesimal
  character of $\pi$ at the archimedean place $\iota \circ \tau$, and
  $\mathrm{HT}_{\tau \circ c} = w - \mathrm{HT}_\tau$.
- At each finite place $v \nmid \ell$ the Weil–Deligne representation $\mathrm{WD}_v$ of $r$ at $v$ is
  compared with $\rho$, for every such $\mathrm{rc}$, by three clauses: the two have the same dimension;
  $\mathrm{WD}_v = \rho$ when $\rho$ has zero monodromy and the commutators of the Weil group act
  trivially on it; and when $E_v \cong \mathbb{Q}_g$ for a prime $g$ and moreover $a = 1$ or $g > 16a^2$, and $\rho$
  has zero monodromy, is tamely ramified and every repeated eigenvalue of a generator of tame inertia
  on $\rho$ is an $(Nv - 1)$-th root of unity, $\mathrm{WD}_v$ has zero monodromy and the same
  characteristic polynomials as $\rho$ on the elements of degree $0$ of the Weil group.
- At each place $v \mid \ell$ where $\sigma$ is spherical, $r$ is crystalline and de Rham at $v$, with
  Hodge–Tate weights $\mathrm{HT}$.
- At each place $v \mid \ell$ and for every such $\mathrm{rc}$ for which $\rho$ has zero monodromy and
  is in one of the two cases of the second item (trivial commutators, or the conditions at
  $E_v \cong \mathbb{Q}_g$), $r$ is de Rham and potentially semistable at $v$, with Hodge–Tate weights
  $\mathrm{HT}$, and the Weil–Deligne representation that $p$-adic Hodge theory attaches to $r$ at $v$
  is compared with $\rho$ by the three clauses of the second item, and by nothing more.

The classical form of this statement, Theorem 2.1.1 of Barnet-Lamb, Gee, Geraghty and Taylor
(below), is a comparison with the normalized local Langlands correspondence itself:
$\iota\mathrm{WD}_v^{F\text{-ss}} \cong \mathrm{rec}(\sigma \otimes |\det|_v^{(1-a)/2})$ at $v \nmid \ell$, and at
$v \mid \ell$ the same isomorphism, with semistability, under the separate hypothesis that $\sigma$ has a
vector fixed by an Iwahori subgroup. The form covered here is not that theorem in other notation: it
quantifies over every map with the laws of a partial correspondence, keeps only the clauses listed,
and above $\ell$ asserts a comparison of Weil–Deligne representations only in the zero-monodromy
cases listed. It is held as a node because these clauses are formulated with encodings
specific to this proof of Weil–Deligne representations, of the $p$-adic Hodge-theoretic conditions at
the places above $\ell$ (crystalline, de Rham and potentially semistable representations, Hodge–Tate
jumps for a chosen embedding) and of the normalization of local components; a reviewable statement
needs these encodings stated and checked first.

A good expansion has a page for the precise statement, once the
[partial local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/partial-local-langlands-correspondence-for-gl-n.md)
has one; a page for the published theorem of Barnet-Lamb, Gee, Geraghty and Taylor; and nodes for
the construction that the proof below follows, through theta lifts and the geometry of the
varieties they involve.

## Expansion

A good expansion also states and links the following, each as Alpöge's library states it at the
locators under Sources:

- a geometric realization in weight one, which attaches $\ell$-adic Galois representations to the automorphic representations of definite unitary groups of odd rank over CM fields that satisfy the proof's congruence and sphericity conditions, compatible with the Satake parameters at the spherical places away from $\ell$ and crystalline, with prescribed Hodge–Tate jumps, at the places above $\ell$, for the Galois representations of the statement
- the existence of theta lifts of automorphic representations from the unitary group of a definite Hermitian space to those of definite skew-Hermitian spaces of every large dimension, under a bound on the weights, for moving to the representations that the geometric realization covers
- a congruence between weights, for reaching the weights that the geometric realization covers
- the argument for local–global compatibility that combines these inputs, for the clauses of the statement

## Depends on

- [Partial local Langlands correspondence for GLₙ over completions of number fields](../../../RepresentationTheory/reductive-groups-over-local-fields/partial-local-langlands-correspondence-for-gl-n.md), whose laws the local–global compatibility above refers to
- [Automorphic forms, cusp forms and automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cuspidal automorphic representations of $\mathrm{GL}_a(\mathbb{A}_E)$
- [Tensor product theorem for automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for their local components
- [Algebraic automorphic representations and Clozel's purity lemma](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/algebraic-automorphic-representations-and-clozel-purity.md), for regular algebraic representations and their infinitesimal characters
- [Weil–Deligne representations](weil-deligne-representations/weil-deligne-representations.md), for Weil–Deligne representations and their monodromy
- [Weil–Deligne representation of an ℓ-adic representation](weil-deligne-representations/weil-deligne-representation-of-an-l-adic-representation.md), for the Weil–Deligne representations of $r$ at the places away from $\ell$
- [Crystalline representations](p-adic-hodge-theory/crystalline-representations.md)
- [de Rham representations](p-adic-hodge-theory/de-rham-representations.md)
- [Semistable and potentially semistable representations](p-adic-hodge-theory/semistable-representations.md)
- [Hodge–Tate representations](p-adic-hodge-theory/hodge-tate-representations.md), for the Hodge–Tate weights
- [Weil–Deligne representation of a de Rham representation](p-adic-hodge-theory/weil-deligne-representation-of-a-de-rham-representation.md), for the Weil–Deligne representations that $p$-adic Hodge theory attaches to $r$ at the places above $\ell$

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Sources

- T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, "Potential automorphy and change of weight", Ann. of Math. 179 (2014), 501–609, arXiv:1010.2561 (version 2), cited as the classical comparison only: §2.1, the definition of a polarized pair (with $\chi_v(-1) = (-1)^n$ at the infinite places when $F$ is imaginary CM, and $\pi^c \cong \pi^\vee \otimes (\chi \circ N_{F/F^+} \circ \det)$), and Theorem 2.1.1 (for a regular algebraic cuspidal polarized automorphic representation $(\pi, \chi)$ of $\mathrm{GL}_n(\mathbb{A}_F)$, a continuous semisimple $r_{l,\iota}(\pi)$ and an integer $w$ with, in (2), $\iota\mathrm{WD}(r_{l,\iota}(\pi)|_{G_{F_v}})^{F\text{-ss}} \cong \mathrm{rec}(\pi_v \otimes |\det|_v^{(1-n)/2})$ at $v \nmid l$ for the normalized local Langlands correspondence; in (3), Hodge–Tate weights with $\mathrm{HT}_{\tau \circ c} = \{w - h : h \in \mathrm{HT}_\tau\}$; and in (4), the same isomorphism at $v \mid l$ when $\pi_v$ has an Iwahori-fixed vector, with semistability there and crystallinity where $\pi_v$ is unramified), which collects the work of Kottwitz, Clozel, Harris, Taylor, Bellaïche, Chenevier, Labesse, Shin and Caraiani cited there.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The node is `UpperTheory.GalStar.Row0b` with the notion `UpperTheory.Zero.LLC.IsRecT` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean`, lines 15–73, with `Tor` and `Sqf` in `WeightsConjAlt.lean`, lines 27–33, and `TmW` in `WeightsConj.lean`, line 18). The library proves it as `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`, line 6), through `galoisRepresentations_of_thetaLift` from `UpperTheory.Gal.Int.Geo.geoOne_holds` and the theta lift `UpperTheory.TP.K.tLiftK`. These are the inputs named above: `galoisLocalGlobalStrong_of_geometry_lift` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean`, lines 24–31) combines the geometric realization `GeoOne` (`.../IntegralStructures/GeometricFlagBases/HodgeTrAt.lean`, lines 79ff., proved as `geoOne_holds` in `.../GeometricFlagBases/WeightOneGeometricRealization.lean`, line 11), the theta lifts `UpperTheory.TP.TLiftK` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean`, lines 12–23) and the weight congruence `UpperTheory.Gal.Wt.wtLacEx_holds` through `coreAll_of`, and derives the local–global compatibility in `rest`. It is consumed twice (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, lines 7–8): by the window bound for Tate–Shafarevich groups, as the hypothesis of `UpperTheory.One.vwin_of_row` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`, lines 4–5); and by the definite-side hypotheses, as the fields `caraianiLocalGlobalDual` and `galoisRepOfPolarizedPairLit` of `UpperTheory.LiteratureTheorems.OpenLiteratureStatements` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, lines 215–218), used at lines 286 and 618 there. Its statement uses the laws of the partial correspondence through `IsRecT` (`MainConclusion.lean`, line 7), quantified over every map `rc` with them and applied to `algNorm σ`, the twist of the local component by $|\det|^{(1-a)/2}$ (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GaloisRepOfPolarizedCuspidal.lean`, lines 24–26), in `PropsB.away` and `AboveB.nice` (`WeightsConjBis.lean`, lines 48–59); the three clauses `AwayB` (lines 26–31), with `IsQpBig` (lines 15–16: $E_v \cong \mathbb{Q}_g$ and $a = 1$ or $16a^2 < g$); the cuspidal, regular algebraic and polarized representations `CuspSub`, `IsRegAlg` and `PolarizedPair` (`src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DualIsConjByOne.lean`, lines 48–55: the sign $\chi_v(-1) = (-1)^a$ and `DualIsConjBy`, the conjugate-dual twist); and the $p$-adic Hodge-theoretic conditions `IsCrysAt`, `IsdRAt`, `IsPstAt` and `IsJumpsAt` (`WeightsConjBis.lean`, lines 39–73), with the spherical case `AboveB.crys` (lines 43–46) separate from the zero-monodromy cases `AboveB.nice` (lines 48–52).
