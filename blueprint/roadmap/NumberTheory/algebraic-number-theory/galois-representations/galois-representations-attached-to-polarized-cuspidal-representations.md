# Galois representations attached to polarized regular algebraic cuspidal representations over CM fields

This node is still to be broken down. It covers the existence of $\ell$-adic Galois representations
attached to cuspidal automorphic representations, in the form that the
[window bound for Tate–Shafarevich groups](tate-shafarevich-window-bound-over-cyclotomic-subfields.md)
and the
[definite-side hypotheses](../../../RepresentationTheory/automorphic-representations/definite-side-hypotheses-for-character-families.md)
use. Let $E$ be a CM field with maximal totally real subfield $E^+$, $\ell$ a prime and
$\iota \colon \overline{\mathbb{Q}}_\ell \to \mathbb{C}$ an isomorphism. For every $a \ge 1$ and every
cuspidal automorphic representation $\pi$ of $\mathrm{GL}_a(\mathbb{A}_E)$ that is regular algebraic and
polarized by a Hecke character of $E^+$, there are a continuous semisimple representation
$r \colon \operatorname{Gal}(\bar E/E) \to \mathrm{GL}_a(\overline{\mathbb{Q}}_\ell)$, an integer $w$ and, for
each embedding $\tau \colon E \to \overline{\mathbb{Q}}_\ell$, a multiset $\mathrm{HT}_\tau$ of integers,
such that:

- $\mathrm{HT}_\tau$ consists of the numbers $(a - 1)/2 - z$, for $z$ running over the infinitesimal
  character of $\pi$ at the archimedean place $\iota \circ \tau$, and
  $\mathrm{HT}_{\tau \circ c} = w - \mathrm{HT}_\tau$, where $c$ is complex conjugation;
- at each finite place $v \nmid \ell$, the Weil–Deligne representation of $r$ at $v$ is compared
  with the image of the local component $\pi_v$ under every partial correspondence with the laws of
  the [partial local Langlands correspondence for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/partial-local-langlands-correspondence-for-gl-n.md):
  the two have the same dimension; they are equal when that image has zero monodromy and the
  commutators of the Weil group act trivially on it; and at places whose completion is $\mathbb{Q}_g$ with $g > 16a^2$ (or for $a = 1$),
  when that image is tamely ramified with zero monodromy and a condition on its repeated inertia
  eigenvalues, the representation of $r$ has zero monodromy and the same characteristic polynomials
  on the elements of degree $0$ of the Weil group;
- at the places above $\ell$, $r$ is crystalline, with Hodge–Tate weights $\mathrm{HT}$, where $\pi$ is
  unramified, and de Rham and potentially semistable, with the same weights and the same comparison
  of Weil–Deligne representations, in the cases of the previous item.

Published theorems give such representations with local–global compatibility for the local
Langlands correspondence itself (Barnet-Lamb, Gee, Geraghty and Taylor, Theorem 2.1.1, below). The
form covered here compares with a partial correspondence and keeps only the clauses listed. It is
not yet stated as a page because these clauses are formulated with encodings specific to this proof
of Weil–Deligne representations, of the $p$-adic Hodge-theoretic conditions at the places above
$\ell$ (crystalline, de Rham and potentially semistable representations, Hodge–Tate jumps for a
chosen embedding) and of the normalization of local components; a reviewable statement needs these
encodings stated and checked first.

A good expansion has a page for the precise statement, once the
[partial local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/partial-local-langlands-correspondence-for-gl-n.md)
has one; a page for the published theorem of Barnet-Lamb, Gee, Geraghty and Taylor; and nodes for
the construction that the proof below follows, through theta lifts and the geometry of the
varieties they involve.

## Depends on

- [Partial local Langlands correspondence for GLₙ over completions of number fields](../../../RepresentationTheory/reductive-groups-over-local-fields/partial-local-langlands-correspondence-for-gl-n.md), whose laws the local–global compatibility above refers to
- [Automorphic representations of GLₙ and unitary groups](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n-and-unitary-groups.md), for cuspidal automorphic representations of $\mathrm{GL}_a(\mathbb{A}_E)$, their local components and their infinitesimal characters
- [Galois cohomology and p-adic Hodge theory](../../galois-representations/galois-cohomology-and-p-adic-hodge-theory.md), for Weil–Deligne representations and the crystalline, de Rham and potentially semistable representations

## Sources

- T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, "Potential automorphy and change of weight", Ann. of Math. 179 (2014), 501–609, arXiv:1010.2561 (version 2): §2.1, Theorem 2.1.1 (for a regular algebraic cuspidal polarized automorphic representation $(\pi, \chi)$ of $\mathrm{GL}_n(\mathbb{A}_F)$, a continuous semisimple $r_{l,\iota}(\pi)$ and an integer $w$ with local–global compatibility $\iota\mathrm{WD}(r_{l,\iota}(\pi)|_{G_{F_v}})^{F\text{-ss}} \cong \mathrm{rec}(\pi_v \otimes |\det|_v^{(1-n)/2})$ at $v \nmid l$, Hodge–Tate weights with $\mathrm{HT}_{\tau \circ c} = \{w - h : h \in \mathrm{HT}_\tau\}$, and crystallinity at $v \mid l$ where $\pi_v$ is unramified), which collects the work of Kottwitz, Clozel, Harris, Taylor, Bellaïche, Chenevier, Labesse, Shin and Caraiani cited there.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The node is `UpperTheory.GalStar.Row0b` with the notion `UpperTheory.Zero.LLC.IsRecT` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean`, lines 15–73, with `Tor` and `Sqf` in `WeightsConjAlt.lean`, lines 27–33, and `TmW` in `WeightsConj.lean`, line 18). The library proves it as `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`, line 6), through `galoisRepresentations_of_thetaLift` from `UpperTheory.Gal.Int.Geo.geoOne_holds` and the theta lift `UpperTheory.TP.K.tLiftK`. It is consumed twice (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, lines 7–8): by the window bound for Tate–Shafarevich groups, as the hypothesis of `UpperTheory.One.vwin_of_row` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`, lines 4–5); and by the definite-side hypotheses, as the fields `caraianiLocalGlobalDual` and `galoisRepOfPolarizedPairLit` of `UpperTheory.LiteratureTheorems.OpenLiteratureStatements` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, lines 215–218), used at lines 286 and 618 there. Its statement uses the laws of the partial correspondence through `IsRecT` (`MainConclusion.lean`, line 7), the cuspidal, regular algebraic and polarized representations `CuspSub`, `IsRegAlg` and `PolarizedPair`, and the $p$-adic Hodge-theoretic conditions `IsCrysAt`, `IsdRAt`, `IsPstAt` and `IsJumpsAt` (`WeightsConjBis.lean`, lines 39–73).
