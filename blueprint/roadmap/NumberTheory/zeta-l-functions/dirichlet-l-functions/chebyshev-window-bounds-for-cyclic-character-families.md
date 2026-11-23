# Window bounds for weighted Chebyshev sums of cyclic families of characters

This node is still to be broken down. It covers the bound that the
[zero-free half-plane for primitive Dirichlet L-functions](primitive-dirichlet-l-functions-zero-free-half-plane.md)
feeds into the
[criterion on windows](zero-free-half-planes-from-chebyshev-bounds-on-windows.md), and its derivation
from [Green's description of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_p)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md),
the [window bound for Tate–Shafarevich groups](../../algebraic-number-theory/galois-representations/tate-shafarevich-window-bound-over-cyclotomic-subfields.md)
and the [definite-side hypotheses](../../../RepresentationTheory/automorphic-representations/definite-side-hypotheses-for-character-families.md).

The bound reads as follows. Let $\psi$ be a primitive Dirichlet character of order $o$, and let
$K_\psi$ be the set of the $o$ primitive characters that induce the powers $\psi^k$,
$0 \le k < o$; it contains $\psi$ and the trivial character modulo $1$. With $G_\chi$ the weighted
Chebyshev functions of the criterion, let

$$G_\psi^{\mathrm{cyc}}(y) = G_{\mathbf 1}(y) + \frac{1}{3o + 1} \sum_{\chi \in K_\psi,\ \chi \ne \mathbf 1} \operatorname{Re} G_\chi(y),$$

where $\mathbf 1$ is the trivial character modulo $1$. Then for every $\theta$ with
$1/2 < \theta < 1$ and every $Y_0 \ge 1$ there is $Y \ge Y_0$ with $G_\psi^{\mathrm{cyc}}(y) \le y^\theta$
for all $y \in [Y, Y^{3/2}]$.

Its derivation passes through two intermediate statements about auxiliary number fields, the
hosts, attached to scales and subject to many arithmetic conditions, and about families of hosts
along windows of scales. The first, from Green's description and the definite-side hypotheses,
says that whenever hosts meeting a given requirement exist at all large scales of a set of windows,
and the members of all families of such hosts satisfy the Tate–Shafarevich bound, some of these
families satisfy, at the scales of their windows, a chain of conditions (the "ties") from which the
bound above follows. The second, from the window bound for Tate–Shafarevich groups, supplies for every primitive
$\psi$ and every small $\varepsilon > 0$ hosts meeting the requirement attached to $\psi$, which
includes the Tate–Shafarevich bound for the host field, at all large scales of a set of windows of
exponent $3/2$.
These statements are not yet stated as pages because the hosts, families, scales and ties are defined
by long lists of conditions specific to this proof; a reviewable statement needs those notions first.

A good expansion has definition pages for the scales, the hosts, the families of hosts along
windows and the ties, a page for each of the two intermediate statements (with Green's
description and the definite-side hypotheses as the inputs of the first, and the Tate–Shafarevich
window bound as the input of the second), and a page for the step from the ties to the bound above.
Both intermediate statements also use a construction of Behrend's type, which a good expansion
states and links: there is $C > 0$ such that for all $n \ge 1$ and $L \ge 2$ some set $T$ of at least
$n e^{-C \sqrt{\log n \log L}} / L$ integers in $[0, n/4L)$ has no three distinct elements
$s_1, s_2, s_3$ with $j(s_2 - s_1) = i(s_3 - s_1)$ for distinct nonzero integers $i, j$ with
$|i|, |j| \le L$. It is built from Behrend's lemma that some sphere centred at the origin contains many
of the lattice points of a box.

## Proof depends on

- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field, in the first intermediate statement
- [Definite-side hypotheses for families of characters](../../../RepresentationTheory/automorphic-representations/definite-side-hypotheses-for-character-families.md), in the first intermediate statement
- [Window bound for Tate–Shafarevich groups of Tate twists over subfields of cyclotomic fields](../../algebraic-number-theory/galois-representations/tate-shafarevich-window-bound-over-cyclotomic-subfields.md), in the second intermediate statement

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The node is the step `UpperTheory.Top.zero_free_all_of_green_v_win` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean`, lines 12–15) up to the criterion: it applies `UpperTheory.Top.zeroFreeAll_of_topG` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean`, lines 12–34) with windows of exponent $3/2$. The first intermediate statement is `UpperTheory.Top.TopG` (same file, lines 12–14) with the ties `ChainTied` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean`, line 97); the second is `GlobalTheory.EX.HostExW` (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean`, lines 118–123) for the requirement `UpperTheory.Top.GChi` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean`, lines 42–43). The families $K_\psi$ with their weights are `Formalism.HC.Level.cyc` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean`, lines 30–38 and 103–121) and `UpperTheory.Comparison₂.level_family` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelFamily.lean`, lines 9–52). The bound above is the hypothesis that `Formalism.HC.level_of_tiedWin` passes to the criterion (`TotientGaloisClasses/TopWin.lean`, lines 68–81), obtained from `UpperTheory.Comparison₂.level_gm_le_on_family_scales` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean`, lines 30–32) and the families that the two intermediate statements supply. The inputs are consumed at `TopPlug.lean`, line 15: Green's description through `UpperTheory.Top.shape_closed_link_n_of_green` (`ThirdPlaceSeries/TopShape.lean`, line 33), with the description given by `GlobalTheory.GreenBridge.green_of_regular` at `ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, line 72; the definite-side hypotheses as the argument of `GlobalTheory.Fc.forall_goal_of_shape_of_hyps` (lines 13–15 there); and the window bound for Tate–Shafarevich groups through `UpperTheory.Top.supplyChi` (`src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean`, lines 8–16). The construction of Behrend's type is `Formalism.FrobeniusOrbits.hostThickExists` (`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean`, line 181, with `NoRel` and `HostThickExists` in `src/Formalism/FrobeniusOrbits/HostThickExists.lean`, lines 13–32), which applies Mathlib's `Behrend.exists_large_sphere` at line 302. The second intermediate statement reaches it through `UpperTheory.Top.supplyOfAdm` (`CharacterBoxes/HostOfField.lean`, line 17), `hof_thick` (`src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean`, line 71) and `UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2` (`src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean`, lines 29–37); the first through `shape_closed_link_n_of_green`, `field_lemmas_except_seven` (`src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/CMFieldLemmas.lean`, line 21) and `dropping_proposition_holds` (`.../GlobalRankLatticeProofs/DroppingPropositionHolds.lean`, lines 104–105).
