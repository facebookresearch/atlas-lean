/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesProbe
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactEmbDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.PieceIntegration
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Rees-route close mod crux-only
Wire: gap-rees-9 (`HdimEqMinAtAss`, `d ≥ 2`) through the
Suppliers (closed `hpiece`, unconditional `hF`/`hhsDeg`, the
`d = 2` joints), with the C1–C4 survey addresses refreshed to
current lines. No new Rees machinery: every theorem below is a
restatement discharging a Rees condition on suppliers, plus
one Newton core (the `d = 2` slice) and one residual SPEC (the `Ge3`
slice).

## Verdict: Rees closes mod crux-only — no gap-rees-10

The exact mod-crux masters are `rees_hdimEqMin_of_sopGrLowerGated_ge3`
(§2: full `HdimEqMinAtAss` on `[HsopGrLowerD2GatedAtAss,
HdimEqMinGe3AtAss]`) and its geometry deliveries
`rees_hkerMin_of_sopGrLowerGated_ge3`,
`rees_hdepth_of_sopGrLowerGated_ge3`,
`rees_hunmixed_general_of_sopGrLowerGated_ge3` (§4). Both remainders
are crux-ring forms: the gated residual is iff-equivalent to
`HkerD2AtAss` (`highD2Close_sopGrLowerD2Gated_iff_hkerD2`,
HighD2Close:379), and the `Ge3` slice is the `d ≥ 3` restriction of
the joint-9 `HdimEqMinAtAss` (HighD2Close:485). No non-crux gap
survives, so no gap-rees-10 is opened.

## gap-rees-9 reassessment (old → new)

* Old (ReesProbe header): open, owned by the crux work
  (`NoetherGeAtAss`, High@Ge2). Not scoped.
* New: split. The `d = 2` slice closes on crux-`d = 2` inputs —
  `rees_hdimEqMin_d2_of_grExactD2` (§1, Newton core, ~15 proof
  lines: `deg ≤ 1` + first-difference nonvanishing forces
  `deg = 1` via `lt_natDegree_of_not_eventuallyEq_zero`), hence on
  `[HkerD2AtAss]` (GrExact §3:230) and on
  `[HsopGrLowerD2GatedAtAss]` (D2 joint, HighD2Close:253). The
  surviving residual is exactly the `Ge3` slice
  `HdimEqMinGe3AtAss` (§1 SPEC) — gap-rees-9′. Total new price:
  this file (500 lines, 1 SPEC + 14 theorems), residual register
  §5.
* Which Rees conditions the D2 joints discharge: the §2 joints
  (`highD2Close_hkerD2_of_sopGrLowerGated`:253 and the D2 ring)
  supply the `d = 2` leg of the `hker` input Rees consumes
  (`HkerD2AtAss` on `[gated]`), and via GrExact §3 the `d = 2`
  leg of `HgrExactD2AtAss`; the §1 core turns that leg into the
  `d = 2` slice of `HdimEqMinAtAss` itself, so the Min `d`-split
  (`hkerMinAtAss_of_hdimEqMin`) closes its `d = 2` case on
  crux-`d = 2` and its `d ≥ 3` case rides the `Ge3` slice.

## C1–C4 survey addresses (all re-verified in tree)

* C1 = augmentation quasi-iso pair at `residueCat`: proved on
  `[hker]` — `koszulResiduePi_quasiIso`
  (`QuasiIsomorphismBridge.lean`, stable) + Shrink adapter
  `quasiIso_residuePiShrunk` (`ReesAssembly.lean`,
  stable).
* C2 = Ext-comparison + Ext-subsingleton below `d`: proved on
  `[hker]` — `koszulProjectiveResolutionOfSequence`
  (`ExtComparison.lean`, stable) + §13 master
  `koszulExt_subsingleton_below_ofSequence`
  (`SelfDuality.lean`, stable).
* C3 = shift-side triple `(e, hS, hS0)`: proved —
  `koszulShiftIsoSigned_commRing_ofSequence`
  (`SelfDuality.lean`, stable, unconditional given `g`);
  `hS`/`hS0` on `[hker]` (`shift_hS_of_r2Reduced`,
  `shift_hS0_of_r2Reduced`, `HomologyTransport.lean`,
  stable).
* C4 = dimension equation: proved unconditional given sop data —
  `grlift_dim_eq_of_sop` (`GradedLift.lean`, stable) via
  `mult_dim_atPrime_eq_spanFinrank`
  (`MultiplicityNonvanishing.lean`, stable).
* Sop data `(g, hgen, hd)`: proved unconditional —
  `grlift_sop_exists` (`GradedLift.lean`, moved +2 from
  the:154 cited in ReesProbe — lone line shift in the survey).
* Basis `b`: proved unconditional — `extBasisULift`
  (`Geometry/K2UnmixednessEndgame.lean`, stable).
* Rees-tfae side conditions: discharged inside the §2 wrapper
  (`exists_isRegular_of_residue_subsingleton`,
  `ReesAssembly.lean`, stable).
* End-to-end: `depthEqDimAt_of_r2Reduced` (`§6 MAIN`,
  `ReesAssembly.lean`, stable) +
  `depthEqDimAt_zero_of_sop` (`§7`,
  `ReesAssembly.lean`, stable) →
  `depthEqDimAt_of_hker_atPrime` (`Geometry/K2UnmixednessEndgame.lean`,
  stable) and `depthEqDimAt_of_hkerMin_atPrime`
  (`Geometry/UnmixednessAtLengthTwo.lean`, stable).
* `d`-split: `hkerAtAss_of_hmin_hdimEq`
  (`Geometry/K2UnmixednessEndgame.lean`, stable),
  `hminOneAtAss_of_pair` (`Geometry/K2UnmixednessEndgame.lean`,
  stable), `hkerMinAtAss_of_hdimEqMin`
  (`Geometry/UnmixednessAtLengthTwo.lean`, stable).
* ReesProbe wires (all stable):
  `rees_hkerAtAss_pair_of_hdimEq`:179,
  `rees_hdepth_of_hdimEqMin`:197,
  `rees_hunmixed_general_of_hkerMin`:212,
  `rees_hunmixed_general_of_hdimEqMin`:230,
  `rees_heightDrop_general_of_hkerMin`:248.

## Impact on Rees inputs

* `hpiece` closed + integrated (HSDegree §5; HSIntegrate:85/:102/
  :121): serves the `hdimEq` input to Rees (gap-rees-9), not Rees
  proper — C1–C4 go through `hker`/R2, never through HS degree
  comparison. Now re-estimated through §1 (this file).
* `hF` unconditional (GrExact:130/:156) + `hne`-on-`hker`
  (GrExact §§2–3) + `HhsDegLowerD2` unconditional (GrExact:365):
  new `d = 2` legs for the gap-rees-9 slice (§§1–2).
* D2 joints (HighD2Close §2): cheapest `HkerD2` leg
  (`highD2Close_hkerD2_of_sopGrLowerGated`:253) feeds the
  slice (§2) — gated form only; the ungated
  `HsopGrLowerD2AtAss` (HighAttack:667) is false as stated
  (witness `J = ⊥`, `Q = ⊥`, `x = 0`; formal refutation still
  open, owned outside Rees) and is never consumed here.
* `minSubAss` unconditional (`MinSubsetAss.minSubAss_all`:232):
  no Rees change (the Min `d`-split needs no `hmin`; pair
  `hmin1` was already closed).
* NoetherGe negative (`NoetherLowerAttack.lean` §4, per-prime iff
  :249): the Noether route does not close `hdimEq`
  unconditionally — confirms the `Ge3` residual stays scoped as
  crux (Noether/High@Ge3 addresses), not as a Rees-side gap.

## What this file proves

* (§1) `HdimEqMinGe3AtAss` SPEC + the Newton core
  `rees_hdimEqMin_d2_of_grExactD2` (`d = 2` slice of
  `HdimEqMinAtAss` on `[HgrExactD2AtAss]`) +
  `rees_ge3_of_hdimEqMin` (restriction, unconditional form).
* (§2) Full-`HdimEqMinAtAss` masters on `[grExactD2, ge3]`,
  `[hkerD2, ge3]`, `[gated, ge3]` (the last is the mod-crux
  master).
* (§3) Rees delivery on `[grExactD2, ge3]`: `HkerMin`,
  per-prime depth, general-`k` unmixedness + height-drop.
* (§4) Ring joint `HgrExactD2 ⟺ HkerD2` (unconditional iff)
  + cheapest-leg delivery on `[gated, ge3]`.
* (§5, doc-only) Residual register + verdict.

## Status

* §1: `HdimEqMinGe3AtAss` SPEC; `rees_hdimEqMin_d2_of_grExactD2`
  conditional-exact on `[HgrExactD2AtAss]`;
  `rees_ge3_of_hdimEqMin` unconditional (conditional-form).
* §2: masters conditional-exact on the named inputs.
* §3: conditional-exact on `[HgrExactD2AtAss,
  HdimEqMinGe3AtAss]`.
* §4: `rees_hkerD2_of_grExactD2` conditional-exact on
  `[HgrExactD2AtAss]`; `rees_grExactD2_iff_hkerD2`
  unconditional (iff); delivery conditional-exact on
  `[HsopGrLowerD2GatedAtAss, HdimEqMinGe3AtAss]`.

## References

Project (read-only): `Regularity/Rees/ReesProbe.lean` (gap-rees
survey + §2 wires), `Regularity/Koszul/GradedExactEmbDimTwo.lean` (§§1–3 `hF`/
`hne`/`grExactD2`, §6 `hsDegLowerD2`:365),
`Regularity/Multiplicity/PieceIntegration.lean` (:85/:102/:121),
`Regularity/Multiplicity/DimTwoEndToEnd.lean` (gated SPEC:147, §2 joints,
iff:379, joint-9:485), `Regularity/Multiplicity/WitnessHighAttack.lean` (§4
SPECs), `Regularity/HomologicalDepth/WitnessKernelDimTwo.lean` (D2 ring),
`Regularity/Multiplicity/NewtonDifferences.lean` (`lt_natDegree_of_not_eventuallyEq_zero`
:452), `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`:309, Min
`d`-split:354), `BridgeToFixedPoint/MinAvoid/MinSubsetAss.lean` (`minSubAss_all`:232).

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ReesClose

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ReesProbe
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactEmbDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PieceIntegration
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimTwoEndToEnd
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. Gap-rees-9 `d = 2` slice: Newton core + `Ge3` residual SPEC -/

/-- Universal `hdimEq` over `Ass(R ⧸ J)` at minimal `d ≥ 3` only: the
`Ge3` slice of `HdimEqMinAtAss` (`UnmixednessAtLengthTwo.lean`) — same body,
`3 ≤ d` in place of `2 ≤ d`. This is the exact surviving residual of
gap-rees-9 once the `d = 2` slice closes (§1 core below).

Specification (Prop address for the `Ge3` exact-degree hypothesis). -/
def HdimEqMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
    3 ≤ d →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
        (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Qw →
        Qw.natDegree = d - 1

/-- The `d = 2` slice of `HdimEqMinAtAss`, closed on gr-exact data
(Newton core): at embdim 2, `deg Qw ≤ 1` plus first-difference
nonvanishing (`hne` of `HgrExactD2AtAss`) forces `deg Qw = 1` — a
degree-0 approximant would make `ΔH_gr` eventually zero
(`lt_natDegree_of_not_eventuallyEq_zero` at `d := 0`). The `hF`
conjunct is not needed.

Conditional on exactly `[HgrExactD2AtAss]`. -/
theorem rees_hdimEqMin_d2_of_grExactD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hdmin : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (_hd2 : 2 ≤ 2)
    (Qw : Polynomial ℚ) (hle : Qw.natDegree ≤ 2 - 1)
    (hag : (fun n => ((SingleDropRegularity.singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Qw) :
    Qw.natDegree = 2 - 1 := by
  obtain ⟨_, hne⟩ := hgrExact Q hQ hdmin
  have hpos : 0 < Qw.natDegree :=
    lt_natDegree_of_not_eventuallyEq_zero Qw 0 hag hne
  omega

/-- The `Ge3` slice is weaker than full `HdimEqMinAtAss` (restriction:
`3 ≤ d` implies `2 ≤ d`).
-/
theorem rees_ge3_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : HdimEqMinAtAss m K J) :
    HdimEqMinGe3AtAss m K J := by
  intro Q _ hQ d hdmin hd3 Qw hle hag
  exact hdimEq Q hQ hdmin (by omega) Qw hle hag

/-! ## §2. Full-`HdimEqMinAtAss` masters -/

/-- Full `HdimEqMinAtAss` on `[HgrExactD2AtAss,
HdimEqMinGe3AtAss]`: the `d = 2` case is the §1 core, the `d ≥ 3`
case is the named residual.

Conditional on exactly `[hgrExact, hge3]`. -/
theorem rees_hdimEqMin_of_grExactD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J := by
  intro Q _ hQ d hdmin hd2 Qw hle hag
  by_cases hd : d = 2
  · subst hd
    exact rees_hdimEqMin_d2_of_grExactD2 m K J hgrExact Q hQ hdmin hd2
      Qw hle hag
  · have hd3 : 3 ≤ d := by omega
    exact hge3 Q hQ hdmin hd3 Qw hle hag

/-- Full `HdimEqMinAtAss` on `[HkerD2AtAss,
HdimEqMinGe3AtAss]`: the §1 core fed with the GrExact-§3 supply
(`grExact_grExactD2_of_hkerD2`).

Conditional on exactly `[hker, hge3]`. -/
theorem rees_hdimEqMin_of_hkerD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  rees_hdimEqMin_of_grExactD2_ge3 m K J
    (grExact_grExactD2_of_hkerD2 m K J hker) hge3

/-- Full `HdimEqMinAtAss` on `[HsopGrLowerD2GatedAtAss,
HdimEqMinGe3AtAss]`: the `HkerD2` leg fed with the cheapest D2
joint (`highD2Close_hkerD2_of_sopGrLowerGated`). The mod-crux
master (both inputs crux-ring forms).

Conditional on exactly `[hgr, hge3]`. -/
theorem rees_hdimEqMin_of_sopGrLowerGated_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  rees_hdimEqMin_of_hkerD2_ge3 m K J
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr) hge3

/-! ## §3. Rees delivery on `[grExactD2, ge3]` -/

/-- Universal minimal `hker` on `[HgrExactD2AtAss,
HdimEqMinGe3AtAss]`: the Min `d`-split
(`hkerMinAtAss_of_hdimEqMin`) fed with the §2 master.

Conditional on exactly `[hgrExact, hge3]`. -/
theorem rees_hkerMin_of_grExactD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    HkerMinAtAss m K J :=
  hkerMinAtAss_of_hdimEqMin m K J
    (rees_hdimEqMin_of_grExactD2_ge3 m K J hgrExact hge3)

/-- Universal `hdepth` on `[HgrExactD2AtAss,
HdimEqMinGe3AtAss]`: the Rees end-to-end output
(`rees_hdepth_of_hdimEqMin`) fed with the §2 master.

Conditional on exactly `[hgrExact, hge3]`. -/
theorem rees_hdepth_of_grExactD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  rees_hdepth_of_hdimEqMin m K J
    (rees_hdimEqMin_of_grExactD2_ge3 m K J hgrExact hge3) Q hQ

/-- General-`k` unmixedness on `[HgrExactD2AtAss,
HdimEqMinGe3AtAss]`: the Rees geometry delivery
(`rees_hunmixed_general_of_hdimEqMin`) fed with the §2 master.

Conditional on exactly `[hgrExact, hge3]` (at `J`; general
`k`). -/
theorem rees_hunmixed_general_of_grExactD2_ge3 (m : ℕ) (K : Type*)
    [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes :=
  rees_hunmixed_general_of_hdimEqMin m K q hsucc J hJ
    (rees_hdimEqMin_of_grExactD2_ge3 m K J hgrExact hge3)

/-- General-`k` height-drop on `[HgrExactD2AtAss,
HdimEqMinGe3AtAss]`: `rees_heightDrop_general_of_hkerMin` fed
with the §3 `hker` wire.

Conditional on exactly `[hgrExact, hge3]` (at `J`; general
`k`). -/
theorem rees_heightDrop_general_of_grExactD2_ge3 (m : ℕ) (K : Type*)
    [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ :=
  rees_heightDrop_general_of_hkerMin m K q hsucc J hJ
    (rees_hkerMin_of_grExactD2_ge3 m K J hgrExact hge3)

/-! ## §4. D2 ring joint + cheapest-leg delivery -/

/-- `HkerD2AtAss` from gr-exact data alone: the HSIntegrate:121
joint (`hsIntegrate_hwitD2_of_grExact_hsDeg`) with the
unconditional `hhsDeg` supply (`grExact_hsDegLowerD2`), projected
through the D2 ring (`hwitD2_iff_hkerD2`). Together with
GrExact §3 this closes the `HgrExactD2 ⟺ HkerD2` loop.

Conditional on exactly `[hgrExact]`. -/
theorem rees_hkerD2_of_grExactD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J) :
    HkerD2AtAss m K J :=
  (hwitD2_iff_hkerD2 m K J).mp
    (hsIntegrate_hwitD2_of_grExact_hsDeg m K J hgrExact
      (grExact_hsDegLowerD2 m K J))

/-- Gr-exact data is exactly `ker = ⊥` strength at embdim 2: it
joins the D2 ring (forward §4 above, backward GrExact §3).
-/
theorem rees_grExactD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrExactD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨rees_hkerD2_of_grExactD2 m K J,
    grExact_grExactD2_of_hkerD2 m K J⟩

/-- Universal minimal `hker` on the cheapest legs
(`[HsopGrLowerD2GatedAtAss, HdimEqMinGe3AtAss]`): the Min
`d`-split fed with the §2 mod-crux master.

Conditional on exactly `[hgr, hge3]`. -/
theorem rees_hkerMin_of_sopGrLowerGated_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    HkerMinAtAss m K J :=
  hkerMinAtAss_of_hdimEqMin m K J
    (rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr hge3)

/-- Universal `hdepth` on the cheapest legs: the Rees end-to-end
output fed with the §2 mod-crux master.

Conditional on exactly `[hgr, hge3]`. -/
theorem rees_hdepth_of_sopGrLowerGated_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  rees_hdepth_of_hdimEqMin m K J
    (rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr hge3) Q hQ

/-- General-`k` unmixedness on the cheapest legs: the Rees
geometry delivery fed with the §2 mod-crux master. The mod-crux
geometry master.

Conditional on exactly `[hgr, hge3]` (at `J`; general `k`). -/
theorem rees_hunmixed_general_of_sopGrLowerGated_ge3 (m : ℕ)
    (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HdimEqMinGe3AtAss m K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes :=
  rees_hunmixed_general_of_hdimEqMin m K q hsucc J hJ
    (rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr hge3)

/-! ## §5. Residual register + verdict (doc-only)

exact residual of the Rees route, post-reprice (verbatim):

* `HsopGrLowerD2GatedAtAss` (gated `d = 2` s.o.p.-to-gr): closes
  the `d = 2` slice of gap-rees-9 (§§1–2) by one `exact` per
  master. Crux-ring form (iff `HkerD2AtAss`, HighD2Close:379).
* `HdimEqMinGe3AtAss` (§1 SPEC: the `d ≥ 3` slice of
  `HdimEqMinAtAss`): closes the remainder (§2 masters) by one
  `exact`. Crux-ring form (restriction of the joint-9
  `HdimEqMinAtAss`, HighD2Close:485).
* `HgrExactD2AtAss` (gr-exact data): joins the D2 ring (§4 iff),
  so the `[grExactD2, ge3]` conditionings (§§2–3) are
  same-strength as the cheapest `[gated, ge3]` legs (§§2, 4) —
  no narrower Rees-side conditioning exists (`hne ⟺ hmult ⟺
  ker = ⊥` by `kwit_hmult_iff_ker_eq_bot`).

why the residual is minimal and exact (all machine-checked):

* The §4 iff shows the §1 core's input is exactly `ker = ⊥`
  strength at embdim 2; the HighD2Close:379 iff shows the
  cheapest leg is too. Neither can be weakened below ring
  strength (unconditional `d = 2` below `ker = ⊥` is OUT of
  reach).
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any
  growth fact beyond the cited suppliers to prove the §§1–4
  masters; the only undischarged inputs are the two residuals
  themselves.

verdict (audited): Rees closes mod crux-only. Every Rees
condition (C1–C4, sop data, basis, tfae sides, end-to-end depth,
`d`-split, Min-scope general-`k` geometry) is proved; the sole
open input gap-rees-9 now closes on two crux-ring remainders.
No non-crux gap survives — no gap-rees-10. The `Ge3` residual
(gap-rees-9′) is owned by the crux work (Noether/High@Ge3
addresses); the gated `d = 2` residual is the D2 crux form.

consumers: any proof of the two residuals discharges
every Rees output (§§2–4) by single `exact`s; any `Ge3`
proof composes with any D2-ring form via the §2 masters.
-/

#print axioms rees_hdimEqMin_d2_of_grExactD2
#print axioms rees_ge3_of_hdimEqMin
#print axioms rees_hdimEqMin_of_grExactD2_ge3
#print axioms rees_hdimEqMin_of_hkerD2_ge3
#print axioms rees_hdimEqMin_of_sopGrLowerGated_ge3
#print axioms rees_hkerMin_of_grExactD2_ge3
#print axioms rees_hdepth_of_grExactD2_ge3
#print axioms rees_hunmixed_general_of_grExactD2_ge3
#print axioms rees_heightDrop_general_of_grExactD2_ge3
#print axioms rees_hkerD2_of_grExactD2
#print axioms rees_grExactD2_iff_hkerD2
#print axioms rees_hkerMin_of_sopGrLowerGated_ge3
#print axioms rees_hdepth_of_sopGrLowerGated_ge3
#print axioms rees_hunmixed_general_of_sopGrLowerGated_ge3

end ReesClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
