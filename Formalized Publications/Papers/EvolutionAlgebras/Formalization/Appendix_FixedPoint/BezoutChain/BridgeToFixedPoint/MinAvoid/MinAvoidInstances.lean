/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.SuccFeedClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.RungOneDiagonalDischarge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.NonprimeAttack
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.NonprimeClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.JointAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge

/-!
# Nonprime `minAvoid` at consumer instances
The general-`c` SPEC is dead (S5 `c = 0` witness): this lane takes
the instance route. Recon first: every `hass`/`hsucc` consumer that
still names a `minAvoid` input is audited for exactly which instances
it needs it at; then `MinAvoidNonprimeSpec` is attacked at those
instances (unconditional where possible, else witnessed-narrowed to
an exact per-instance residual). Foundation: the S5 iff (exact per-`(j, Q)` address) and the S3
verdict shape (step-strength — cited, never consumed: `HdimEqMinAtAss` appears in
this file only as a downstream consumer binder, never as a lever to
conclude anything upstream of it).

## Recon verdict (unconditional)

The consumers needing `minAvoid` are: S4 `SuccFeedClose` §1
(general-`c` masters), §2 (instance masters at `cDiagOnes`/Gap),
RUNG1 `RungOneJoin` (instance masters at `cDiagOnes`/Gap/`n = 1`),
S1-allocator instance masters (`MinAvoidJoin` §3/§4), and the J9
plug (`SuccFeedClose`, general `c`). Prime-single is
closed unconditionally at general `c` (S2), so every consumer's
`minAvoid` leg is exactly `MinAvoidNonprimeSpec` at its instance
(§1 recon iffs). Instance-by-instance:

* general `c` (S4 §1 masters, J9 plug): dead uniformly — the S5
  witness refutes `∀ c, SPEC` at every `n ≥ 3`; the J9-plug
  pair leg is refuted uniformly (§1). Residual: the exact
  per-`(j, Q)` obligations (S5), not uniformly closable.
* `cDiagOnes` (all `n`): open — exact per-`(j, Q)` address (§2),
  gated only on rung data (nonprime steps / nonprime `hass`).
* Gap `diagWitness` (`n = 3`): open — collapses to a single rung-2
  per-`Q` obligation (§3, unconditional iff onto `GapRung2Residual`).
* `n = 1`: closed unconditional (S3 vacuity, cited).

## What is proved here

* §1 recon: `AllSpec ⟺ NonprimeSpec` at `cDiagOnes`/Gap (S2 iff
  instantiated); `n = 1` nonprime closed (S3); no-uniform-SPEC (S5);
  J9-plug pair leg not uniform (S5 zero refutation).
* §2 `cDiagOnes`: exact address (S5); SPEC from
  nonprime-steps / nonprime-`hass` (S5); single
  non-membership (S2 — single holds, minimal open).
* §3 Gap: the same four at `diagWitness`, plus the unconditional
  single-rung collapse (`SPEC ⟺ GapRung2Residual`) and its per-`Q`
  unfolding (`rfl`).
* §4 re-fires: all 4 RUNG1 instance masters, all 4 S1-allocator
  instance masters, all 4 S4 §2 instance masters, and the J9 plug
  — each narrowed to nonprime-only `minAvoid` input (S2
  discharge). No other lane owns these narrowings (S2 re-fired only
  the 2 general-`c` S1 masters).

Status: instance route settled (recon exact;
`cDiagOnes`/Gap narrowed to sharp per-instance residuals with
rung-data gates; `n = 1` closed; general `c` witnessed-dead;
13 consumer re-fires on nonprime-only input).

## Residual register (verbatim)

closed this lane: [consumer-instance recon (exact addresses)];
[`cDiagOnes` SPEC = per-`(j, Q)` obligations + rung-data gates];
[Gap SPEC = single rung-2 per-`Q` residual + rung-data gates];
[13 re-fires on nonprime-only input (RUNG1/S1/S4 instances,
J9 plug)]. Open (exact): [`MinAvoidNonprimeSpec` at `cDiagOnes`
(per-`(j, Q)` obligations — sharp residual)]; [`GapRung2Residual`
(single rung-2 per-`Q` obligation — sharp residual)]; [general-`c`
SPEC — dead uniformly (S5 witness), per-`(j, Q)` obligations stay
open per `c`]; [rung-1 local gates per instance `c` (in HD2)];
[the per-stage `d ≥ 2` allocator = the crux ].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidJoin` (SPECs),
`BridgeToFixedPoint/PrimeSingleClose` (S2 close + iff + single),
`BridgeToFixedPoint/NonprimeClose` (S3 `n = 1` vacuity),
`BridgeToFixedPoint/NonprimeAttack` (S5 iff + reductions +
refutations), `BridgeToFixedPoint/RungOneJoin` (RUNG1 instance masters),
`BridgeToFixedPoint/SuccFeedClose` (S4 §2 masters + J9 plug),
`BridgeToFixedPoint/RungOneDiagonalDischarge` (`cDiagOnes` + rung-1 gates),
`BridgeToFixedPoint/RungDiagonalGap` (`diagWitness`),
`BridgeToFixedPoint/MinAvoidRungs` (stage ideals + minimal forms),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`, `statementIndex`,
`shift_add_one`), `Geometry/UnmixednessAtLengthTwo` (downstream `hdimEq`
binder), `Regularity/SingleAllocator` (allocator binder),
`Regularity/JointAssembly` (`Hdich` binder),
`Regularity/WitnessHighAttack` (`d2`/`ge3` binders),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`). No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoid/MinAvoidJoin.lean` (nonprime SPEC, splitter).
* `BridgeToFixedPoint/MinAvoid/PrimeSingleClose.lean`
  (single, prime close, `AllSpec ⟺ nonprime`).
* `BridgeToFixedPoint/MinAvoid/NonprimeClose.lean` (S3 verdict
  shape — cited only; `n = 1` vacuity).
* `BridgeToFixedPoint/MinAvoid/NonprimeAttack.lean/:
  533` (address iff, reductions, zero refutations).
* `BridgeToFixedPoint/Rung/RungOneJoin.lean` (RUNG1 instance
  masters).
* `BridgeToFixedPoint/AssumptionFeeds/SuccFeedClose.lean` (S4
  instance masters + J9 plug).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAvoidInstances

/-! ## §1. Recon: exactly which instances need `minAvoid` -/

/-- Recon at `cDiagOnes` (unconditional): every consumer's full
`minAvoid` obligation at the all-ones-diagonal family is the
nonprime SPEC there — the S2 iff instantiated (prime
stages discharged by the S2 close).
-/
theorem recon_allSpec_iff_nonprime_cDiagOnes (n : ℕ) (K : Type*)
    [Field K] (hn : 0 < n) :
    MinAvoidJoin.MinAvoidAllSpec n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn ↔
      MinAvoidJoin.MinAvoidNonprimeSpec n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn :=
  PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K _ hn

#print axioms recon_allSpec_iff_nonprime_cDiagOnes

/-- Recon at the Gap witness (unconditional): every consumer's full
`minAvoid` obligation at `diagWitness` is the nonprime SPEC there.
-/
theorem recon_allSpec_iff_nonprime_gap (K : Type*) [Field K]
    (hn : 0 < 3) :
    MinAvoidJoin.MinAvoidAllSpec 3 K
        (RungDiagonalGap.diagWitness K) hn ↔
      MinAvoidJoin.MinAvoidNonprimeSpec 3 K
        (RungDiagonalGap.diagWitness K) hn :=
  PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin 3 K _ hn

#print axioms recon_allSpec_iff_nonprime_gap

/-- Recon at `n = 1` (unconditional): the nonprime SPEC is vacuous —
the S3 close. The `n = 1` consumer instance is done.
-/
theorem recon_n1_nonprime_closed (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    MinAvoidJoin.MinAvoidNonprimeSpec 1 K c hn :=
  NonprimeClose.minAvoidNonprimeSpec_n1_vacuous K c hn

#print axioms recon_n1_nonprime_closed

/-- Recon for general `c` (unconditional): no uniform close exists —
the S5 witness (`c = 0` refutes the SPEC at every `n ≥ 3`).
The S4 §1 general-`c` masters keep an exact per-`c` residual.
-/
theorem recon_no_uniform_nonprime (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) (h3 : 3 ≤ n) :
    ¬ ∀ c : Fin n → Fin n → Fin n → K,
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  NonprimeAttack.minAvoidNonprimeSpec_not_forall n K hn h3

#print axioms recon_no_uniform_nonprime

/-- Recon for the J9 plug (unconditional): its
`[hprime, hnonprime]` pair leg cannot close uniformly — prime
closes (S2) but nonprime fails at `c = 0` (S5), so the
pair fails. The plug keeps an exact per-`c` nonprime residual.
-/
theorem recon_j9plug_pair_not_uniform (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (h3 : 3 ≤ n) :
    ¬ ∀ c : Fin n → Fin n → Fin n → K,
      MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn ∧
        MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  intro hall
  exact NonprimeAttack.not_minAvoidNonprimeSpec_zero
    n K hn h3 (hall _).2

#print axioms recon_j9plug_pair_not_uniform

/-! ## §2. `cDiagOnes` instance: exact address + rung-data gates -/

/-- Exact per-`(j, Q)` address at `cDiagOnes` (unconditional): the
S5 iff instantiated — the sharp residual at this instance.
-/
theorem nonprimeSpec_cDiagOnes_iff_mem (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn ↔
      (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        ¬ (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j).IsPrime →
        ∀ Q ∈ (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j).minimalPrimes,
          (bridgeSystem n K
            (RungOneDiagonalDischarge.cDiagOnes n K) hn) j ∉ Q) :=
  NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem n K _ hn

#print axioms nonprimeSpec_cDiagOnes_iff_mem

/-- `cDiagOnes` SPEC from nonprime-stage steps only
(unconditional reduction): the S5 narrowing instantiated.
-/
theorem nonprime_cDiagOnes_of_stepsNonprime (n : ℕ) (K : Type*)
    [Field K] (hn : 0 < n)
    (hsteps : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K
            (RungOneDiagonalDischarge.cDiagOnes n K) hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn) j)) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn :=
  NonprimeAttack.minAvoidNonprime_of_stepsNonprime n K _ hn
    hsteps

#print axioms nonprime_cDiagOnes_of_stepsNonprime

/-- `cDiagOnes` SPEC from nonprime-stage `hass` only
(unconditional reduction): the S5 narrowing instantiated.
-/
theorem nonprime_cDiagOnes_of_hassNonprime (n : ℕ) (K : Type*)
    [Field K] (hn : 0 < n)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j).IsPrime →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn :=
  NonprimeAttack.minAvoidNonprime_of_hassNonprime n K _ hn
    hass

#print axioms nonprime_cDiagOnes_of_hassNonprime

/-- Single non-membership at `cDiagOnes` (unconditional): the S2
triangular specialization instantiated — the single holds,
minimality stays open (the gap shape at this instance).
-/
theorem single_cDiagOnes (n : ℕ) (K : Type*) [Field K] (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) j ∉
      MinAvoidRungs.stageIdeal n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  PrimeSingleClose.bridgeSystem_notMem_stageIdeal n K _ hn j

#print axioms single_cDiagOnes

/-! ## §3. Gap instance: single-rung collapse + rung-data gates -/

/-- Exact per-`(j, Q)` address at the Gap witness
(unconditional): the S5 iff instantiated.
-/
theorem nonprimeSpec_gap_iff_mem (K : Type*) [Field K] (hn : 0 < 3) :
    MinAvoidJoin.MinAvoidNonprimeSpec 3 K
        (RungDiagonalGap.diagWitness K) hn ↔
      (∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
        ¬ (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j).IsPrime →
        ∀ Q ∈ (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j).minimalPrimes,
          (bridgeSystem 3 K
            (RungDiagonalGap.diagWitness K) hn) j ∉ Q) :=
  NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem 3 K _ hn

#print axioms nonprimeSpec_gap_iff_mem

/-- Gap SPEC from nonprime-stage steps only (unconditional
reduction): the S5 narrowing instantiated.
-/
theorem nonprime_gap_of_stepsNonprime (K : Type*) [Field K]
    (hn : 0 < 3)
    (hsteps : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal 3 K
        (RungDiagonalGap.diagWitness K) hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸
          (MinAvoidRungs.stageIdeal 3 K
            (RungDiagonalGap.diagWitness K) hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
            (MvPolynomial (Fin (statementIndex 3 + 2)) K))))
        ((bridgeSystem 3 K
          (RungDiagonalGap.diagWitness K) hn) j)) :
    MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn :=
  NonprimeAttack.minAvoidNonprime_of_stepsNonprime 3 K _ hn
    hsteps

#print axioms nonprime_gap_of_stepsNonprime

/-- Gap SPEC from nonprime-stage `hass` only (unconditional
reduction): the S5 narrowing instantiated.
-/
theorem nonprime_gap_of_hassNonprime (K : Type*) [Field K]
    (hn : 0 < 3)
    (hass : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal 3 K
        (RungDiagonalGap.diagWitness K) hn j).IsPrime →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn :=
  NonprimeAttack.minAvoidNonprime_of_hassNonprime 3 K _ hn
    hass

#print axioms nonprime_gap_of_hassNonprime

/-- Single non-membership at the Gap witness (unconditional): the
S2 triangular specialization instantiated.
-/
theorem single_gap (K : Type*) [Field K] (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) :
    (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) j ∉
      MinAvoidRungs.stageIdeal 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  PrimeSingleClose.bridgeSystem_notMem_stageIdeal 3 K _ hn j

#print axioms single_gap

/-- The unique rung-`≥ 2` index at `n = 3` (unconditional):
`Fin (statementIndex 3 + 1) = Fin 3`, so `2 ≤ j.val` forces
`j = gapRung2`.
-/
def gapRung2 (hn : 0 < 3) : Fin (statementIndex 3 + 1) :=
  ⟨2, by have hidx : statementIndex 3 + 1 = 3 :=
    shift_add_one 3 hn; omega⟩

#print axioms gapRung2

/-- The exact per-instance residual at the Gap witness: the single
rung-2 obligation — if the rung-2 stage ideal is nonprime, the
fixed rung-2 element avoids every minimal prime over it. This is
the witnessed-narrowed remainder of `MinAvoidNonprimeSpec` at
`diagWitness` (collapse below is unconditional).
-/
def GapRung2Residual (K : Type*) [Field K] (hn : 0 < 3) : Prop :=
  ¬ (MinAvoidRungs.stageIdeal 3 K (RungDiagonalGap.diagWitness K) hn
    (gapRung2 hn)).IsPrime →
    MinAvoidRungs.MinAvoidRung 3 K (RungDiagonalGap.diagWitness K) hn
      (gapRung2 hn)

#print axioms GapRung2Residual

/-- Single-rung collapse at the Gap witness (unconditional): the
SPEC `⟺` the rung-2 residual — `Fin 3` has exactly one index
with `2 ≤ val`, so the `∀`-binder is one obligation.
-/
theorem nonprimeSpec_gap_iff_rung2Residual (K : Type*) [Field K]
    (hn : 0 < 3) :
    MinAvoidJoin.MinAvoidNonprimeSpec 3 K
        (RungDiagonalGap.diagWitness K) hn ↔
      GapRung2Residual K hn := by
  have hidx : statementIndex 3 + 1 = 3 := shift_add_one 3 hn
  have hj2 : 2 ≤ (gapRung2 hn).val := by
    have h2 : (gapRung2 hn).val = 2 := rfl
    omega
  constructor
  · intro h hP
    exact h (gapRung2 hn) hj2 hP
  · intro h j hj hP
    have hlt := j.isLt
    have hval : j.val = 2 := by omega
    have h2 : (gapRung2 hn).val = 2 := rfl
    have heq : j = gapRung2 hn := Fin.ext (by omega)
    subst heq
    exact h hP

#print axioms nonprimeSpec_gap_iff_rung2Residual

/-- The Gap residual unfolded to per-`Q` form (unconditional,
`rfl`-level): the single rung-2 obligation with `MinAvoidRung`
inlined — the sharpest address of the Gap remainder.
-/
theorem gapRung2Residual_unfold (K : Type*) [Field K] (hn : 0 < 3) :
    GapRung2Residual K hn ↔
      (¬ (MinAvoidRungs.stageIdeal 3 K (RungDiagonalGap.diagWitness K) hn
        (gapRung2 hn)).IsPrime →
        ∀ Q ∈ (MinAvoidRungs.stageIdeal 3 K (RungDiagonalGap.diagWitness K)
          hn (gapRung2 hn)).minimalPrimes,
          (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
            (gapRung2 hn) ∉ Q) :=
  Iff.rfl

#print axioms gapRung2Residual_unfold

/-! ## §4. Consumer re-fires on nonprime-only input -/

/-- RUNG1 re-fired on nonprime-only `minAvoid`: full
`hass_all` at `cDiagOnes` from `[∀-HdimEq, nonprime-minimal]`
(the S2 iff feeds the unfolded `hmin` binder
definitionally).

Conditional on exactly `[hdimEq, hnonprime]`. -/
theorem hass_all_cDiagOnes_of_hdimEq_of_nonprimeMin (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
            {k | k.val < j.val})))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  RungOneJoin.hass_all_cDiagOnes_of_hdimEq_of_minAvoid K n hn hdimEq
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K _
      hn).mpr hnonprime)

#print axioms hass_all_cDiagOnes_of_hdimEq_of_nonprimeMin

/-- RUNG1 re-fired on nonprime-only `minAvoid`: full
`hass_all` at the Gap witness from `[∀-HdimEq,
nonprime-minimal]`.

Conditional on exactly `[hdimEq, hnonprime]`. -/
theorem hass_all_gap_of_hdimEq_of_nonprimeMin (K : Type*) [Field K]
    (hn : 0 < 3)
    (hdimEq : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
            {k | k.val < j.val})))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  RungOneJoin.hass_all_gap_of_hdimEq_of_minAvoid K hn hdimEq
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin 3 K _
      hn).mpr hnonprime)

#print axioms hass_all_gap_of_hdimEq_of_nonprimeMin

/-- RUNG1 re-fired on nonprime-only `minAvoid`: full
`hsucc` at `cDiagOnes` from `[∀-HdimEq, nonprime-minimal]`.

Conditional on exactly `[hdimEq, hnonprime]`. -/
theorem hsucc_cDiagOnes_of_hdimEq_of_nonprimeMin (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
            {k | k.val < j.val})))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) :=
  RungOneJoin.hsucc_cDiagOnes_of_hdimEq_of_minAvoid K n hn hdimEq
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K _
      hn).mpr hnonprime)

#print axioms hsucc_cDiagOnes_of_hdimEq_of_nonprimeMin

/-- RUNG1 re-fired on nonprime-only `minAvoid`: full
`hsucc` at the Gap witness from `[∀-HdimEq, nonprime-minimal]`.

Conditional on exactly `[hdimEq, hnonprime]`. -/
theorem hsucc_gap_of_hdimEq_of_nonprimeMin (K : Type*) [Field K]
    (hn : 0 < 3)
    (hdimEq : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
            {k | k.val < j.val})))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) :=
  RungOneJoin.hsucc_gap_of_hdimEq_of_minAvoid K hn hdimEq
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin 3 K _
      hn).mpr hnonprime)

#print axioms hsucc_gap_of_hdimEq_of_nonprimeMin

/-- S1 re-fired on nonprime-only `minAvoid`: full `hass_all`
at `cDiagOnes` from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hass_all_cDiagOnes_of_alloc_of_nonprimeMin (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  MinAvoidJoin.hass_all_cDiagOnes_of_alloc_of_minAvoid K n hn
    halloc
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K _
      hn).mpr hnonprime)

#print axioms hass_all_cDiagOnes_of_alloc_of_nonprimeMin

/-- S1 re-fired on nonprime-only `minAvoid`: full `hass_all`
at the Gap witness from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hass_all_gap_of_alloc_of_nonprimeMin (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  MinAvoidJoin.hass_all_gap_of_alloc_of_minAvoid K hn halloc
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin 3 K _
      hn).mpr hnonprime)

#print axioms hass_all_gap_of_alloc_of_nonprimeMin

/-- S1 re-fired on nonprime-only `minAvoid`: full `hsucc`
at `cDiagOnes` from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hsucc_cDiagOnes_of_alloc_of_nonprimeMin (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) :=
  MinAvoidJoin.hsucc_cDiagOnes_of_alloc_of_minAvoid K n hn halloc
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K _
      hn).mpr hnonprime)

#print axioms hsucc_cDiagOnes_of_alloc_of_nonprimeMin

/-- S1 re-fired on nonprime-only `minAvoid`: full `hsucc`
at the Gap witness from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hsucc_gap_of_alloc_of_nonprimeMin (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) :=
  MinAvoidJoin.hsucc_gap_of_alloc_of_minAvoid K hn halloc
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin 3 K _
      hn).mpr hnonprime)

#print axioms hsucc_gap_of_alloc_of_nonprimeMin

/-- S4 re-fired on nonprime-only `minAvoid`: full `hass_all`
at `cDiagOnes` from `[per-stage allocator, nonprime-minimal]` (the
S2 close discharges `hprime`).

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hassFeed_all_cDiagOnes_of_alloc_of_nonprimeMin (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  SuccFeedClose.hassFeed_all_cDiagOnes_of_alloc_of_pair K n hn
    halloc
    (PrimeSingleClose.minAvoidPrimeSingleSpec_unconditional
      n K _ hn)
    hnonprime

#print axioms hassFeed_all_cDiagOnes_of_alloc_of_nonprimeMin

/-- S4 re-fired on nonprime-only `minAvoid`: full `hass_all`
at the Gap witness from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hassFeed_all_gap_of_alloc_of_nonprimeMin (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  SuccFeedClose.hassFeed_all_gap_of_alloc_of_pair K hn halloc
    (PrimeSingleClose.minAvoidPrimeSingleSpec_unconditional
      3 K _ hn)
    hnonprime

#print axioms hassFeed_all_gap_of_alloc_of_nonprimeMin

/-- S4 re-fired on nonprime-only `minAvoid`: full `hsucc`
at `cDiagOnes` from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hsuccFeed_cDiagOnes_of_alloc_of_nonprimeMin (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) :=
  SuccFeedClose.hsuccFeed_cDiagOnes_of_alloc_of_pair K n hn halloc
    (PrimeSingleClose.minAvoidPrimeSingleSpec_unconditional
      n K _ hn)
    hnonprime

#print axioms hsuccFeed_cDiagOnes_of_alloc_of_nonprimeMin

/-- S4 re-fired on nonprime-only `minAvoid`: full `hsucc`
at the Gap witness from `[per-stage allocator, nonprime-minimal]`.

Conditional on exactly `[halloc, hnonprime]`. -/
theorem hsuccFeed_gap_of_alloc_of_nonprimeMin (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) :=
  SuccFeedClose.hsuccFeed_gap_of_alloc_of_pair K hn halloc
    (PrimeSingleClose.minAvoidPrimeSingleSpec_unconditional
      3 K _ hn)
    hnonprime

#print axioms hsuccFeed_gap_of_alloc_of_nonprimeMin

/-- J9 plug re-fired on nonprime-only `minAvoid`: full
`hsucc` via J9 from `[hdich, d2∀, ge3∀, local, supp, alloc,
nonprime]` (the S2 close discharges the plug's `hprime`
leg; the `hnonprime` leg stays exact per `c` — §1 shows it
cannot close uniformly).

Conditional on exactly `[hdich, d2∀, ge3∀, local, supp,
halloc, hnonprime]` (plug certificate). -/
theorem plug_j9_hsucc_of_hdich_of_d2_ge3_of_nonprimeMin (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdich : JointAssembly.HdichRung1 n K c hn)
    (hd2 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      WitnessHighAttack.HnoHomRelHighD2AtAss (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})))
    (hge3 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      WitnessHighAttack.HnoHomRelHighMinGe3AtAss
        (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})))
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccFeedClose.plug_j9_hsucc_of_hdich_of_d2_ge3_of_feed
    K n hn c hdich hd2 hge3 hdiag hsupp halloc
    (PrimeSingleClose.minAvoidPrimeSingleSpec_unconditional
      n K c hn)
    hnonprime

#print axioms plug_j9_hsucc_of_hdich_of_d2_ge3_of_nonprimeMin

end MinAvoidInstances
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
