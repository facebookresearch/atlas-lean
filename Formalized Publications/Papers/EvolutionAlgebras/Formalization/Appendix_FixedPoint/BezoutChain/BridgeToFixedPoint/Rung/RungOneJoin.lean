/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssReductionRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssRungFeeds
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.RungOneDiagonalDischarge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Rung-1 join into the `hass` feed
join the HD2 rung-1 closes into the HS `hass_all`
masters: the rung-1 input of `AssReductionRungs` §4 is discharged
(or narrowed) instance by instance, and the HS masters are restated
on the surviving inputs. `hdimEq_all` / `minAvoid_all` are taken as
SPEC hypotheses (other lanes' territory, never reproved).

## What is proved here

* §1 Rung-1 avoidance closes (the second rung-1 shape — HD2 closed
  the step shape only): `rung1Avoid` unconditional at the
  `cDiagOnes` family (all `n`), at the Gap witness, and
  vacuous at `n = 1`, via the step-to-avoidance
  converter; plus the offcenter-gated form (no `supp` input).
* §2 `hass` feed wiring: the HS master restated with rung-1
  discharged — full masters on `[local-∀, supp-∀, hdimEq,
  minAvoid]` and `[local-∀, offcenter-∀, hdimEq, minAvoid]`,
  instance masters at `cDiagOnes` / Gap on `[hdimEq, minAvoid]`,
  and `hass_all` unconditional-vacuous at `n = 1`.
* §3 End-to-end `hsucc` on surviving inputs: the `SuccClosureRungs`
  master fired with rung-1 discharged — `hsucc` at
  `cDiagOnes` / Gap conditional-exact on `[hdimEq, minAvoid]`,
  and `hsucc` unconditional at `n = 1`.
* §4 Instance-close audit: explicit certificates that every HD2 §5
  close feeds the / consumption shapes with no
  shape delta (each audit theorem states the consumer binder
  verbatim and is proved by the HD2 close — elaboration is the
  audit).

Status: rung-1 feed narrowed-or-closed + HS masters restated.
`∀`-unconditional rung-1 is impossible (HD §3: `c = 0` refutes
every `∀`-form) and is not attempted; every close here is an
instance close or a gated form.

## Residual register (verbatim)

closed this lane: [rung-1 avoidance at `cDiagOnes`/Gap/`n = 1`];
[offcenter-gated rung-1 avoidance]; [`hass_all` on
`[local, supp/offcenter, hdimEq, minAvoid]`]; [`hass_all` at
`cDiagOnes`/Gap on `[hdimEq, minAvoid]`]; [`hass_all` vacuous at
`n = 1`]; [`hsucc` at `cDiagOnes`/Gap on `[hdimEq, minAvoid]`];
[`hsucc` unconditional at `n = 1`]; [HD2 §5 audit: all closes
feed with zero delta]. Open (exact): [rung-1 local
diagonality `HdiagRung1-∀` per instance `c` (in HD2)];
[rung-1 scalar support `HsuppRung1-∀` / offcenter-`∀` per
instance `c` (in HD2)]; [rungs `≥ 2` `[hdimEq, minAvoid]`
(other lanes' territory, unchanged)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/RungOneDiagonalDischarge` (rung-1
step closes), `BridgeToFixedPoint/AssReductionRungs` (master),
`BridgeToFixedPoint/AssRungFeeds` (converter), `BridgeToFixedPoint/SuccClosureRungs`
(master), `BridgeToFixedPoint/MinAvoidRungs` (register shapes),
`BridgeToFixedPoint/RungDiagonalGap`
(`diagWitness`), `BridgeToFixedPoint/RungDiagonal` (`rungI0`),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`, `statementIndex`),
`Geometry/UnmixednessAtLengthTwo` (`HdimEqMinAtAss`), `Regularity/RegularityBridge`
(`SuccessiveSMulRegular`), narrow Mathlib. No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/AssumptionFeeds/RungOneDiagonalDischarge.lean` (rung-1
  step closes consumed here).
* `BridgeToFixedPoint/AssumptionFeeds/AssReductionRungs.lean` (masters restated here).
* `BridgeToFixedPoint/AssumptionFeeds/AssRungFeeds.lean` (step-to-avoidance converter).
* `BridgeToFixedPoint/SuccClosureRungs.lean` (`hsucc` master fired in §3).

Mathlib v4.34.0 (all read-only): `associatedPrimes`
(`RingTheory/Ideal/AssociatedPrime/Basic.lean`); `IsSMulRegular`
(`RingTheory/Regular/IsSMulRegular.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungOneJoin

/-! ## §1 Rung-1 avoidance closes (second rung-1 shape) -/

/-- shape rung-1 avoidance at the all-ones-diagonal family,
unconditionally (all `n`): the HD2 step close through the
step-to-avoidance converter. The rung-1 avoidance input of
the master is discharged at `cDiagOnes`.
-/
theorem rung1Avoid_cDiagOnes (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) k ∉ P :=
  AssRungFeeds.rung1Avoid_of_rung1step n K _ hn
    (RungOneDiagonalDischarge.rung1step_cDiagOnes n K hn)

#print axioms rung1Avoid_cDiagOnes

/-- shape rung-1 avoidance at the Gap witness,
unconditionally (concrete instance): the HD2 step close
through the converter.
-/
theorem rung1Avoid_gap (K : Type*) [Field K] (hn : 0 < 3) :
    ∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex 3 + 2)) K)
        (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
            (MvPolynomial (Fin (statementIndex 3 + 2)) K)))),
        (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) k ∉ P :=
  AssRungFeeds.rung1Avoid_of_rung1step 3 K _ hn
    (RungOneDiagonalDischarge.rung1step_gap K hn)

#print axioms rung1Avoid_gap

/-- shape rung-1 avoidance at `n = 1`,
unconditional-vacuous: the HD2 vacuous step close through
the converter.
-/
theorem rung1Avoid_n1_vacuous (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    ∀ k : Fin (statementIndex 1 + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex 1 + 2)) K)
        (MvPolynomial (Fin (statementIndex 1 + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem 1 K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 1 + 2)) K)
            (MvPolynomial (Fin (statementIndex 1 + 2)) K)))),
        (bridgeSystem 1 K c hn) k ∉ P :=
  AssRungFeeds.rung1Avoid_of_rung1step 1 K c hn
    (RungOneDiagonalDischarge.rung1step_n1_vacuous K c hn)

#print axioms rung1Avoid_n1_vacuous

/-- shape rung-1 avoidance from `[local-∀, offcenter-∀]`
with no support hypothesis (conditional-exact): the HD2
offcenter-gated step close through the converter.

Conditional on exactly `[HdiagRung1-∀, offcenter-∀]`. -/
theorem rung1Avoid_of_local_of_offcenter (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P :=
  AssRungFeeds.rung1Avoid_of_rung1step n K c hn
    (RungOneDiagonalDischarge.rung1step_of_local_of_offcenter n K c hn
      hdiag hoff)

#print axioms rung1Avoid_of_local_of_offcenter

/-! ## §2 `hass` feed wiring: HS on surviving inputs -/

/-- Full `hass_all` from `[local-∀, supp-∀, ∀-HdimEq, ∀-minAvoid]`
(no rung-1 hypothesis): the HS master with rung 1
discharged by the HD2 feeder. The rung-1 input of the
`hass` feed is narrowed to the HD2 local gates.

Conditional on exactly `[local, supp, hdimEq, minAvoid]`. -/
theorem hass_all_of_local_of_supp_of_hdimEq_of_minAvoid (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid K n
    hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_supp n K c hn hdiag
      hsupp)
    hdimEq hmin

#print axioms hass_all_of_local_of_supp_of_hdimEq_of_minAvoid

/-- Full `hass_all` from `[local-∀, offcenter-∀, ∀-HdimEq,
∀-minAvoid]` (NO rung-1, NO `supp` hypothesis): the HS
master with rung 1 discharged by the HD2 offcenter-gated
feeder.

Conditional on exactly `[local, offcenter, hdimEq, minAvoid]`. -/
theorem hass_all_of_local_of_offcenter_of_hdimEq_of_minAvoid
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid K n
    hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_offcenter n K c hn
      hdiag hoff)
    hdimEq hmin

#print axioms hass_all_of_local_of_offcenter_of_hdimEq_of_minAvoid

/-- Full `hass_all` at the all-ones-diagonal family from
`[∀-HdimEq, ∀-minAvoid]` only (no rung-1 hypotheses): the HS
master with rung 1 discharged by the HD2
family close.

Conditional on exactly `[hdimEq, minAvoid]`. -/
theorem hass_all_cDiagOnes_of_hdimEq_of_minAvoid (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
            {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid K n
    hn _ (RungOneDiagonalDischarge.rung1step_cDiagOnes n K hn) hdimEq hmin

#print axioms hass_all_cDiagOnes_of_hdimEq_of_minAvoid

/-- Full `hass_all` at the Gap witness from `[∀-HdimEq,
∀-minAvoid]` ONLY (NO rung-1 hypotheses): the HS master
with rung 1 discharged by the HD2 instance close.

Conditional on exactly `[hdimEq, minAvoid]`. -/
theorem hass_all_gap_of_hdimEq_of_minAvoid (K : Type*) [Field K]
    (hn : 0 < 3)
    (hdimEq : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
            {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid K 3
    hn _ (RungOneDiagonalDischarge.rung1step_gap K hn) hdimEq hmin

#print axioms hass_all_gap_of_hdimEq_of_minAvoid

/-- Full `hass_all` at `n = 1`, unconditional-vacuous (no
hypotheses at all): `Fin (statementIndex 1 + 1) = Fin 1` has no
index with `2 ≤ val`, so the conclusion binder is empty.
-/
theorem hass_all_n1_vacuous (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    ∀ j : Fin (statementIndex 1 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 1 K c hn j := by
  intro j hj
  have h1 : statementIndex 1 + 1 = 1 := rfl
  have hlt := j.isLt
  omega

#print axioms hass_all_n1_vacuous

/-! ## §3 End-to-end `hsucc` on surviving inputs -/

/-- Full `hsucc` at the all-ones-diagonal family from
`[∀-HdimEq, ∀-minAvoid]` only (no rung-1 hypotheses): the
`SuccClosureRungs` master with rung 1 discharged by the HD2
family close. The `MinAvoidRung` `∀`-form feeds the
`hmin` binder definitionally (HS `rfl` certificate).

Conditional on exactly `[hdimEq, minAvoid]`. -/
theorem hsucc_cDiagOnes_of_hdimEq_of_minAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
            {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn _ (RungOneDiagonalDischarge.rung1step_cDiagOnes n K hn)
    hdimEq hmin

#print axioms hsucc_cDiagOnes_of_hdimEq_of_minAvoid

/-- Full `hsucc` at the Gap witness from `[∀-HdimEq, ∀-minAvoid]`
only (no rung-1 hypotheses): the `SuccClosureRungs` master with
rung 1 discharged by the HD2 instance close.

Conditional on exactly `[hdimEq, minAvoid]`. -/
theorem hsucc_gap_of_hdimEq_of_minAvoid (K : Type*) [Field K]
    (hn : 0 < 3)
    (hdimEq : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
        (Ideal.span
          (Set.image
            (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
            {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K 3 hn _ (RungOneDiagonalDischarge.rung1step_gap K hn) hdimEq hmin

#print axioms hsucc_gap_of_hdimEq_of_minAvoid

/-- Full `hsucc` at `n = 1`, unconditional (no hypotheses at
all): the `SuccClosureRungs` master with rung 1 discharged by
the HD2 vacuous close and the `hdimEq` / `hmin` binders
discharged vacuously (`Fin 1` has no index with `2 ≤ val`).
-/
theorem hsucc_n1_unconditional (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 1 K c hn) := by
  have hvac : ∀ j : Fin (statementIndex 1 + 1), 2 ≤ j.val → False := by
    intro j hj
    have h1 : statementIndex 1 + 1 = 1 := rfl
    have hlt := j.isLt
    omega
  exact SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K 1 hn c (RungOneDiagonalDischarge.rung1step_n1_vacuous K c hn)
    (fun j hj => (hvac j hj).elim)
    (fun j hj => (hvac j hj).elim)

#print axioms hsucc_n1_unconditional

/-! ## §4 Instance-close audit: HD2 §5 closes feed /

Each audit theorem below states the consumer binder verbatim
(`hrung1` step shape `hrung1` avoidance shape)
and is proved by the supplier close — elaboration checks
definitional equality, so a clean build confirms the audit:
all three HD2 §5 closes feed with no shape delta, and the
§1 avoidance closes feed the route with no delta.
No adapter, no residual on the rung-1 side.
-/

/-- Audit: the HD2 family close feeds the HS
`hrung1` binder with zero shape delta (stated verbatim).
-/
theorem audit_step_cDiagOnes_feeds_393 (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) k) :=
  RungOneDiagonalDischarge.rung1step_cDiagOnes n K hn

#print axioms audit_step_cDiagOnes_feeds_393

/-- Audit: the HD2 Gap close feeds the HS `hrung1`
binder with zero shape delta (stated verbatim).
-/
theorem audit_step_gap_feeds_393 (K : Type*) [Field K] (hn : 0 < 3) :
    ∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
            (MvPolynomial (Fin (statementIndex 3 + 2)) K))))
        ((bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) k) :=
  RungOneDiagonalDischarge.rung1step_gap K hn

#print axioms audit_step_gap_feeds_393

/-- Audit: the HD2 `n = 1` close feeds the HS
`hrung1` binder with zero shape delta (stated verbatim).
-/
theorem audit_step_n1_feeds_393 (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    ∀ k : Fin (statementIndex 1 + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex 1 + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem 1 K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 1 + 2)) K)
            (MvPolynomial (Fin (statementIndex 1 + 2)) K))))
        ((bridgeSystem 1 K c hn) k) :=
  RungOneDiagonalDischarge.rung1step_n1_vacuous K c hn

#print axioms audit_step_n1_feeds_393

/-- Audit: the §1 `cDiagOnes` avoidance close feeds the HS
`hrung1` binder with zero shape delta (stated verbatim).
-/
theorem audit_avoid_cDiagOnes_feeds_503 (n : ℕ) (K : Type*)
    [Field K] (hn : 0 < n) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) k ∉ P :=
  rung1Avoid_cDiagOnes n K hn

#print axioms audit_avoid_cDiagOnes_feeds_503

/-- Audit: the §1 Gap avoidance close feeds the HS `hrung1`
binder with zero shape delta (stated verbatim).
-/
theorem audit_avoid_gap_feeds_503 (K : Type*) [Field K]
    (hn : 0 < 3) :
    ∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex 3 + 2)) K)
        (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
            (MvPolynomial (Fin (statementIndex 3 + 2)) K)))),
        (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) k ∉ P :=
  rung1Avoid_gap K hn

#print axioms audit_avoid_gap_feeds_503

/-- Audit: the §1 `n = 1` avoidance close feeds the HS
`hrung1` binder with zero shape delta (stated verbatim).
-/
theorem audit_avoid_n1_feeds_503 (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    ∀ k : Fin (statementIndex 1 + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex 1 + 2)) K)
        (MvPolynomial (Fin (statementIndex 1 + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem 1 K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 1 + 2)) K)
            (MvPolynomial (Fin (statementIndex 1 + 2)) K)))),
        (bridgeSystem 1 K c hn) k ∉ P :=
  rung1Avoid_n1_vacuous K c hn

#print axioms audit_avoid_n1_feeds_503

/-! ## §5. Residual register (doc only; see module docstring)

closed this lane: [rung-1 avoidance closes]; [`hass_all` /
`hsucc` on surviving inputs]; [HD2 §5 audit: zero delta]. Open
(exact): [HD2 local gates per instance `c`]; [rungs `≥ 2`
`[hdimEq, minAvoid]`]. No new remainder beyond the register.
-/

end RungOneJoin
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
