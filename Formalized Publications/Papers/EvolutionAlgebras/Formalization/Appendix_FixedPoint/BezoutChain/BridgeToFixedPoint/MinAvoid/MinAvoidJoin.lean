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
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinSubsetAss
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# `minAvoid` join into the `hass` feed
join the last non-crux, non-rung-1 `hass` input (`minAvoid_all`)
into the end-to-end feed: attack it per rung / per prime (with the
closed `minSubAss` as lever), narrow the surviving residual to an
exact named SPEC, and restate the `hass_all` + `hsucc` masters on
`[rung-1, hdimEq-allocator-input, minAvoid-SPEC]` in
`SuccClosureRungs`-§4-exact shapes. `HdimEq`-family inputs enter only
through the `HdimEqMasterAlloc` allocator (SPEC hypotheses, never
attacked — /H own the crux). No `∀`-form over `c` is
attempted (all dead); no head-on crux attack (suspended).

## What is proved here

* §1 SPEC addresses (unconditional packaging): `MinAvoidAllSpec`
  (the exact HS `hmin` binder, named), the prime-single /
  nonprime-minimal SPEC pair (the exact HS splitter inputs,
  named), the `rfl` certificate onto the `SuccClosureRungs`-§4 `hmin`
  binder, and the unconditional splitter iff
  (`all ⟺ prime-singles ∧ nonprime`).
* §2 `minAvoid ⟺ step` exactness (the attack → verdict): per-rung
  `minAvoid` from the rung step (unconditional reduction via the
  step-`⟺`-`hass` iff + closed `minSubAss`); per-rung
  `MinAvoidRung j ⟺ step_j` conditional-exact on
  `[steps below j, hdimEq_j]` (the reverse leg is the HS
  rung lemma); per-prime twins (from-step reduction + iff mod
  `Min = Ass`); the `∀`-level converse of HassRung
  (`steps_all` from `[rung1step, hdimEq_all, minAvoid_all]`,
  so with the `∀`-level equivalence is exact mod
  `[rung1, hdimEq]`); `minAvoid` unconditional-vacuous at `n = 1`.
  verdict: `minAvoid` is the step mod `[below-steps, hdimEq]` —
  no independent route exists or is claimed; the residual is the
  §1 SPEC, carefully narrowed (prime-collapse / nonprime-only).
* §3 `hass_all` end-to-end on surviving inputs: the HS
  master restated with `hdimEq` fed by the per-stage allocator —
  general rung-1-step and rung-1-avoidance routes, `[local, supp]`
  and `[local, offcenter]` gated routes (via the Rung1Join
  / feeders), instance masters at `cDiagOnes` / Gap on
  `[alloc, minAvoid]`, the `d = 2` / `d ≥ 3` split-allocator
  variant (D2/Ge3 joint-attack shape), and the narrower-SPEC
  variant on `[prime-singles, nonprime-minimal]`.
* §4 `hsucc` end-to-end on surviving inputs: the `SuccClosureRungs`
  master fired with `hdimEq` fed by the allocator — rung-1-step,
  rung-1-avoidance (route), `[local, supp]`, `[local,
  offcenter]`, `cDiagOnes` / Gap instance masters on `[alloc,
  minAvoid]`, and the narrower-SPEC variant (via MinAss).
* §5 Feed audits: explicit certificates that `MinAvoidAllSpec`
  feeds the  `hmin` binders and the per-stage
  allocator feeds the `hdimEq` binder with no shape delta
  (each audit theorem states the consumer binder verbatim and is
  proved by the supplier — elaboration is the audit).

Status: `minAvoid` settled (step-strength, SPEC-narrowed)
+ `hass`/`hsucc` feed complete except the named SPECs below.

## Residual register (verbatim)

closed this lane: [`minAvoid` SPEC addresses + splitter iff];
[per-rung `minAvoid ⟺ step` on `[below-steps, hdimEq]` +
per-prime twins + `∀`-level converse + `n = 1` vacuity];
[`hass_all` on `[rung1/local-gates, alloc(-split), minAvoid-SPEC]`];
[`hsucc` on the same surviving inputs]; [feed audits: zero delta].
open (exact): [`MinAvoidAllSpec` (narrowed: prime-singles +
nonprime-only; is the step mod `[below-steps, hdimEq]` — verdict,
not open work)]; [rung-1 local gates per instance `c`
(in HD2)]; [the per-stage `d ≥ 2` allocator = the crux
]; [`hass` at `n = 1` and
`hsucc` at `n = 1` already unconditional (Rung1Join), cited not
duplicated].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/AssReductionRungs` (/ masters prime collapse
splitter
`rfl` certificate, rung/per-prime reductions),
`BridgeToFixedPoint/RungOneJoin` (gated feeders,
instance masters, `hsucc` masters),
`BridgeToFixedPoint/AssRungFeeds` (`hass_all_iff_steps`), `BridgeToFixedPoint/MinSubsetAss`
(`hsucc`-from-`hass`, `AssAvoidPrime`),
`BridgeToFixedPoint/MinAvoidRungs` (register shapes + iffs), `BridgeToFixedPoint/SuccClosureRungs`
(masters), `BridgeToFixedPoint/RungOneDiagonalDischarge` (rung-1 step
feeders + `cDiagOnes`), `BridgeToFixedPoint/RungDiagonal` (`rungI0`),
`BridgeToFixedPoint/RungDiagonalGap` (`diagWitness`),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`, `statementIndex`),
`Geometry/UnmixednessAtLengthTwo` (`HdimEqMinAtAss`),
`Regularity/SingleAllocator` (the allocator + HS converter),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`), narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/AssumptionFeeds/AssReductionRungs.lean/:
  458/:503` (rung lemma, minAvoid packaging, prime collapse,
  splitter, masters, `rfl` certificate, avoidance route).
* `BridgeToFixedPoint/Rung/RungOneJoin.lean`
  (gated feeders, instance masters, `hsucc` masters).
* `BridgeToFixedPoint/AssumptionFeeds/AssRungFeeds.lean` (`hass_all_iff_steps`).
* `BridgeToFixedPoint/MinAvoid/MinSubsetAss.lean` (`AssAvoidPrime`,
  `hsucc`-from-`hass`).
* `BridgeToFixedPoint/MinAvoidRungs.lean` (`MinAvoidRung`,
  `MinAvoidPrime`, per-rung iff, step `⟺` `hass`).
* `BridgeToFixedPoint/SuccClosureRungs.lean` (`hsucc` masters).
* `BridgeToFixedPoint/AssumptionFeeds/RungOneDiagonalDischarge.lean`
  (`rung1step_of_local_of_supp/offcenter`).
* `Regularity/DimensionEquality/SingleAllocator.lean`
  (allocator, HS converter, split converter).

Mathlib v4.34.0 (all read-only): `associatedPrimes`
(`RingTheory/Ideal/AssociatedPrime/Basic.lean`);
`Ideal.minimalPrimes` (`RingTheory/Ideal/MinimalPrime/Basic.lean`);
`IsSMulRegular` (`RingTheory/Regular/IsSMulRegular.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAvoidJoin

/-! ## §1. `minAvoid` SPEC addresses (unconditional packaging) -/

/-- The `∀`-closed minimal-avoidance SPEC: the exact HS
`hmin` binder, named so the feed's last non-crux input is a single
address.
-/
def MinAvoidAllSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    MinAvoidRungs.MinAvoidRung n K c hn j

/-- The prime-stage single-non-membership SPEC: the exact HS
`hprime` binder, named.
-/
def MinAvoidPrimeSingleSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
    (bridgeSystem n K c hn) j ∉
      MinAvoidRungs.stageIdeal n K c hn j

/-- The nonprime-stage minimal-avoidance SPEC: the exact HS
`hnonprime` binder (the strictly narrower residual after prime
stages collapse to singles), named.
-/
def MinAvoidNonprimeSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
    MinAvoidRungs.MinAvoidRung n K c hn j

#print axioms MinAvoidAllSpec
#print axioms MinAvoidPrimeSingleSpec
#print axioms MinAvoidNonprimeSpec

/-- `MinAvoidAllSpec` is the `SuccClosureRungs`-§4 `hmin` binder
(unconditional): the HS `rfl` certificate restated on the
named SPEC — definitionally the same `∀`-form, so the §4 `hsucc`
master consumes the SPEC with no adapter.
-/
theorem minAvoidAllSpec_iff_hmin_binder (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidAllSpec n K c hn ↔
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P) :=
  AssReductionRungs.minAvoid_all_iff_hmin_binder n K c hn

#print axioms minAvoidAllSpec_iff_hmin_binder

/-- The splitter iff (unconditional): `minAvoid_all` holds iff the
prime-stage singles and the nonprime-stage residual both hold.
Forward specializes (prime stages via the HS collapse);
backward is the HS splitter. This is the exact narrowed
shape of the residual: singles where stages are prime,
`MinAvoidRung` only where they are not.
-/
theorem minAvoidAllSpec_iff_primeSingle_nonprime (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidAllSpec n K c hn ↔
      MinAvoidPrimeSingleSpec n K c hn ∧
        MinAvoidNonprimeSpec n K c hn := by
  constructor
  · intro h
    constructor
    · intro j hj hP
      exact (@AssReductionRungs.minAvoidRung_iff_single_of_prime
        n K _ c hn j hP).mp (h j hj)
    · intro j hj _
      exact h j hj
  · rintro ⟨hprime, hnonprime⟩ j hj
    exact AssReductionRungs.minAvoid_all_of_primeSingle_of_nonprimeMin
      n K c hn hprime hnonprime j hj

#print axioms minAvoidAllSpec_iff_primeSingle_nonprime

/-! ## §2. `minAvoid ⟺ step` exactness (attack → verdict) -/

/-- Per-rung `minAvoid` from the rung step (unconditional
reduction): the step is fixed-element Ass-avoidance (the
iff), and Ass-avoidance is minimal avoidance by the closed
`minSubAss` (the HS packaging). The fixed bridge element
avoids every minimal prime as soon as it is regular.
-/
theorem minAvoidRung_of_step (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (hstep : IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    MinAvoidRungs.MinAvoidRung n K c hn j :=
  AssReductionRungs.minAvoidRung_of_hassRung n K c hn j
    ((MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mp hstep)

#print axioms minAvoidRung_of_step

/-- Per-rung `MinAvoidRung j ⟺ step_j` (conditional-exact on
`[hsteps, hdimEq]`): the reverse leg is the HS rung lemma
(`Min = Ass` from below-steps + `hdimEq`, then `hass → step`);
the forward leg is `minAvoidRung_of_step` above. This is the exact
per-rung address of fixed-`hmin`: it is the rung step mod
`[steps below j, hdimEq_j]` — downstream of the step, never an
independent lever.

Conditional on exactly `[hsteps, hdimEq]`. -/
theorem minAvoidRung_iff_step_of_steps_of_hdimEq (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hsteps : ∀ k : Fin (statementIndex n + 1), k.val < j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)) :
    MinAvoidRungs.MinAvoidRung n K c hn j ↔
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) := by
  constructor
  · intro hmin
    exact AssReductionRungs.stepSpanRung_of_steps_of_hdimEq_of_minAvoid
      n K c hn j hj hsteps hdimEq hmin
  · exact minAvoidRung_of_step n K c hn j

#print axioms minAvoidRung_iff_step_of_steps_of_hdimEq

/-- Per-prime `minAvoid` from the rung step (unconditional
reduction): the single-`(j, P)` minimal form — the step gives
per-prime Ass-avoidance at `P`, and `P` minimal over the stage
ideal is associated (closed `minSubAss`), hence avoided.
-/
theorem minAvoidPrime_of_step (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hstep : IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    MinAvoidRungs.MinAvoidPrime n K c hn j P := by
  have hass : MinAvoidRungs.AssAvoidRung n K c hn j :=
    (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mp hstep
  exact AssReductionRungs.minAvoidPrime_of_assAvoidPrime n K c hn j P
    (hass P)

#print axioms minAvoidPrime_of_step

/-- Per-prime minimal iff per-prime Ass-avoidance modulo
`Min = Ass` (unconditional): the single-`(j, P)` congruence —
under set-equality of minimal and associated primes the two
per-prime obligations coincide.
-/
theorem minAvoidPrime_iff_assAvoidPrime_of_minEqAss (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (heq : (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes =
      associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j)) :
    MinAvoidRungs.MinAvoidPrime n K c hn j P ↔
      MinSubsetAss.AssAvoidPrime n K c hn j P := by
  unfold MinAvoidRungs.MinAvoidPrime MinSubsetAss.AssAvoidPrime
  rw [heq]

#print axioms minAvoidPrime_iff_assAvoidPrime_of_minEqAss

/-- `∀`-level steps from `[rung-1 step, ∀-HdimEq, ∀-minAvoid]`
(conditional-exact): the HS master across the
`hass_all ⟺ steps` iff — the exact converse of HassRung
(`minAvoid_all` from `steps_all`), so together the `∀`-level
`minAvoid ⟺ steps` equivalence is exact mod `[rung1, hdimEq]`.

Conditional on exactly `[hrung1, hdimEq, hmin]`. -/
theorem steps_all_of_rung1step_of_hdimEq_of_minAvoid (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) :=
  (AssRungFeeds.hass_all_iff_steps n K c hn).mp
    (AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid
      K n hn c hrung1 hdimEq hmin)

#print axioms steps_all_of_rung1step_of_hdimEq_of_minAvoid

/-- `MinAvoidAllSpec` at `n = 1`, unconditional-vacuous (no
hypotheses at all): `Fin (statementIndex 1 + 1) = Fin 1` has no
index with `2 ≤ val`, so the SPEC binder is empty.
-/
theorem minAvoidAllSpec_n1_vacuous (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    MinAvoidAllSpec 1 K c hn := by
  intro j hj
  have h1 : statementIndex 1 + 1 = 1 := rfl
  have hlt := j.isLt
  omega

#print axioms minAvoidAllSpec_n1_vacuous

/-! ## §3. `hass_all` end-to-end on surviving inputs -/

/-- Full `hass_all` from `[rung-1 step, per-stage allocator,
`MinAvoidAllSpec`]` (NO `hdimEq` hypothesis): the HS master
with the `hdimEq` binder fed by the per-stage `d ≥ 2` allocator
(the allocator's HS converter). The `hass` feed's crux input is
now the single allocator address.

Conditional on exactly `[hrung1, halloc, hmin]`. -/
theorem hass_all_of_rung1step_of_alloc_of_minAvoidSpec (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid K n
    hn c hrung1
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hass_all_of_rung1step_of_alloc_of_minAvoidSpec

/-- Full `hass_all` from `[rung-1 avoidance, per-stage allocator,
`MinAvoidAllSpec`]` (NO step hypothesis): the HS master
with the `hdimEq` binder fed by the allocator. The two rung-1
routes coincide on the surviving inputs.

Conditional on exactly `[hrung1, halloc, hmin]`. -/
theorem hass_all_of_rung1Avoid_of_alloc_of_minAvoidSpec (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  AssReductionRungs.hass_all_of_rung1Avoid_of_hdimEq_of_minAvoid K n
    hn c hrung1
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hass_all_of_rung1Avoid_of_alloc_of_minAvoidSpec

/-- Full `hass_all` from `[local-∀, supp-∀, per-stage allocator,
`MinAvoidAllSpec`]` (NO rung-1 hypothesis): the Rung1Join
feeder with the `hdimEq` binder fed by the allocator.

Conditional on exactly `[local, supp, halloc, hmin]`. -/
theorem hass_all_of_local_of_supp_of_alloc_of_minAvoidSpec
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  RungOneJoin.hass_all_of_local_of_supp_of_hdimEq_of_minAvoid K n
    hn c hdiag hsupp
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hass_all_of_local_of_supp_of_alloc_of_minAvoidSpec

/-- Full `hass_all` from `[local-∀, offcenter-∀, per-stage
allocator, `MinAvoidAllSpec`]` (NO rung-1, NO `supp`
hypothesis): the Rung1Join feeder with the `hdimEq` binder
fed by the allocator.

Conditional on exactly `[local, offcenter, halloc, hmin]`. -/
theorem hass_all_of_local_of_offcenter_of_alloc_of_minAvoidSpec
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  RungOneJoin.hass_all_of_local_of_offcenter_of_hdimEq_of_minAvoid
    K n hn c hdiag hoff
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hass_all_of_local_of_offcenter_of_alloc_of_minAvoidSpec

/-- Full `hass_all` at the all-ones-diagonal family from
`[per-stage allocator, minAvoid]` only (no rung-1 hypotheses):
the Rung1Join instance master with the `hdimEq` binder fed
by the allocator.

Conditional on exactly `[halloc, hmin]`. -/
theorem hass_all_cDiagOnes_of_alloc_of_minAvoid (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  RungOneJoin.hass_all_cDiagOnes_of_hdimEq_of_minAvoid K n hn
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn _
      halloc)
    hmin

#print axioms hass_all_cDiagOnes_of_alloc_of_minAvoid

/-- Full `hass_all` at the Gap witness from `[per-stage allocator,
minAvoid]` ONLY (NO rung-1 hypotheses): the Rung1Join
instance master with the `hdimEq` binder fed by the allocator.

Conditional on exactly `[halloc, hmin]`. -/
theorem hass_all_gap_of_alloc_of_minAvoid (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  RungOneJoin.hass_all_gap_of_hdimEq_of_minAvoid K hn
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K 3 hn _
      halloc)
    hmin

#print axioms hass_all_gap_of_alloc_of_minAvoid

/-- Full `hass_all` from `[rung-1 step, split allocator,
`MinAvoidAllSpec`]` (NO `hdimEq` hypothesis): the per-stage
`d = 2` / `d ≥ 3` split-allocator slices (the D2/Ge3 joint-attack
shape) feed the `hdimEq` binder via the allocator's split
converter, then the HS master fires.

Conditional on exactly `[hrung1, hallocSplit, hmin]`. -/
theorem hass_all_of_rung1step_of_allocSplit_of_minAvoidSpec
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (hallocSplit : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => d = 2) ∧
        SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 3 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  AssReductionRungs.hass_all_of_rung1step_of_hdimEq_of_minAvoid K n
    hn c hrung1
    (SingleAllocator.hdimEqMaster_j9_hdimEq_all_of_allocSplit K n
      hn c hallocSplit)
    hmin

#print axioms hass_all_of_rung1step_of_allocSplit_of_minAvoidSpec

/-- Full `hass_all` from `[rung-1 step, per-stage allocator,
prime-singles, nonprime-minimal]` (NO full-`minAvoid`
hypothesis): the §1 splitter narrows `MinAvoidAllSpec` to the
prime-single + nonprime-only pair, then the allocator master
fires. The feed is complete on the strictly narrower SPEC.

Conditional on exactly `[hrung1, halloc, hprime, hnonprime]`. -/
theorem hass_all_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  hass_all_of_rung1step_of_alloc_of_minAvoidSpec K n hn c hrung1
    halloc
    ((minAvoidAllSpec_iff_primeSingle_nonprime n K c hn).mpr
      ⟨hprime, hnonprime⟩)

#print axioms hass_all_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin

/-! ## §4. `hsucc` end-to-end on surviving inputs -/

/-- Full `hsucc` from `[rung-1 step, per-stage allocator,
`MinAvoidAllSpec`]` (NO `hdimEq` hypothesis): the `SuccClosureRungs`
master with the `hdimEq` binder fed by the allocator and the §4
`hmin` binder fed by the SPEC (definitionally — §1 certificate).
The `SuccClosureRungs`-§4-exact end-to-end feed.

Conditional on exactly `[hrung1, halloc, hmin]`. -/
theorem hsucc_of_rung1step_of_alloc_of_minAvoidSpec (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn c hrung1
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hsucc_of_rung1step_of_alloc_of_minAvoidSpec

/-- Full `hsucc` from `[rung-1 avoidance, per-stage allocator,
`MinAvoidAllSpec`]` (NO step hypothesis): the `SuccClosureRungs`
fixed-family route with the `hdimEq` binder fed by the allocator.

Conditional on exactly `[hrung1, halloc, hmin]`. -/
theorem hsucc_of_rung1Avoid_of_alloc_of_minAvoidSpec (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_minAvoid
    K n hn c hrung1
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hsucc_of_rung1Avoid_of_alloc_of_minAvoidSpec

/-- Full `hsucc` from `[local-∀, supp-∀, per-stage allocator,
`MinAvoidAllSpec`]` (NO rung-1 hypothesis): the master with
rung 1 discharged by the HD2 feeder and `hdimEq` fed by the
allocator.

Conditional on exactly `[local, supp, halloc, hmin]`. -/
theorem hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_supp n K c hn hdiag
      hsupp)
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec

/-- Full `hsucc` from `[local-∀, offcenter-∀, per-stage allocator,
`MinAvoidAllSpec`]` (NO rung-1, NO `supp` hypothesis): the
master with rung 1 discharged by the HD2 offcenter-gated
feeder and `hdimEq` fed by the allocator.

Conditional on exactly `[local, offcenter, halloc, hmin]`. -/
theorem hsucc_of_local_of_offcenter_of_alloc_of_minAvoidSpec
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_offcenter n K c hn
      hdiag hoff)
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    hmin

#print axioms hsucc_of_local_of_offcenter_of_alloc_of_minAvoidSpec

/-- Full `hsucc` at the all-ones-diagonal family from `[per-stage
allocator, minAvoid]` only (no rung-1 hypotheses): the Rung1Join
instance master with the `hdimEq` binder fed by the
allocator.

Conditional on exactly `[halloc, hmin]`. -/
theorem hsucc_cDiagOnes_of_alloc_of_minAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) :=
  RungOneJoin.hsucc_cDiagOnes_of_hdimEq_of_minAvoid K n hn
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn _
      halloc)
    hmin

#print axioms hsucc_cDiagOnes_of_alloc_of_minAvoid

/-- Full `hsucc` at the Gap witness from `[per-stage allocator,
minAvoid]` ONLY (NO rung-1 hypotheses): the Rung1Join
instance master with the `hdimEq` binder fed by the allocator.

Conditional on exactly `[halloc, hmin]`. -/
theorem hsucc_gap_of_alloc_of_minAvoid (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hmin : MinAvoidAllSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) :=
  RungOneJoin.hsucc_gap_of_hdimEq_of_minAvoid K hn
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K 3 hn _
      halloc)
    hmin

#print axioms hsucc_gap_of_alloc_of_minAvoid

/-- Full `hsucc` from `[rung-1 step, per-stage allocator,
prime-singles, nonprime-minimal]` (NO full-`minAvoid`
hypothesis): the MinAss `hsucc`-from-`hass` master fired
with the §3 narrower-SPEC `hass_all` and the allocator-fed
`hdimEq`. The end-to-end feed is complete on the strictly
narrower SPEC.

Conditional on exactly `[hrung1, halloc, hprime, hnonprime]`. -/
theorem hsucc_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinSubsetAss.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    K n hn c hrung1
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    (hass_all_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
      K n hn c hrung1 halloc hprime hnonprime)

#print axioms hsucc_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin

/-! ## §5. Feed audits: SPECs feed / with zero delta

Each audit theorem below states the consumer binder verbatim and
is proved by the supplier — elaboration checks definitional
equality, so a clean build confirms the audit: the §1 SPEC and
the per-stage allocator feed with no shape delta. No adapter,
no residual on the feed side.
-/

/-- Audit: `MinAvoidAllSpec` feeds the HS `hmin` binder
with zero shape delta (stated verbatim).
-/
theorem audit_minAvoidSpec_feeds_393 (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j :=
  hmin

#print axioms audit_minAvoidSpec_feeds_393

/-- Audit: `MinAvoidAllSpec` feeds the `SuccClosureRungs` `hmin`
binder with zero shape delta (stated verbatim, unfolded §4
shape across the reducible stage-ideal abbrev).
-/
theorem audit_minAvoidSpec_feeds_400 (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hmin : MinAvoidAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P :=
  hmin

#print axioms audit_minAvoidSpec_feeds_400

/-- Audit: the per-stage `d ≥ 2` allocator feeds the HS /
`hdimEq` binder with zero shape delta (stated verbatim),
via the allocator's HS converter.
-/
theorem audit_alloc_feeds_hdimEq_binder (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) :=
  SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c halloc

#print axioms audit_alloc_feeds_hdimEq_binder

/-! ## §6. Residual register (doc only; see module docstring)

closed this lane: [SPEC addresses + splitter iff]; [`minAvoid ⟺
step` per-rung/per-prime + `∀`-converse + `n = 1` vacuity];
[`hass_all` / `hsucc` on surviving inputs]; [feed audits: zero
delta]. Open (exact): [`MinAvoidAllSpec` (narrowed; is the step
mod `[below-steps, hdimEq]` — verdict)]; [rung-1 local gates per
instance (in HD2)]; [per-stage `d ≥ 2` allocator (Track
R/H-owned crux)]. No new remainder beyond the register.
-/

end MinAvoidJoin
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
