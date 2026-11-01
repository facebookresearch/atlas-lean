/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssRungFeeds
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinSubsetAss
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# `hass` reduction at rungs `≥ 2`
Task: bank the step-assembly theory for the `hass` reduction at rungs
`≥ 2` (`hunmixed + minAvoid → rung step → hsucc`) and attack `hass_all`
(fixed-element Ass-avoidance across rungs `≥ 2` — the last
`SuccClosureRungs`-§4 input family alongside `hdimEq`) via the bank, ending in
`SuccClosureRungs`-§4-consumable form. `hdimEq`-family inputs are taken as
explicit SPEC hypotheses (the crux is not owned here). `minSubAss` is
reused closed (never reproved); fixed-`hmin`-as-lever and `∀`-forms are
never retried (settled/dead).

## Verdict (attack closes to the exact terminal triple)

* §1 (unconditional bank): stage-ideal chains — `J = ⊥` at rung 0,
  monotonicity in the rung index, the successor equation
  `J₊ = J ⊔ span {q j}`.
* §2 (bank): per-rung rung-step transport — `hass` at rung `j` from
  `[hunmixed, minAvoid]` (register shape), from `[hsucc_prefix, hdimEq,
  minAvoid]`, and from `[steps below j, hdimEq, minAvoid]` (the
  induction rung lemma); span-shape step from the same triple; plus
  minAvoid-per-rung packaging with closed `minSubAss` as lever
  (per-rung and per-prime forms).
* §3 (bank): prime-stage collapse — `minAvoid` at a prime stage is a
  single non-membership (unconditional iff reduction, no hunmixed
  input); the `∀`-form splitter isolating prime stages from the
  non-prime residual.
* §4 (attack endpoint, conditional-exact): `hass_all` from
  `[rung1step, hdimEq_all, minAvoid_all]` by strong rung induction
  (rung 0 unconditional in-file, rung 1 by hypothesis, rungs `≥ 2` via
  the §2 rung lemma with prefix steps from the IH); the `rfl`
  certificate that the `MinAvoidRung` `∀`-form is the §4 `hmin` binder;
  SPEC-variant (`HdimEqAllSpec`) and fixed-family (`rung1Avoid`)
  masters. The direct induction is proved (not the
  `hsucc`-then-`hass⟺steps` composition) so the per-rung reduction
  chain fires explicitly.

## Residual register (verbatim)

closed this lane: [stage-ideal chain bank (`⊥`/mono/succ)];
[per-rung `hass` transport from `[hunmixed]`/`[hsucc_prefix, hdimEq]`/
`[steps below, hdimEq]` + `minAvoid`]; [span-step from the triple];
[minAvoid per-rung/per-prime packaging on closed `minSubAss`];
[prime-stage `minAvoid` collapse + `∀`-splitter]; [`hass_all` from
`[rung1step, hdimEq_all, minAvoid_all]` + SPEC/fixed-family variants].
open (exact): [per-rung minimal avoidance `minAvoid_all` — terminal:
at prime stages it is a single non-membership (§3); elsewhere it is
the step mod `[steps below, hdimEq]` (no independent route — the
`MinAvoidRungs`/`MinSubsetAss` verdict, not open work)]; [rung-1 step /
avoidance — HD-lane owned (`[hdiag, hgen]` or `[hdich]` suppliers)];
[the `HdimEq` crux (SPEC-scoped, proved elsewhere)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/FinalDischargeHub` (rung 0),
`BridgeToFixedPoint/MinAvoidRungs` (register shapes + iffs), `BridgeToFixedPoint/SuccClosureRungs`
(prefix slices + converters), `BridgeToFixedPoint/AssRungFeeds` (SPEC shim +
`Min = Ass` from below-steps), `BridgeToFixedPoint/MinSubsetAss` (closed `minSubAss`
+ per-rung `Min = Ass`), `Geometry/UnmixednessAtLengthTwo` (`HdimEqMinAtAss`),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`), narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoidRungs.lean` (avoidance conversions,
  per-rung `Min ⟺ Ass`, step `⟺` `hass`); (the R3 register).
* `BridgeToFixedPoint/SuccClosureRungs.lean` (`prefixSlice`, span
  equation, prefix-`hsucc`, shape converter); (the §4 master
  whose input shape is matched here).
* `BridgeToFixedPoint/AssumptionFeeds/AssRungFeeds.lean` (`hass ⟺ steps`,
  rung-1 converters, SPEC shim, `Min = Ass` from below-steps).
* `BridgeToFixedPoint/MinAvoid/MinSubsetAss.lean` (closed `minSubAss`,
  `∀`-form, prime `Min = Ass`, per-rung `Min = Ass`).
* `BridgeToFixedPoint/RungStepFromUnmixedness.lean`
  (step from `[hunmixed, minAvoid]` — the transported masters).
* `BridgeToFixedPoint/FinalDischargeHub.lean` (`bridgeSystem_rung_zero`).
* `Geometry/UnmixednessAtLengthK.lean`, `Geometry/UnmixednessAtLengthTwo.lean`
  (unmixedness suppliers, consumed via).
* `Regularity/Koszul/YSopStep.lean` (`ysop_step`: local-ring
  existence-form master — the existence half is banked upstream
  (`MinAvoidRungs` §1, `AssRungFeeds` §1); this lane is fixed-element).
* `Regularity/Assembly/JointAssembly.lean` (closure map:
  `hass ⟺ step ⇐ [hunmixed, minAvoid]` — reduced per rung here).

Mathlib v4.34.0 (all read-only):

* `associatedPrimes` (`RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.minimalPrimes` (`RingTheory/Ideal/MinimalPrime/Basic.lean`).
* `IsSMulRegular` (`RingTheory/Regular/IsSMulRegular.lean`).
* `Ideal.span_empty/span_mono/span_union`
  (`RingTheory/Ideal/Span.lean`).
* `Set.image_empty/image_mono/image_union/image_singleton`
  (`Data/Set/Image.lean`).
* `Nat.strong_induction_on` (in-tree precedent:
  `BridgeToFixedPoint/SuccClosureRungs.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AssReductionRungs

/-! ## §1. Stage-ideal chains (unconditional) -/

/-- The stage ideal at rung 0 is `⊥` (unconditional): no rung index
lies below `0`, so the image is empty and the span is `⊥`.
-/
theorem stageIdeal_eq_bot_of_val_zero (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj0 : j.val = 0) :
    MinAvoidRungs.stageIdeal n K c hn j = ⊥ := by
  have hempty : {k : Fin (statementIndex n + 1) | k.val < j.val} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    omega
  unfold MinAvoidRungs.stageIdeal
  rw [hempty, Set.image_empty, Ideal.span_empty]

#print axioms stageIdeal_eq_bot_of_val_zero

/-- Stage ideals are monotone in the rung index (unconditional): a
larger prefix spans a larger ideal.
-/
theorem stageIdeal_mono (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j k : Fin (statementIndex n + 1)) (hle : j.val ≤ k.val) :
    MinAvoidRungs.stageIdeal n K c hn j ≤
      MinAvoidRungs.stageIdeal n K c hn k := by
  unfold MinAvoidRungs.stageIdeal
  apply Ideal.span_mono
  apply Set.image_mono
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  omega

#print axioms stageIdeal_mono

/-- Successor equation for stage ideals (unconditional): the stage
ideal at rung `k = j + 1` is the stage-`j` ideal plus the span of the
fixed rung-`j` element.
-/
theorem stageIdeal_succ (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j k : Fin (statementIndex n + 1)) (hk : k.val = j.val + 1) :
    MinAvoidRungs.stageIdeal n K c hn k =
      MinAvoidRungs.stageIdeal n K c hn j ⊔
        Ideal.span {(bridgeSystem n K c hn) j} := by
  have hset : {k' : Fin (statementIndex n + 1) | k'.val < k.val} =
      {k' : Fin (statementIndex n + 1) | k'.val < j.val} ∪ {j} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_cases hxj : x.val < j.val
      · exact Or.inl hxj
      · have hxeq : x = j := by
          apply Fin.ext
          omega
        exact Or.inr hxeq
    · rintro (hx | rfl)
      · omega
      · omega
  unfold MinAvoidRungs.stageIdeal
  rw [hset, Set.image_union, Set.image_singleton, Ideal.span_union]

#print axioms stageIdeal_succ

/-! ## §2. Rung-step transport + minAvoid packaging (bank) -/

/-- Per-rung `hass` from `[hunmixed, minAvoid]` (unconditional
reduction): every Ass prime of the stage quotient is minimal, hence
avoided — the `MinAvoidRungs` register shape stated at the rung.
-/
theorem hassRung_of_hunmixed_of_minAvoid (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (hunmixed : ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j),
        P ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes)
    (hmin : MinAvoidRungs.MinAvoidRung n K c hn j) :
    MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidRungs.assAvoid_of_hminAvoid_of_subAss
    (MinAvoidRungs.stageIdeal n K c hn j) ((bridgeSystem n K c hn) j)
    hunmixed hmin

#print axioms hassRung_of_hunmixed_of_minAvoid

/-- Per-rung `hass` from `[prefix-hsucc, HdimEq, minAvoid]`
(conditional-exact): `Min = Ass` via the `MinSubsetAss` per-rung
master, then the per-rung `Min ⟺ Ass` iff — the exact J9-map
per-rung reduction (`hass ⟺ step ⇐ [hunmixed, minAvoid]` with
`hunmixed ⇐ [hsucc_prefix, hdimEq]`), stated in `AssAvoidRung` form.

Conditional on exactly `[hsucc_pre, hdimEq, hmin]`. -/
theorem hassRung_of_hsuccPrefix_of_hdimEq_of_minAvoid (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hsucc_pre : RegularityBridge.SuccessiveSMulRegular
      (SuccClosureRungs.prefixSlice n K c hn j))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j))
    (hmin : MinAvoidRungs.MinAvoidRung n K c hn j) :
    MinAvoidRungs.AssAvoidRung n K c hn j :=
  (MinAvoidRungs.minAvoidRung_iff_assAvoidRung_of_minEqAss n K c hn j
    (MinSubsetAss.minEqAssRung_of_hsuccPrefix_of_hdimEq n K c hn j hj
      hsucc_pre hdimEq)).mp hmin

#print axioms hassRung_of_hsuccPrefix_of_hdimEq_of_minAvoid

/-- Per-rung `hass` from `[steps below j, HdimEq, minAvoid]` (no
`hsucc_prefix` hypothesis — conditional-exact): `Min = Ass` via the
`AssRungFeeds` below-steps master, then the per-rung iff. The
induction rung lemma feeding the §4 master.

Conditional on exactly `[hsteps, hdimEq, hmin]`. -/
theorem hassRung_of_steps_of_hdimEq_of_minAvoid (n : ℕ) (K : Type*)
    [Field K]
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
      (MinAvoidRungs.stageIdeal n K c hn j))
    (hmin : MinAvoidRungs.MinAvoidRung n K c hn j) :
    MinAvoidRungs.AssAvoidRung n K c hn j :=
  (MinAvoidRungs.minAvoidRung_iff_assAvoidRung_of_minEqAss n K c hn j
    (AssRungFeeds.minEqAssRung_of_steps_of_hdimEq n K c hn j hj
      hsteps hdimEq)).mp hmin

#print axioms hassRung_of_steps_of_hdimEq_of_minAvoid

/-- Span-shape rung step from `[steps below j, HdimEq, minAvoid]`
(conditional-exact): the rung lemma transported across the
step-`⟺`-`hass` iff — the shape converter into span-quotient form.

Conditional on exactly `[hsteps, hdimEq, hmin]`. -/
theorem stepSpanRung_of_steps_of_hdimEq_of_minAvoid (n : ℕ)
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
      (MinAvoidRungs.stageIdeal n K c hn j))
    (hmin : MinAvoidRungs.MinAvoidRung n K c hn j) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (MinAvoidRungs.stageIdeal n K c hn j •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mpr
    (hassRung_of_steps_of_hdimEq_of_minAvoid n K c hn j hj hsteps
      hdimEq hmin)

#print axioms stepSpanRung_of_steps_of_hdimEq_of_minAvoid

/-- Per-rung `minAvoid` from per-rung `hass` (unconditional
reduction): the `Min ⊆ Ass` leg is the closed `minSubAss` — the
per-rung form of the `MinSubsetAss` discharge, with the closed
lever applied pointwise.
-/
theorem minAvoidRung_of_hassRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (hass : MinAvoidRungs.AssAvoidRung n K c hn j) :
    MinAvoidRungs.MinAvoidRung n K c hn j :=
  MinAvoidRungs.hminAvoid_of_assAvoid_of_minSubAss
    (MinAvoidRungs.stageIdeal n K c hn j) ((bridgeSystem n K c hn) j)
    (MinSubsetAss.minSubAss_of_noetherian _) hass

#print axioms minAvoidRung_of_hassRung

/-- Per-prime `minAvoid` from per-prime Ass-avoidance (unconditional
reduction): the single-`(j, P)` minimal form — if `P` is minimal over
the stage ideal it is associated (closed `minSubAss`), hence the
fixed element is outside it.
-/
theorem minAvoidPrime_of_assAvoidPrime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hass : MinSubsetAss.AssAvoidPrime n K c hn j P) :
    MinAvoidRungs.MinAvoidPrime n K c hn j P :=
  fun hmin => hass (MinSubsetAss.minSubAss_of_noetherian _ P hmin)

#print axioms minAvoidPrime_of_assAvoidPrime

/-! ## §3. Prime-stage collapse (bank) -/

/-- `minAvoid` at a prime stage is a single non-membership
(unconditional iff reduction): both minimal and associated primes
are `{J}` (`MinSubsetAss.minEqAss_of_prime`, no hunmixed input), so
the per-rung minimal obligation is exactly the fixed next element
outside the stage ideal itself.
-/
theorem minAvoidRung_iff_single_of_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    [(MinAvoidRungs.stageIdeal n K c hn j).IsPrime] :
    MinAvoidRungs.MinAvoidRung n K c hn j ↔
      (bridgeSystem n K c hn) j ∉
        MinAvoidRungs.stageIdeal n K c hn j := by
  unfold MinAvoidRungs.MinAvoidRung
  rw [MinSubsetAss.minEqAss_of_prime]
  exact MinSubsetAss.assAvoidRung_iff_single_of_prime n K c hn j

#print axioms minAvoidRung_iff_single_of_prime

/-- The `∀`-form `minAvoid` splitter (conditional-exact): per-rung
case analysis — prime stages discharge by the single
non-membership (§3 iff), non-prime stages stay as the exact
terminal residual. This isolates the strictly narrower remainder
(`minAvoid` at non-prime stages only, given prime-stage singles).

Conditional on exactly `[hprime, hnonprime]`. -/
theorem minAvoid_all_of_primeSingle_of_nonprimeMin (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hprime : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      (bridgeSystem n K c hn) j ∉ MinAvoidRungs.stageIdeal n K c hn j)
    (hnonprime : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j := by
  intro j hj
  rcases Classical.em
    (MinAvoidRungs.stageIdeal n K c hn j).IsPrime with hP | hP
  · exact (@minAvoidRung_iff_single_of_prime n K _ c hn j hP).mpr
      (hprime j hj hP)
  · exact hnonprime j hj hP

#print axioms minAvoid_all_of_primeSingle_of_nonprimeMin

/-! ## §4. Master induction: `hass_all` from the terminal triple -/

/-- Full `hass_all` at bridge data from `[rung-1 step, ∀-HdimEq,
∀-minAvoid]` by strong rung induction (NO `hass` hypothesis): rung 0
via `FinalDischargeHub.bridgeSystem_rung_zero`, rung 1 by hypothesis,
rungs `≥ 2` via the §2 rung lemma with prefix steps built from the
IH (below-rung `hass` across the step-`⟺`-`hass` iff). The attack
endpoint: `hass_all` needs exactly the `SuccClosureRungs`-§4 triple. The
`hdimEq` binder is the verbatim §4 shape; the `hmin` binder is the
`MinAvoidRung` `∀`-form (definitionally the §4 binder — see the
`rfl` certificate below). The direct induction is proved rather than
composing the `SuccClosureRungs` §4 `hsucc` master with `hass ⟺ steps`, so
the per-rung reduction chain fires explicitly.

Conditional on exactly `[hrung1, hdimEq, hmin]`. -/
theorem hass_all_of_rung1step_of_hdimEq_of_minAvoid (K : Type*)
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
      MinAvoidRungs.AssAvoidRung n K c hn j := by
  have key : ∀ t : ℕ, ∀ j : Fin (statementIndex n + 1), j.val = t →
      2 ≤ j.val → MinAvoidRungs.AssAvoidRung n K c hn j := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t IH =>
      intro j hj_eq hj_ge2
      have hsteps : ∀ k : Fin (statementIndex n + 1),
          k.val < j.val →
          IsSMulRegular
            (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
              (Ideal.span
                (Set.image (bridgeSystem n K c hn)
                  {k' | k'.val < k.val}) •
              (⊤ : Submodule
                (MvPolynomial (Fin (statementIndex n + 2)) K)
                (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) k) := by
        intro k hk_lt
        by_cases hk0 : k.val = 0
        · have ek : k =
              (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
                Fin (statementIndex n + 1)) := Fin.ext hk0
          rw [ek]
          exact FinalDischargeHub.bridgeSystem_rung_zero n K c hn
        · by_cases hk1 : k.val = 1
          · exact hrung1 k hk1
          · have hk_ge2 : 2 ≤ k.val := by omega
            have hlt : k.val < t := by omega
            have hass_k := IH k.val hlt k rfl hk_ge2
            exact (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn k).mpr
              hass_k
      have hdimEq_j : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) := hdimEq j hj_ge2
      exact hassRung_of_steps_of_hdimEq_of_minAvoid n K c hn j hj_ge2
        hsteps hdimEq_j (hmin j hj_ge2)
  intro j hj
  exact key j.val j rfl hj

#print axioms hass_all_of_rung1step_of_hdimEq_of_minAvoid

/-- The `MinAvoidRung` `∀`-form is the `SuccClosureRungs`-§4 `hmin` binder
(unconditional, by `rfl`): the stage-ideal abbrev is reducible, so
the §4 master consumes the `MinAvoidRung` `∀`-form with no adapter.
-/
theorem minAvoid_all_iff_hmin_binder (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j) ↔
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P) :=
  Iff.rfl

#print axioms minAvoid_all_iff_hmin_binder

/-- Full `hass_all` from `[rung-1 step, HdimEq-SPEC, ∀-minAvoid]`
(conditional-exact): the §4 master on the named SPEC address
(`AssRungFeeds.HdimEqAllSpec`), via the SPEC-shim adapter.

Conditional on exactly `[hrung1, hspec, hmin]`. -/
theorem hass_all_of_rung1step_of_hdimEqSpec_of_minAvoid (K : Type*)
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
    (hspec : AssRungFeeds.HdimEqAllSpec n K c hn)
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  hass_all_of_rung1step_of_hdimEq_of_minAvoid K n hn c hrung1
    (AssRungFeeds.hdimEq_all_of_spec n K c hn hspec) hmin

#print axioms hass_all_of_rung1step_of_hdimEqSpec_of_minAvoid

/-- Full `hass_all` from `[rung-1 avoidance, ∀-HdimEq, ∀-minAvoid]`
(no step hypothesis — conditional-exact): the §4 master on the
fixed-family rung-1 input, via the rung-1 avoidance-`→`-step
converter. The two rung-1 routes coincide.

Conditional on exactly `[hrung1, hdimEq, hmin]`. -/
theorem hass_all_of_rung1Avoid_of_hdimEq_of_minAvoid (K : Type*)
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
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  hass_all_of_rung1step_of_hdimEq_of_minAvoid K n hn c
    (AssRungFeeds.rung1step_of_rung1Avoid n K c hn hrung1)
    hdimEq hmin

#print axioms hass_all_of_rung1Avoid_of_hdimEq_of_minAvoid

/-! ## §5. Residual register (doc only; see module docstring)

closed this lane: [stage-ideal chains]; [per-rung `hass` transport
+ span-step + minAvoid packaging]; [prime-stage collapse +
splitter]; [`hass_all` from the terminal triple + variants]. Open
(exact): [`minAvoid_all` — terminal (prime-collapse / step-mod
below)]; [rung-1 (HD-lane)]; [`HdimEq` crux (not owned)]. No new
remainder beyond the register.
-/

end AssReductionRungs
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
