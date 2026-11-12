/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.Pinsker
public import MathlibExt.InformationTheory.PinskerPMF

@[expose] public section

/-!
# Tests for Pinsker's inequality on PMFs

Concrete laws on `Bool` with a zero coordinate: an absolutely continuous pair with finite
divergence, and a pair that is not absolutely continuous, where the divergence is infinite.
-/

set_option autoImplicit false

open MeasureTheory Real InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.PinskerPMF

/-- A fair coin. -/
noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

theorem fair_apply (b : Bool) : (fair b).toReal = 1 / 2 := by
  simp [fair]

theorem pure_true_apply (b : Bool) : ((PMF.pure true) b).toReal = if b then 1 else 0 := by
  cases b <;> simp [PMF.pure_apply]

/-- The `L1` distance between a point mass and a fair coin is `1`, in either order. -/
theorem l1_pure_fair :
    ∑ b, |((PMF.pure true) b).toReal - (fair b).toReal| = 1 := by
  rw [Fintype.sum_bool, pure_true_apply, pure_true_apply, fair_apply, fair_apply]
  norm_num

theorem l1_fair_pure :
    ∑ b, |(fair b).toReal - ((PMF.pure true) b).toReal| = 1 := by
  rw [Fintype.sum_bool, pure_true_apply, pure_true_apply, fair_apply, fair_apply]
  norm_num

/-! ### Absolutely continuous, finite divergence

`PMF.pure true` has a zero coordinate at `false`, where the fair coin is positive. -/

theorem pure_ac_fair : ∀ b, fair b = 0 → (PMF.pure true) b = 0 := by
  intro b hb
  simp [fair] at hb

/-- The divergence is finite. -/
example : klDiv (PMF.pure true).toMeasure fair.toMeasure ≠ ∞ :=
  klDiv_ne_top (toMeasure_absolutelyContinuous pure_ac_fair) Integrable.of_finite

/-- Its value is `log 2` nats. -/
theorem toReal_klDiv_pure_fair :
    (klDiv (PMF.pure true).toMeasure fair.toMeasure).toReal = log 2 := by
  rw [toReal_klDiv_toMeasure pure_ac_fair, Fintype.sum_bool, pure_true_apply, pure_true_apply,
    fair_apply, fair_apply]
  norm_num

/-- Pinsker on the concrete pair: `1 ≤ 2 KL`, with the right side finite. -/
example : ENNReal.ofReal 1 ≤ 2 * klDiv (PMF.pure true).toMeasure fair.toMeasure := by
  have h := InformationTheory.pinsker_pmf (PMF.pure true) fair
  rwa [l1_pure_fair, one_pow] at h

/-! ### Not absolutely continuous, infinite divergence

The fair coin charges `false`, which `PMF.pure true` rules out. -/

theorem not_ac_fair_pure : ¬ fair.toMeasure ≪ (PMF.pure true).toMeasure := by
  intro h
  have hq : (PMF.pure true).toMeasure {false} = 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.pure_apply]
  have hp := h hq
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at hp
  simp [fair] at hp

theorem klDiv_fair_pure : klDiv fair.toMeasure (PMF.pure true).toMeasure = ∞ :=
  klDiv_of_not_ac not_ac_fair_pure

/-- Pinsker on the concrete pair holds because the right side is `∞`. -/
example : ENNReal.ofReal 1 ≤ 2 * klDiv fair.toMeasure (PMF.pure true).toMeasure := by
  have h := InformationTheory.pinsker_pmf fair (PMF.pure true)
  rwa [l1_fair_pure, one_pow] at h

/-- The `toReal` form of Pinsker is false on this pair, which is why `pinsker_pmf` is stated in
`ℝ≥0∞`. -/
example :
    ¬ (∑ b, |(fair b).toReal - ((PMF.pure true) b).toReal|) ^ 2 ≤
      2 * (klDiv fair.toMeasure (PMF.pure true).toMeasure).toReal := by
  rw [l1_fair_pure, klDiv_fair_pure]
  norm_num

/-! ### Shared real-valued API -/

/-- The real theorem allows a common zero coordinate and a zero numerator. -/
example : (1 : ℝ) ≤ 2 * log 2 := by
  let p : Fin 3 → ℝ := ![1, 0, 0]
  let q : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]
  have h := MathlibExt.InformationTheory.Pinsker.csiszar_kullback_pinsker_of_support p q
    (by intro a; fin_cases a <;> norm_num [p])
    (by intro a; fin_cases a <;> norm_num [q])
    (by norm_num [p, Fin.sum_univ_succ])
    (by norm_num [q, Fin.sum_univ_succ])
    (by intro a; fin_cases a <;> norm_num [p, q])
  norm_num [p, q, Fin.sum_univ_succ] at h ⊢
  exact h

/-- The strict-positive public signature is preserved as a corollary. -/
example {α : Type*} [Fintype α] [Nonempty α] (p q : α → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (hp_sum : ∑ a, p a = 1) (hq_sum : ∑ a, q a = 1) :
    (∑ a, |p a - q a|) ^ 2 ≤ 2 * ∑ a, p a * log (p a / q a) :=
  MathlibExt.InformationTheory.Pinsker.csiszar_kullback_pinsker
    p q hp hq hp_sum hq_sum

end MathlibExtTest.InformationTheory.PinskerPMF
