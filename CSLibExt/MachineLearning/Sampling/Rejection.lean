/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Rejection sampling

Sample from a target `p : PMF α` using a proposal `q` and an envelope constant `M` with
`p ≤ M q`. Draw `x ~ q` and accept it with probability `p x / (M q x)` (`acceptProb`).
Otherwise, try again.

* `trial`: one round, as a law on (proposal, accepted?). `trial_apply_true`: `x` is proposed and
  accepted with probability `p x / M`. `tsum_trial_true`: a round accepts with probability `1 / M`.
* `trial_true_div_tsum`: conditional on acceptance, the proposal has law `p`.
* `tsum_rejections_mul_trial` (**rejection sampling outputs the target law**): over independent
  rounds, the output is `x` after exactly `k` rejections with probability `r ^ k P(x, accepted)`,
  where `r` is the rejection probability. Summing the geometric series over `k` gives `p x`.
* `eq_of_firstStep`: equivalently, `p` is the only finite solution of the first-step equation
  `out x = P(x, accepted) + r out x` satisfied by the law of the loop's output.

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004, §2.3.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §11.1.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open scoped ENNReal

variable {α : Type*}

/-- A coin that lands `true` with probability `r ≤ 1`. -/
noncomputable def coin (r : ℝ≥0∞) (hr : r ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b ↦ cond b r (1 - r)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    exact add_tsub_cancel_of_le hr)

/-- The acceptance probability `p x / (M q x)` of a proposal `x`. -/
noncomputable def acceptProb (p q : PMF α) (M : ℝ≥0∞) (x : α) : ℝ≥0∞ := p x / (M * q x)

theorem acceptProb_le_one {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (x : α) :
    acceptProb p q M x ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hM x)

/-- One round of **rejection sampling** for the target `p` with proposal `q` and envelope
constant `M` (`p ≤ M q`): draw `x ~ q`, then accept it with probability `p x / (M q x)`. The
result is the pair (proposal, accepted?). -/
noncomputable def trial (p q : PMF α) (M : ℝ≥0∞) (hM : ∀ x, p x ≤ M * q x) : PMF (α × Bool) :=
  q.bind fun x ↦ (coin (acceptProb p q M x) (acceptProb_le_one hM x)).map (Prod.mk x)

theorem trial_apply {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (x : α) (b : Bool) :
    trial p q M hM (x, b) = q x * coin (acceptProb p q M x) (acceptProb_le_one hM x) b := by
  classical
  rw [trial, PMF.bind_apply, tsum_eq_single x]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro b' hb'
      simp [Ne.symm hb']
  · intro y hy
    rw [PMF.map_apply]
    simp [Ne.symm hy]

/-- A proposal `x` is drawn and accepted with probability `p x / M`. -/
theorem trial_apply_true {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (x : α) :
    trial p q M hM (x, true) = p x / M := by
  rw [trial_apply, coin, PMF.ofFintype_apply, Bool.cond_true, acceptProb]
  by_cases hq : q x = 0
  · have hp : p x = 0 := le_antisymm (by simpa [hq] using hM x) bot_le
    simp [hq, hp]
  · rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr (PMF.apply_ne_top q x)) (Or.inr hq)]
    calc q x * (p x * (M⁻¹ * (q x)⁻¹)) = p x * M⁻¹ * (q x * (q x)⁻¹) := by ring
      _ = p x * M⁻¹ := by rw [ENNReal.mul_inv_cancel hq (PMF.apply_ne_top q x), mul_one]

/-- A round accepts with probability `1 / M`. -/
theorem tsum_trial_true {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) :
    ∑' x, trial p q M hM (x, true) = M⁻¹ := by
  simp_rw [trial_apply_true, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A round rejects with probability `1 - 1 / M`. -/
theorem tsum_trial_false_add {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) :
    ∑' x, trial p q M hM (x, false) + M⁻¹ = 1 := by
  have hprod := ENNReal.tsum_prod (f := fun (a : α) (b : Bool) ↦ trial p q M hM (a, b))
  rw [← tsum_trial_true hM, ← ENNReal.tsum_add, ← (trial p q M hM).tsum_coe]
  refine Eq.trans ?_ hprod.symm
  exact tsum_congr fun x ↦ (tsum_bool (f := fun b ↦ trial p q M hM (x, b))).symm

/-- **Conditional on acceptance, the proposal has the target law**: `P(x, accepted) / P(accepted)
= p x`. -/
theorem trial_true_div_tsum {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (hM0 : M ≠ 0)
    (hMt : M ≠ ∞) (x : α) :
    trial p q M hM (x, true) / ∑' y, trial p q M hM (y, true) = p x := by
  rw [trial_apply_true, tsum_trial_true, div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_assoc,
    ENNReal.inv_mul_cancel hM0 hMt, mul_one]

/-- **Rejection sampling outputs the target law.** Repeating independent rounds until one accepts,
the output is `x` after exactly `k` rejections with probability `r ^ k * P(x, accepted)`, where
`r` is the rejection probability. Summing over `k` gives `p x`. -/
theorem tsum_rejections_mul_trial {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x)
    (hM0 : M ≠ 0) (hMt : M ≠ ∞) (x : α) :
    ∑' k : ℕ, (∑' y, trial p q M hM (y, false)) ^ k * trial p q M hM (x, true) = p x := by
  have hsum := tsum_trial_false_add hM
  have hrt : ∑' y, trial p q M hM (y, false) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
  have hr : 1 - ∑' y, trial p q M hM (y, false) = M⁻¹ :=
    ENNReal.sub_eq_of_eq_add_rev hrt hsum.symm
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, hr, inv_inv, trial_apply_true,
    ENNReal.mul_div_cancel hM0 hMt]

/-- The same conclusion from the first-step equation: the output law `out` of the loop satisfies
`out x = P(x, accepted) + P(reject) * out x`, and `p` is its only finite solution. -/
theorem eq_of_firstStep {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (hM0 : M ≠ 0)
    (hMt : M ≠ ∞) {out : α → ℝ≥0∞} (hfin : ∀ x, out x ≠ ∞)
    (hout : ∀ x, out x = trial p q M hM (x, true) + (∑' y, trial p q M hM (y, false)) * out x)
    (x : α) : out x = p x := by
  set r := ∑' y, trial p q M hM (y, false)
  have hr1 : r ≤ 1 := by rw [← tsum_trial_false_add hM]; exact le_self_add
  have hrt : r * out x ≠ ∞ := ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hr1)
    (hfin x)
  have h1 : out x = r * out x + M⁻¹ * out x := by
    rw [← add_mul, tsum_trial_false_add hM, one_mul]
  have h2 : trial p q M hM (x, true) = M⁻¹ * out x := by
    have := (hout x).symm.trans h1
    rw [add_comm (r * out x)] at this
    exact (ENNReal.add_left_inj hrt).mp this
  rw [trial_apply_true, div_eq_mul_inv, mul_comm] at h2
  exact ((ENNReal.mul_right_inj (ENNReal.inv_ne_zero.mpr hMt) (ENNReal.inv_ne_top.mpr hM0)).mp
    h2).symm

end Cslib.MachineLearning.Sampling
