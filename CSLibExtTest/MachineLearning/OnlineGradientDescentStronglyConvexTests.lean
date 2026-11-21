/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.OnlineGradientDescentStronglyConvex

/-!
# Tests for strongly convex online gradient descent regret

Concrete one-dimensional instances of `ogd_regret_strongly_convex`, direct
numeric checks of the harmonic estimate at `T = 1, 2, 3`, and axiom audits.
-/

namespace CSLibExtTest.MachineLearning.OnlineGradientDescentStronglyConvex

open Cslib.MachineLearning.OnlineGradientDescentStronglyConvex
open scoped InnerProductSpace

/-- T1 cost: `(1 / 2) * y ^ 2` (strongly convex with `α = 1`). -/
noncomputable def t1f : ℕ → ℝ → ℝ := fun _ y => (1 / 2 : ℝ) * y ^ 2

/-- T1 subgradient: `y` (i.e. `α * (y - xstar)` with `α = 1`, `xstar = 0`). -/
noncomputable def t1g : ℕ → ℝ → ℝ := fun _ y => y

/-- T1 iterates: constantly at the comparator `xstar = 0`. -/
noncomputable def t1x : ℕ → ℝ := fun _ => 0

/-- T1 projection: constantly `0` (singleton feasible set). -/
noncomputable def t1proj : ℝ → ℝ := fun _ => 0

/-- T1: on a singleton feasible set the regret is `0` by direct computation,
and the bound of `ogd_regret_strongly_convex` with `α = 1` and `G = 1` holds. -/
theorem t1_singleton_regret (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.range T, (t1f t (t1x t) - t1f t 0)) = 0 ∧
      (∑ t ∈ Finset.range T, (t1f t (t1x t) - t1f t 0))
        ≤ ((1 : ℝ) ^ 2 / (2 * 1)) * (1 + Real.log T) := by
  constructor
  · apply Finset.sum_eq_zero
    intro t _
    simp [t1f, t1x]
  · have hα : (0 : ℝ) < 1 := by norm_num
    have hG0 : (0 : ℝ) ≤ 1 := by norm_num
    have hproj : LipschitzWith 1 t1proj := by
      apply LipschitzWith.mk_one
      intro x y
      simp [t1proj]
    have hprojstar : t1proj 0 = 0 := rfl
    have hupd : ∀ t, t1x (t + 1) = t1proj (t1x t
      - (1 / (1 * ((t : ℝ) + 1))) • t1g t (t1x t)) := fun t => rfl
    have hsc : ∀ (t : ℕ) (y : ℝ), t1f t (t1x t)
        + ⟪t1g t (t1x t), y - t1x t⟫_ℝ + (1 / 2) * ‖y - t1x t‖ ^ 2
        ≤ t1f t y := by
      intro t y
      simp only [t1f, t1x, t1g, inner_zero_left, sub_zero]
      rw [Real.norm_eq_abs, sq_abs]
      simp
    have hG : ∀ t, ‖t1g t (t1x t)‖ ≤ 1 := fun t => by simp [t1g, t1x]
    exact ogd_regret_strongly_convex t1proj t1f t1g 1 1 t1x 0 T
      hα hG0 hproj hprojstar hupd hsc hG hT

/-- T2 cost: `(y - 1) ^ 2` (strongly convex with `α = 2`). -/
noncomputable def t2f : ℕ → ℝ → ℝ := fun _ y => (y - 1) ^ 2

/-- T2 subgradient: `2 * (y - 1)`. -/
noncomputable def t2g : ℕ → ℝ → ℝ := fun _ y => 2 * (y - 1)

/-- T2 iterates: `x 0 = 0`, then constantly at the comparator `xstar = 1`. -/
noncomputable def t2x : ℕ → ℝ := fun t => if t = 0 then 0 else 1

/-- T2: the explicit sequence satisfies the projected-gradient update with
`proj = id` and `α = 2`. -/
theorem t2_update : ∀ t, t2x (t + 1)
    = t2x t - (1 / (2 * ((t : ℝ) + 1))) • t2g t (t2x t) := by
  intro t
  by_cases ht : t = 0
  · subst ht
    norm_num [t2x, t2g, smul_eq_mul]
  · simp [t2x, t2g, ht, smul_eq_mul]

/-- T2 strong-convexity hypothesis for the quadratic instance. -/
theorem t2_hsc : ∀ (t : ℕ) (y : ℝ), t2f t (t2x t)
    + ⟪t2g t (t2x t), y - t2x t⟫_ℝ + (2 / 2 : ℝ) * ‖y - t2x t‖ ^ 2
    ≤ t2f t y := by
  intro t y
  have heq : t2f t (t2x t) + ⟪t2g t (t2x t), y - t2x t⟫_ℝ
      + (2 / 2 : ℝ) * ‖y - t2x t‖ ^ 2 = t2f t y := by
    simp only [t2f, t2g, Real.inner_apply, Real.norm_eq_abs, sq_abs]
    ring
  exact le_of_eq heq

/-- T2 gradient-norm hypothesis with `G = 2`. -/
theorem t2_hG : ∀ t, ‖t2g t (t2x t)‖ ≤ 2 := by
  intro t
  by_cases ht : t = 0
  · subst ht
    norm_num [t2g, t2x, Real.norm_eq_abs]
  · have hx : t2x t = 1 := by simp [t2x, ht]
    rw [hx]
    norm_num [t2g]

/-- T2: exact regret at `T = 1` is `1`. -/
theorem t2_regret_one :
    (∑ t ∈ Finset.range 1, (t2f t (t2x t) - t2f t 1)) = 1 := by
  rw [Finset.sum_range_one]
  norm_num [t2f, t2x]

/-- T2: exact regret at `T = 2` is `1`. -/
theorem t2_regret_two :
    (∑ t ∈ Finset.range 2, (t2f t (t2x t) - t2f t 1)) = 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_one]
  norm_num [t2f, t2x]

/-- T2: `ogd_regret_strongly_convex` on the quadratic instance. -/
theorem t2_bound (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.range T, (t2f t (t2x t) - t2f t 1))
      ≤ ((2 : ℝ) ^ 2 / (2 * 2)) * (1 + Real.log T) := by
  have hα : (0 : ℝ) < 2 := by norm_num
  have hG0 : (0 : ℝ) ≤ 2 := by norm_num
  have hproj : LipschitzWith 1 (id : ℝ → ℝ) :=
    LipschitzWith.mk_one fun x y => le_refl _
  have hprojstar : id (1 : ℝ) = 1 := rfl
  exact ogd_regret_strongly_convex id t2f t2g 2 2 t2x 1 T
    hα hG0 hproj hprojstar (fun t => t2_update t) t2_hsc t2_hG hT

/-- T2: `ogd_regret_strongly_convex` at `T = 1` with `G = 2`. -/
theorem t2_bound_one :
    (∑ t ∈ Finset.range 1, (t2f t (t2x t) - t2f t 1))
      ≤ ((2 : ℝ) ^ 2 / (2 * 2)) * (1 + Real.log 1) := by
  simpa using t2_bound 1 (by norm_num)

/-- T2: `ogd_regret_strongly_convex` at `T = 2` with `G = 2`. -/
theorem t2_bound_two :
    (∑ t ∈ Finset.range 2, (t2f t (t2x t) - t2f t 1))
      ≤ ((2 : ℝ) ^ 2 / (2 * 2)) * (1 + Real.log 2) := by
  simpa using t2_bound 2 (by norm_num)

/-- T2: at `T = 1` the regret `1` equals the bound (tightness). -/
theorem t2_cmp_one :
    (∑ t ∈ Finset.range 1, (t2f t (t2x t) - t2f t 1)) = 1 ∧
      (1 : ℝ) = ((2 : ℝ) ^ 2 / (2 * 2)) * (1 + Real.log 1) := by
  refine ⟨t2_regret_one, ?_⟩
  rw [Real.log_one]
  norm_num

/-- T2: at `T = 2` the regret `1` is below the bound. -/
theorem t2_cmp_two :
    (∑ t ∈ Finset.range 2, (t2f t (t2x t) - t2f t 1)) = 1 ∧
      (1 : ℝ) ≤ ((2 : ℝ) ^ 2 / (2 * 2)) * (1 + Real.log 2) := by
  refine ⟨t2_regret_two, ?_⟩
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfactor : ((2 : ℝ) ^ 2 / (2 * 2)) = 1 := by norm_num
  rw [hfactor, one_mul]
  linarith

/-- T3: harmonic estimate at `T = 1` by direct evaluation. -/
theorem t3_one :
    (∑ t ∈ Finset.range 1, (1 : ℝ) / ((t : ℝ) + 1)) ≤ 1 + Real.log 1 := by
  rw [Finset.sum_range_one, Real.log_one]
  norm_num

/-- Lower bound `1 / 2 ≤ log 2` from `log x ≤ x - 1` at `x = 1 / 2`. -/
theorem t3_log_two : ((1 : ℝ) / 2) ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have e : ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ := by norm_num
  rw [e, Real.log_inv] at h
  linarith

/-- T3: harmonic estimate at `T = 2` by direct evaluation. -/
theorem t3_two :
    (∑ t ∈ Finset.range 2, (1 : ℝ) / ((t : ℝ) + 1)) ≤ 1 + Real.log 2 := by
  have hLHS : (1 : ℝ) / ((0 : ℝ) + 1) + (1 : ℝ) / ((1 : ℝ) + 1) = 3 / 2 := by
    norm_num
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.cast_zero, Nat.cast_one, hLHS]
  linarith [t3_log_two]

/-- Lower bound `1 / 3 ≤ log (3 / 2)` from `log x ≤ x - 1` at `x = 2 / 3`. -/
theorem t3_log_three_halves : ((1 : ℝ) / 3) ≤ Real.log ((3 : ℝ) / 2) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
  have e : ((2 : ℝ) / 3) = ((3 : ℝ) / 2)⁻¹ := by norm_num
  rw [e, Real.log_inv] at h
  linarith

/-- T3: harmonic estimate at `T = 3` by direct evaluation. -/
theorem t3_three :
    (∑ t ∈ Finset.range 3, (1 : ℝ) / ((t : ℝ) + 1)) ≤ 1 + Real.log 3 := by
  have hdecomp : Real.log 3 = Real.log 2 + Real.log ((3 : ℝ) / 2) := by
    have e : (3 : ℝ) = 2 * (3 / 2) := by norm_num
    conv_lhs => rw [e]
    rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
      (show ((3 : ℝ) / 2) ≠ 0 by norm_num)]
  have hLHS : (1 : ℝ) / ((0 : ℝ) + 1) + (1 : ℝ) / ((1 : ℝ) + 1)
      + (1 : ℝ) / (((2 : ℕ) : ℝ) + 1) = 11 / 6 := by
    norm_num
  have h2 : (∑ t ∈ Finset.range 2, (1 : ℝ) / ((t : ℝ) + 1))
      = (1 : ℝ) / ((0 : ℝ) + 1) + (1 : ℝ) / ((1 : ℝ) + 1) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_one, Nat.cast_zero, Nat.cast_one]
  rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ, h2, hLHS]
  linarith [t3_log_two, t3_log_three_halves, hdecomp]

-- T4: axiom audit for the harmonic estimate and the regret bound.
#print axioms harmonic_sum_le_one_add_log
#print axioms ogd_regret_strongly_convex

end CSLibExtTest.MachineLearning.OnlineGradientDescentStronglyConvex
