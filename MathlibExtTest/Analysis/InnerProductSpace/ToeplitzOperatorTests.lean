/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ToeplitzOperator

/-!
# Tests for Toeplitz operators on `ℓ²(ℕ, 𝕜)` with absolutely summable symbol

The test symbols are the delta symbols `δ₀`, `δ₁`, `δ₋₁` (finitely
supported, hence absolutely summable) and the two-term symbol supported on
`{0, 1}` with values `1, 2`.

* `T_{δ₀}` fixes `e₀` and `e₁` (it is the identity); `T_{δ₁}` is the
  unilateral shift (`e₀ ↦ e₁`); `T_{δ₋₁}` is the backward shift
  (`e₁ ↦ e₀`, `e₀ ↦ 0`).
* `‖T_{δ₁}‖ = ‖T_{δ₋₁}‖ = 1`.
* `(T_{δ₁})† = T_{δ₋₁}`, so `T_{δ₁}` is not self-adjoint, while the
  real delta symbol `δ₀ • 2` is self-adjoint.
* `T_{δ₀}` is not compact (its symbol is nonzero).
-/

open Set Filter Topology Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.ToeplitzOperator

namespace MathlibExtTest.Analysis.InnerProductSpace.ToeplitzOperatorTests

/-- The two-term symbol supported on `{0, 1}` with values `1, 2`. -/
private abbrev twoTerm : ℤ → ℂ :=
  fun k => if k = 0 then 1 else if k = 1 then 2 else 0

/-- The two-term symbol is absolutely summable. -/
private theorem summable_norm_twoTerm : Summable fun k => ‖twoTerm k‖ := by
  refine summable_of_ne_finset_zero (s := {0, 1}) ?_
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [twoTerm, hk.1, hk.2]

/-- `T_{δ₀}` fixes `e₀`. -/
example : toeplitzOperator (toeplitzDelta 0 (1 : ℂ)) (summable_norm_toeplitzDelta 0 1)
    (lp.single 2 0 (1 : ℂ)) = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [toeplitzOperator_apply,
    tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [toeplitzDelta, lp.single_apply]
  · simp [toeplitzDelta, lp.single_apply, hi]

/-- `T_{δ₀}` is the identity, so it fixes `e₁`. -/
example : toeplitzOperator (toeplitzDelta 0 (1 : ℂ)) (summable_norm_toeplitzDelta 0 1)
    (lp.single 2 1 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [toeplitzOperator_apply,
    tsum_eq_single 1 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 1
  · subst hi
    simp [toeplitzDelta, lp.single_apply]
  · have hne : (↑i - 1 : ℤ) ≠ 0 := by
      intro hcon
      apply hi
      have h1 : (↑i : ℤ) = 1 := by linarith [hcon]
      exact_mod_cast h1
    simp [toeplitzDelta, lp.single_apply, hi, hne]

/-- `T_{δ₁}` sends `e₀` to `e₁` (the unilateral shift). -/
example : toeplitzOperator (toeplitzDelta 1 (1 : ℂ)) (summable_norm_toeplitzDelta 1 1)
    (lp.single 2 0 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [toeplitzOperator_apply,
    tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 1
  · subst hi
    simp [toeplitzDelta, lp.single_apply]
  · simp [toeplitzDelta, lp.single_apply, hi]

/-- `T_{δ₋₁}` sends `e₁` to `e₀` (the backward shift). -/
example : toeplitzOperator (toeplitzDelta (-1) (1 : ℂ)) (summable_norm_toeplitzDelta (-1) 1)
    (lp.single 2 1 (1 : ℂ)) = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [toeplitzOperator_apply,
    tsum_eq_single 1 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [toeplitzDelta, lp.single_apply]
  · simp [toeplitzDelta, lp.single_apply, hi]

/-- `T_{δ₋₁}` kills `e₀`. -/
example : toeplitzOperator (toeplitzDelta (-1) (1 : ℂ)) (summable_norm_toeplitzDelta (-1) 1)
    (lp.single 2 0 (1 : ℂ)) = 0 := by
  apply lp.ext
  funext i
  rw [toeplitzOperator_apply,
    tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [toeplitzDelta, lp.single_apply]
  · simp [toeplitzDelta, lp.single_apply]

/-- The shift has operator norm `1`. -/
example : ‖toeplitzOperator (toeplitzDelta 1 (1 : ℂ)) (summable_norm_toeplitzDelta 1 1)‖ = 1 := by
  rw [norm_toeplitzOperator_delta]
  simp

/-- The backward shift has operator norm `1`. -/
example : ‖toeplitzOperator (toeplitzDelta (-1) (1 : ℂ))
    (summable_norm_toeplitzDelta (-1) 1)‖ = 1 := by
  rw [norm_toeplitzOperator_delta]
  simp

/-- The adjoint of the shift is the backward shift. -/
example : (toeplitzOperator (toeplitzDelta 1 (1 : ℂ)) (summable_norm_toeplitzDelta 1 1))† =
    toeplitzOperator (toeplitzDelta (-1) (1 : ℂ)) (summable_norm_toeplitzDelta (-1) 1) := by
  rw [adjoint_toeplitzOperator]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rw [toeplitzOperator_apply, toeplitzOperator_apply]
  apply tsum_congr
  intro j
  show star (toeplitzDelta 1 (1 : ℂ) (-((i : ℤ) - (j : ℤ)))) * x j =
    toeplitzDelta (-1) (1 : ℂ) ((i : ℤ) - (j : ℤ)) * x j
  by_cases hk : (i : ℤ) - (j : ℤ) = -1
  · have h2 : -((i : ℤ) - (j : ℤ)) = 1 := by omega
    have e1 : toeplitzDelta (-1) (1 : ℂ) ((i : ℤ) - (j : ℤ)) = 1 := by
      simp [toeplitzDelta, hk]
    have e2 : star (toeplitzDelta 1 (1 : ℂ) (-((i : ℤ) - (j : ℤ)))) = 1 := by
      rw [h2]
      simp [toeplitzDelta]
    rw [e1, e2]
  · have h2 : ((j : ℤ) - (i : ℤ)) ≠ 1 := by omega
    have e1 : toeplitzDelta (-1) (1 : ℂ) ((i : ℤ) - (j : ℤ)) = 0 := by
      simp [toeplitzDelta, hk]
    have e2 : star (toeplitzDelta 1 (1 : ℂ) (-((i : ℤ) - (j : ℤ)))) = 0 := by
      simp [toeplitzDelta, h2]
    rw [e1, e2]

/-- The shift is not self-adjoint. -/
example : ¬ IsSelfAdjoint (toeplitzOperator (toeplitzDelta 1 (1 : ℂ))
    (summable_norm_toeplitzDelta 1 1)) := by
  rw [isSelfAdjoint_toeplitzOperator_iff]
  intro h
  have h1 := h (-1)
  simp [toeplitzDelta, neg_neg] at h1

/-- The real delta symbol `δ₀ • 2` is self-adjoint. -/
example : IsSelfAdjoint (toeplitzOperator (toeplitzDelta 0 (2 : ℂ))
    (summable_norm_toeplitzDelta 0 2)) := by
  apply isSelfAdjoint_toeplitzOperator_of_forall_star
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [toeplitzDelta]
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp [toeplitzDelta, hk, hnk]

/-- `T_{δ₀}` is not compact: its symbol is nonzero. -/
example : ¬ IsCompactOperator (toeplitzOperator (toeplitzDelta 0 (1 : ℂ))
    (summable_norm_toeplitzDelta 0 1)) := by
  rw [isCompactOperator_toeplitzOperator_iff]
  intro h
  have h0 := congrFun h 0
  simp [toeplitzDelta] at h0

/-- The zero symbol gives the zero operator. -/
example : toeplitzOperator (0 : ℤ → ℂ) (by simp) = 0 := toeplitzOperator_zero

/-- The two-term symbol: `(T_a e₀) 0 = 1`. -/
example : toeplitzOperator twoTerm summable_norm_twoTerm (lp.single 2 0 (1 : ℂ)) 0 = 1 := by
  rw [toeplitzOperator_apply_single]
  norm_num [twoTerm]

/-- The two-term symbol: `(T_a e₀) 1 = 2`. -/
example : toeplitzOperator twoTerm summable_norm_twoTerm (lp.single 2 0 (1 : ℂ)) 1 = 2 := by
  rw [toeplitzOperator_apply_single]
  norm_num [twoTerm]

/-- The two-term symbol: `(T_a e₀) 2 = 0`. -/
example : toeplitzOperator twoTerm summable_norm_twoTerm (lp.single 2 0 (1 : ℂ)) 2 = 0 := by
  rw [toeplitzOperator_apply_single]
  norm_num [twoTerm]

end MathlibExtTest.Analysis.InnerProductSpace.ToeplitzOperatorTests
