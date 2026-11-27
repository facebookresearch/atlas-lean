/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.SharpnessFK
public import CSLibExtTest.Complexity.BooleanFunctions.CovLowerBound

/-!
# Tests for the Grönwall bootstrap and the scaled-decay algebra lemma

Tests for `CSLibExt.Complexity.BooleanFunctions.SharpnessFK`:

* `var_indicator` / `var_eventIndicator` for `andEvent` at `p = 1/2` (`3/16 = 1/4 · 3/4`);
* `covSum_ge_of_indicator` with every hypothesis discharged for the one-tree family `andTree`;
* `gronwall_lower`, `subcritical_decay` and `subcritical_decay_box` for the exponential
  `θ x = exp (rate · (x - b))`, which satisfies the differential inequality with equality, so the
  decay bound is attained;
* `differential_inequality` at explicit numbers;
* `scaled_decay_of_scalar_identity` for `q = 2` and `q = 3`, where the scalar factor is `1/2` and `2/3`.

The file contains no sharpness theorem (see its module doc), so there is no sharpness statement
to test.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.OSSS.CovLowerBound StatMech.OSSS.SharpnessFK Set

/-! ## Variance of an event -/

example : var νHalf (andEvent.indicator (fun _ => (1 : ℝ)))
    = expect νHalf (andEvent.indicator (fun _ => (1 : ℝ)))
      * (1 - expect νHalf (andEvent.indicator (fun _ => (1 : ℝ)))) :=
  var_eventIndicator andEvent

/-- `var_eventIndicator` for `andEvent`: `P(andEvent) = 1/4` and `Var = 1/4 · 3/4 = 3/16`. -/
example : var νHalf (andEvent.indicator (fun _ => (1 : ℝ))) = 3 / 16 := by
  rw [var_eventIndicator, ← andTree_evalR_eq, expect_andTree]; norm_num

/-- `covSum_ge_of_indicator` for the one-tree family `andTree`: `1/4 · (1/4 · 3/4) ≤ 1/4`. -/
example : (1 / 4 : ℝ) * (1 / 4 * (1 - 1 / 4)) ≤ 1 / 4 := by
  have h := covSum_ge_of_indicator (κ := Unit) νHalf_isProbWeight andEvent_isIncreasing
    (fun _ => andTree) (fun _ => andTree_evalR_eq) (fun _ e => reveal νHalf andTree e)
    (fun _ _ => le_rfl) (1 / 4) (by norm_num) siteVar_νHalf 1 zero_le_one
    (fun e => by simpa using reveal_andTree_le_one e)
  rw [← andTree_evalR_eq, expect_andTree, andTree_evalR_eq, Fintype.sum_bool,
    cov_coordI_andEvent, cov_coordI_andEvent] at h
  norm_num at h ⊢

/-! ## The Grönwall bootstrap -/

/-- The exponential `x ↦ exp (rate · (x - b))` has derivative `rate · exp (rate · (x - b))`. -/
lemma hasDerivAt_expAffine (rate b x : ℝ) :
    HasDerivAt (fun y => Real.exp (rate * (y - b))) (rate * Real.exp (rate * (x - b))) x := by
  have h : HasDerivAt (fun y => rate * (y - b)) rate x := by
    simpa using ((hasDerivAt_id x).sub_const b).const_mul rate
  simpa [mul_comm] using h.exp

/-- `gronwall_lower` for `f x = exp (2 x)` with the non-optimal rate `λ = 1` on `[0, 1]`
(the inequality `f ≤ f' = 2 f` is strict): `exp 1 · f 0 ≤ f 1`. -/
example : Real.exp (1 * (1 - 0)) * Real.exp (2 * (0 - 0)) ≤ Real.exp (2 * (1 - 0)) :=
  gronwall_lower 0 1 1 zero_le_one (fun y => Real.exp (2 * (y - 0)))
    (fun x => 2 * Real.exp (2 * (x - 0))) (fun x _ => hasDerivAt_expAffine 2 0 x)
    (fun x _ => by have := Real.exp_pos (2 * (x - 0)); linarith)

/-- `subcritical_decay` for `θ x = exp (2 (x - 1))` on `[0, 1]`: the bound `θ 0 ≤ exp (-2)` is
attained. -/
example : Real.exp (2 * (0 - 1)) ≤ Real.exp (-(2 * (1 - 0))) ∧ Real.exp (-(2 * (1 - 0))) < 1 := by
  have h := subcritical_decay 0 1 2 zero_lt_one two_pos (fun y => Real.exp (2 * (y - 1)))
    (fun x => 2 * Real.exp (2 * (x - 1))) (fun x _ => hasDerivAt_expAffine 2 1 x)
    (fun _ _ => le_rfl) (Real.exp_pos _).le (by simp)
  exact h.2

example : Real.exp ((1 * 3) * (0 - 1)) ≤ Real.exp (-(1 * (3 : ℕ) * (1 - 0))) :=
  subcritical_decay_box 0 1 1 3 zero_lt_one one_pos (by norm_num)
    (fun y => Real.exp ((1 * 3) * (y - 1))) (fun x => (1 * 3) * Real.exp ((1 * 3) * (x - 1)))
    (fun x _ => hasDerivAt_expAffine (1 * 3) 1 x) (fun _ _ => by push_cast; exact le_rfl)
    (Real.exp_pos _).le (by simp)

/-- `differential_inequality` at `n = 2`, `c₀ = 1/4`, `cR = 1`, `D = 1`, `θ = 1/2`, `S = 1/8`,
`θ' = 1/8`. -/
example : (2 : ℕ) * (1 / 4 : ℝ) * 1 / 1 * (1 / 2 * (1 - 1 / 2)) ≤ 1 / 8 :=
  differential_inequality 2 (1 / 4) 1 1 (1 / 2) (1 / 8) (1 / 8) one_pos (by norm_num)
    (by norm_num) zero_le_one

/-! ## The scaled-decay algebra lemma -/

/-- `scaled_decay_of_scalar_identity` for `q = 2`, with `x = exp (-c)`: the scaled bound
implies the unscaled one since the scalar factor `(2 - 1) / 2` is at most `1`. -/
example (c : ℝ) : 0 ≤ (2 - 1) / 2 * Real.exp (-c) ∧ (2 - 1) / 2 * Real.exp (-c) ≤ Real.exp (-c) := by
  have h := scaled_decay_of_scalar_identity 2 le_rfl c (Real.exp (-c)) _ rfl
    (Real.exp_pos _).le le_rfl
  refine ⟨h.1, le_trans h.2 ?_⟩
  calc (2 - 1) / 2 * Real.exp (-c) ≤ 1 * Real.exp (-c) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    _ = Real.exp (-c) := one_mul _

example : 0 ≤ (2 / 3 : ℝ) * (1 / 2) ∧ (2 / 3 : ℝ) * (1 / 2) ≤ Real.exp (-Real.log 2) := by
  have h := scaled_decay_of_scalar_identity 3 (by norm_num) (Real.log 2) (1 / 2)
    ((2 / 3) * (1 / 2)) (by norm_num) (by norm_num)
    (by rw [Real.exp_neg, Real.exp_log two_pos]; norm_num)
  refine ⟨h.1, le_trans h.2 ?_⟩
  calc (3 - 1) / 3 * Real.exp (-Real.log 2) ≤ 1 * Real.exp (-Real.log 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    _ = Real.exp (-Real.log 2) := one_mul _

end StatMechTest.BooleanFunctions
