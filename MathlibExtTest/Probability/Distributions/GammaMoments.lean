/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.GammaMoments

/-!
# Tests for moments, scaling and tails of the gamma law

The exponential special case (`a = 1`) of the mean and the tail, the variance at shape `2`, the
scaling law, the Erlang tail at shape `2`, the boundary `c = 0` of the tail (total mass `1`),
and the incomplete gamma function at its edges.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace MathlibExtTest.Probability.Distributions.GammaMoments

/-- `Γ(1, 0) = 1`. -/
example : upperIncompleteGamma 1 0 = 1 := by
  rw [upperIncompleteGamma_one, neg_zero, exp_zero]

/-- `Γ(a, 0) = Γ(a)` at `a = 3`: `Γ(3) = 2`. -/
example : upperIncompleteGamma 3 0 = 2 := by
  rw [upperIncompleteGamma_zero (by norm_num)]
  have h := Real.Gamma_nat_eq_factorial 2
  norm_num at h ⊢

/-- The closed form at shape `2`: `Γ(2, x) = (1 + x) e^{-x}`. -/
example {x : ℝ} (hx : 0 ≤ x) : upperIncompleteGamma 2 x = (1 + x) * exp (-x) := by
  have h := upperIncompleteGamma_natCast_add_one 1 hx
  norm_num [Finset.sum_range_succ] at h
  rw [h]
  ring

/-- The exponential law of rate `2` has mean `1 / 2`. -/
example : ∫ x, x ∂gammaMeasure 1 2 = 1 / 2 :=
  integral_id_gammaMeasure (by norm_num) (by norm_num)

/-- Shape `2`, rate `1`: variance `2`. -/
example : variance id (gammaMeasure 2 1) = 2 := by
  rw [variance_id_gammaMeasure (by norm_num) (by norm_num)]
  norm_num

/-- The third moment of the exponential law of rate `1` is `Γ(4) = 6`. -/
example : ∫ x, x ^ (3 : ℝ) ∂gammaMeasure 1 1 = 6 := by
  rw [integral_rpow_gammaMeasure (by norm_num) (by norm_num) (by norm_num)]
  have h := Real.Gamma_nat_eq_factorial 3
  norm_num at h ⊢

/-- Doubling a `Gamma(3, 4)` variable gives `Gamma(3, 2)`. -/
example : (gammaMeasure 3 4).map (fun x => 2 * x) = gammaMeasure 3 2 := by
  rw [gammaMeasure_map_const_mul (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Boundary `c = 0`: the gamma law gives the half-line `(0, ∞)` mass `1`. -/
example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : (gammaMeasure a r).real (Ioi 0) = 1 := by
  rw [gammaMeasure_real_Ioi ha hr le_rfl, mul_zero, upperIncompleteGamma_zero ha,
    div_self (Gamma_pos_of_pos ha).ne']

/-- The exponential tail `P(X > c) = e^{-r c}` from the Erlang formula at shape `1`. -/
example {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    (gammaMeasure 1 r).real (Ioi c) = exp (-(r * c)) := by
  have h := gammaMeasure_real_Ioi_natCast_add_one 0 hr hc
  norm_num at h
  exact h

/-- The Erlang tail at shape `2`: `P(X > c) = e^{-r c} (1 + r c)`. -/
example {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    (gammaMeasure 2 r).real (Ioi c) = exp (-(r * c)) * (1 + r * c) := by
  have h := gammaMeasure_real_Ioi_natCast_add_one 1 hr hc
  norm_num [Finset.sum_range_succ] at h
  exact h

end MathlibExtTest.Probability.Distributions.GammaMoments
