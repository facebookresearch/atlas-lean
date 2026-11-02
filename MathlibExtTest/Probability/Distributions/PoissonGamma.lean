/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonGamma

@[expose] public section

open Real Set Filter Topology ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.Distributions.PoissonGamma

/-! ### Concrete values of the distribution function -/

/-- `F_1(x) = e^{-x} (1 + x)`. -/
example (x : ℝ) : poissonCDF x 1 = exp (-x) * (1 + x) := by
  simp [poissonCDF, Finset.sum_range_succ]; ring

/-- At mean `0` every `F_k` is `1` (point mass at `0`). -/
example : poissonCDF 0 5 = 1 := poissonCDF_zero_left 5

/-- `F_k` is the Poisson distribution function: `P(Poisson(2) ≤ 0) = e^{-2}`. -/
example : (poissonMeasure 2).real (Set.Iic 0) = exp (-2) := by
  rw [poissonMeasure_real_Iic, poissonCDF_zero_right]; norm_num

/-- Poisson–Gamma duality at `k = 0`: the exponential law of rate `r` has tail `e^{-r x}`. -/
example {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    (gammaMeasure ((0 : ℕ) + 1) r).real (Ioi x) = exp (-(r * x)) := by
  rw [gammaMeasure_real_Ioi_poissonCDF 0 hr hx, poissonCDF_zero_right]

/-- Monotone in `k` and in the mean, on concrete points. -/
example : poissonCDF 1 2 < poissonCDF 1 3 ∧ poissonCDF 2 3 < poissonCDF 1 3 :=
  ⟨poissonCDF_lt_poissonCDF_succ one_pos 2,
    poissonCDF_strictAntiOn 3 (by norm_num : (1 : ℝ) ∈ Ici 0) (by norm_num) (by norm_num)⟩

/-! ### Garwood's bound -/

/-- With no events, the 95% upper bound (`α = 1/20`) is `log 20`. -/
example : garwoodUpper (1 / 20) 0 = log 20 := by
  rw [garwoodUpper_zero (by norm_num) (by norm_num)]; norm_num

/-- The bound solves `F_k(u) = α`, here for `k = 3`, `α = 1/10`. -/
example : poissonCDF (garwoodUpper (1 / 10) 3) 3 = 1 / 10 :=
  poissonCDF_garwoodUpper (by norm_num) (by norm_num) 3

/-- More events give a larger bound. -/
example : garwoodUpper (1 / 20) 2 < garwoodUpper (1 / 20) 5 :=
  garwoodUpper_strictMono (by norm_num) (by norm_num) (by norm_num)

/-- Exact coverage for the true mean `3` at level `1/10`. -/
example : 1 - 1 / 10 ≤ (poissonMeasure 3).real {k | ((3 : ℝ≥0) : ℝ) ≤ garwoodUpper (1 / 10) k} :=
  garwoodUpper_coverage 3 (by norm_num) (by norm_num)

/-- Super-uniformity at the boundary `α = 0`: `P(F_r(K) ≤ 0) ≤ 0`. -/
example (r : ℝ≥0) : (poissonMeasure r).real {k | poissonCDF r k ≤ 0} ≤ 0 :=
  poissonMeasure_real_poissonCDF_le r le_rfl

/-- Junk value outside `0 < α < 1`: at `α = 0` every `x ≥ 0` qualifies, the set is unbounded,
and `sSup` returns `0`. -/
example (k : ℕ) : garwoodUpper 0 k = 0 := by
  unfold garwoodUpper
  apply Real.sSup_of_not_bddAbove
  rintro ⟨b, hb⟩
  have h0 : (0 : ℝ) ≤ |b| + 1 := by positivity
  have h := hb ⟨h0, (poissonCDF_pos h0 k).le⟩
  linarith [le_abs_self b]

end MathlibExtTest.Probability.Distributions.PoissonGamma
