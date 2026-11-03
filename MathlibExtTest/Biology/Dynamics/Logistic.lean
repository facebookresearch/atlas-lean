/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.Logistic

/-!
# Tests for the logistic growth equation

Initial value, the ODE at a concrete point, the convergence and exponential limits, the exact
transit time for `N = 2` (`(2 / r) log 3`), the boundary case `N = 1` (time `0`), monotonicity,
and the junk value of the explicit formula where its denominator vanishes.
-/

@[expose] public section

open Real Filter Set
open scoped Topology
open MathlibExt.Biology.Dynamics.Logistic

namespace MathlibExtTest.Biology.Dynamics.Logistic

/-- The explicit solution starts at `x₀`. -/
example : logistic 2 10 3 0 = 3 := logistic_zero 3 (by norm_num)

/-- With `x₀ = K` the population stays at the carrying capacity. -/
example (r t : ℝ) : logistic r 5 5 t = 5 := by
  have := exp_pos (r * t)
  simp only [logistic]
  field_simp
  ring

/-- The ODE holds for every time when `0 < x₀ ≤ K`. -/
example (t : ℝ) :
    HasDerivAt (logistic 1 2 1) (1 * logistic 1 2 1 t * (1 - logistic 1 2 1 t / 2)) t :=
  hasDerivAt_logistic (by norm_num)
    (logistic_denom_pos (by norm_num) (by norm_num) (Or.inr (by norm_num))).ne'

/-- Uniqueness on `[0, 1]` for the biological domain. -/
example {x : ℝ → ℝ} (hc : ContinuousOn x (Icc 0 1))
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt x (2 * x t * (1 - x t / 3)) (Ici t) t)
    (h0 : x 0 = 1) : EqOn x (logistic 2 3 1) (Icc 0 1) :=
  eqOn_logistic_of_hasDerivWithinAt (by norm_num) (by norm_num) (by norm_num) hc hd h0

/-- Convergence to the carrying capacity. -/
example : Tendsto (logistic 1 7 1) atTop (𝓝 7) :=
  tendsto_logistic_atTop (by norm_num) (by norm_num)

/-- The exponential-growth limit `K → ∞`. -/
example : Tendsto (fun K => logistic 1 K 2 3) atTop (𝓝 (2 * exp (1 * 3))) :=
  tendsto_logistic_carryingCapacity_atTop 1 2 3

/-- Log-odds are linear in time. -/
example : log (logistic 2 1 (1 / 2) 3 / (1 - logistic 2 1 (1 / 2) 3)) = 2 * 3 := by
  rw [logit_logistic (by norm_num) (by norm_num)]
  norm_num

/-- Transit time for `N = 2` (from `1/4` to `3/4`): `(2 / r) log 3`. -/
example : logistic 5 1 (1 / (2 * (2 : ℕ))) (2 / 5 * log (2 * (2 : ℕ) - 1)) =
    1 - 1 / (2 * (2 : ℕ)) :=
  logistic_transitTime_twoN (by norm_num) (by norm_num)

/-- Boundary case `N = 1`: the transit time `(2 / r) log 1` is `0` and `1/2 = 1 - 1/2`. -/
example (r : ℝ) : (2 / r) * log (2 * (1 : ℕ) - 1) = 0 := by norm_num

/-- The logistic solution is strictly increasing below the carrying capacity. -/
example : StrictMono (logistic 1 4 1) :=
  strictMono_logistic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Junk value: outside the domain (`x₀ > K`, `r t < 0`) the denominator can vanish, and the
formula then returns `0` (division by zero), which is not a solution value. Here
`K = 1`, `x₀ = 2`, `e^{r t} = 1/2`. -/
example : logistic (log (1 / 2)) 1 2 1 = 0 := by
  simp only [logistic, mul_one]
  rw [exp_log (by norm_num)]
  norm_num

end MathlibExtTest.Biology.Dynamics.Logistic
