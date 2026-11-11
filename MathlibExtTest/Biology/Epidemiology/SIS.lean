/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SIS

/-!
# Tests for the closed-population SIS model

The concrete model `β = 2`, `γ = 1`, `N = 1`, `I₀ = 1/100` (`R₀ = 2`): initial value,
positivity and invariance at a concrete time, the endemic limit `1/2`, and `R₀ = 2`. Also the
critical case `β = γ` at a concrete time (algebraic decay), `β = 0` (pure exponential decay),
`I₀ = 0` (constant), the subcritical limit, the time function `growthIntegral`, non-vacuity of
`IsSolution` and of the uniqueness/limit hypotheses, and the linearized threshold.
-/

open Real Filter Set Matrix
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SIS

open MathlibExt.Biology.Epidemiology.SIS

/-! ### `growthIntegral` -/

example : growthIntegral 0 3 = 3 := growthIntegral_zero_left 3

example (r : ℝ) : growthIntegral r 0 = 0 := growthIntegral_zero_right r

example : growthIntegral 1 1 = exp 1 - 1 := by
  rw [growthIntegral_of_ne_zero one_ne_zero]; simp

/-- For `r < 0` and `t ≥ 0` the time function is still nonnegative. -/
example : 0 ≤ growthIntegral (-1) 5 := growthIntegral_nonneg _ (by norm_num)

/-! ### The concrete model `β = 2`, `γ = 1`, `N = 1`, `I₀ = 1/100` -/

example : sisInfected 2 1 1 (1 / 100) 0 = 1 / 100 := sisInfected_zero _ _ _ _

example : sisSusceptible 2 1 1 (1 / 100) 0 = 99 / 100 := by
  simp [sisSusceptible]; norm_num

/-- Positivity at `t = 1`. -/
example : 0 < sisInfected 2 1 1 (1 / 100) 1 := by
  have hD := one_le_sisDenom (β := 2) (γ := 1) (N := 1) (I₀ := 1 / 100) (t := 1) (by norm_num)
    one_pos (by norm_num) zero_le_one
  exact div_pos (mul_pos (by norm_num) (exp_pos _)) (by linarith)

/-- Invariance of `[0, N]` at `t = 1`. -/
example : sisInfected 2 1 1 (1 / 100) 1 ∈ Icc 0 1 :=
  sisInfected_mem_Icc (by norm_num) (by norm_num) one_pos (by norm_num) zero_le_one

/-- The explicit pair solves the SIS system (non-vacuity of `IsSolution`). -/
example : IsSolution 2 1 1 (sisSusceptible 2 1 1 (1 / 100)) (sisInfected 2 1 1 (1 / 100)) :=
  isSolution_sis (by norm_num) one_pos (by norm_num)

/-- **Endemic limit** `I* = N (1 - γ / β) = 1/2`. -/
example : Tendsto (sisInfected 2 1 1 (1 / 100)) atTop (𝓝 (1 / 2)) := by
  have := tendsto_sisInfected_endemic (β := 2) (γ := 1) (N := 1) (I₀ := 1 / 100) zero_le_one
    (by norm_num) one_ne_zero (by norm_num)
  norm_num at this ⊢
  exact this

/-- The endemic limit for an arbitrary solution of the concrete model (hypotheses satisfiable:
applied to the explicit solution). -/
example : Tendsto (sisInfected 2 1 1 (1 / 100)) atTop (𝓝 (1 * (1 - 1 / 2))) :=
  (isSolution_sis (γ := 1) (by norm_num) one_pos (by norm_num)).tendsto_infected_endemic
    zero_le_one (by norm_num) one_pos (by simp [sisSusceptible]) (by norm_num)

/-- Bridge to the logistic solution, carrying capacity `K = N (β - γ) / β = 1/2`. -/
example (t : ℝ) : sisInfected 2 1 1 (1 / 100) t =
    MathlibExt.Biology.Dynamics.Logistic.logistic 1 (1 / 2) (1 / 100) t := by
  rw [sisInfected_eq_logistic (by norm_num) (by norm_num) one_ne_zero]; norm_num

/-- **`R₀ = 2`.** -/
example : MathlibExt.Biology.Epidemiology.NextGenerationMatrix.R0 !![(2 : ℝ)] !![1] = 2 := by
  rw [R0_eq (by norm_num) one_pos]; norm_num

/-! ### Critical, subcritical and degenerate cases -/

/-- **Critical case `β = γ = 1`, `N = 1`, `I₀ = 1/2`**: `I(2) = (1/2) / (1 + 1) = 1/4`. -/
example : sisInfected 1 1 1 (1 / 2) 2 = 1 / 4 := by
  simp [sisInfected]; norm_num

/-- `β = 0`: pure exponential decay `I(t) = I₀ e^{-γ t}`. -/
example (I₀ t : ℝ) : sisInfected 0 3 1 I₀ t = I₀ * exp (-3 * t) := by
  simp [sisInfected]

/-- `I₀ = 0`: the explicit solution is constant `0`. -/
example (t : ℝ) : sisInfected 2 1 1 0 t = 0 := sisInfected_zero_left _ _ _ _

/-- Subcritical extinction, `β = 1 < γ = 2`. -/
example : Tendsto (sisInfected 1 2 1 (1 / 2)) atTop (𝓝 0) :=
  tendsto_sisInfected_zero (by norm_num) (by norm_num) (by norm_num) one_pos (by norm_num)

/-- Critical extinction, `β = γ = 1` (algebraic decay). -/
example : Tendsto (sisInfected 1 1 1 (1 / 2)) atTop (𝓝 0) :=
  tendsto_sisInfected_zero (by norm_num) one_pos le_rfl one_pos (by norm_num)

/-- `β = 0` extinction. -/
example : Tendsto (sisInfected 0 1 1 1) atTop (𝓝 0) :=
  tendsto_sisInfected_zero le_rfl one_pos zero_le_one one_pos zero_le_one

/-! ### Existence, uniqueness, equilibria -/

example : ∃ S I : ℝ → ℝ, IsSolution 2 1 1 S I ∧ I 0 = 1 / 100 ∧ S 0 = 1 - 1 / 100 ∧
    ∀ t, 0 ≤ t → I t ∈ Icc 0 1 :=
  exists_isSolution (by norm_num) (by norm_num) one_pos (by norm_num)

/-- Uniqueness identifies the explicit solution with itself through `infected_eq_sisInfected`
(hypotheses satisfiable). -/
example (t : ℝ) (ht : 0 ≤ t) :
    sisInfected 2 1 1 (1 / 100) t = sisInfected 2 1 1 (sisInfected 2 1 1 (1 / 100) 0) t :=
  (isSolution_sis (γ := 1) (by norm_num) one_pos (by norm_num)).infected_eq_sisInfected
    (by norm_num) one_pos (by simp [sisSusceptible]) (by norm_num) ht

example : IsSolution 2 1 1 (fun _ => 1) (fun _ => 0) := isSolution_const_zero _ _ _

/-- The endemic equilibrium `(S, I) ≡ (1/2, 1/2)` for `β = 2`, `γ = 1`, `N = 1`. -/
example : IsSolution 2 1 1 (fun _ => 1 * 1 / 2) (fun _ => 1 * (1 - 1 / 2)) :=
  isSolution_const_endemic (by norm_num)

/-- Threshold at `t = 0` for the concrete model: `R₀ S(0) / N = 2 · 99/100 > 1`. -/
example : 0 < deriv (sisInfected 2 1 1 (1 / 100)) 0 := by
  rw [(isSolution_sis (γ := 1) (by norm_num) one_pos (by norm_num)).deriv_infected_pos_iff
    one_pos one_pos (by simp)]
  simp [sisSusceptible]; norm_num

/-! ### The linearized threshold -/

example : (!![(1 : ℝ)] - !![2]).IsHurwitz := (isHurwitz_iff (by norm_num) (by norm_num)).2
  (by norm_num)

example : ¬ (!![(2 : ℝ)] - !![1]).IsHurwitz := by
  rw [isHurwitz_iff (by norm_num) one_pos]; norm_num

example : ∃ μ ∈ spectrum ℂ ((!![(2 : ℝ)] - !![1]).map (algebraMap ℝ ℂ)), 0 < μ.re :=
  (exists_re_pos_iff (by norm_num) one_pos).2 (by norm_num)

example : spectrum ℂ ((!![(3 : ℝ)]).map (algebraMap ℝ ℂ)) = {(3 : ℂ)} := by
  simpa using spectrum_one_by_one 3

/-! ### `F` and `V` as derivatives at the disease-free equilibrium -/

/-- `∂ℱ/∂I = β` at `(S, I) = (N, 0)`, for `β = 2`, `N = 5`. -/
example :
    HasDerivAt (fun x : ℝ => 2 * 5 * x / 5) ((!![(2 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0) 0 :=
  hasDerivAt_newInfections_dfe (by norm_num)

example : HasDerivAt (fun x : ℝ => 2 * (5 - x) * x / 5)
    ((!![(2 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0) 0 :=
  hasDerivAt_newInfections_closed_dfe (by norm_num)

example : HasDerivAt (fun x : ℝ => 1 * x) ((!![(1 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0) 0 :=
  hasDerivAt_transfers_dfe 1

/-- The SIS infected rate at `β = 2`, `γ = 1`, `N = 1` has Jacobian `(F - V)₀₀ = 1` at the
disease-free state. -/
example : HasDerivAt (fun x : ℝ => 2 * (1 - x) * x / 1 - 1 * x)
    ((!![(2 : ℝ)] - !![1] : Matrix (Fin 1) (Fin 1) ℝ) 0 0) 0 :=
  hasDerivAt_infectedField_zero 1 one_ne_zero

/-- **Boundary `N = 0`**: Lean's `x / 0 = 0` makes the new-infection map identically `0`, so its
derivative is `0`, not `β = 2`. This is why the `F`-entry lemmas assume `N ≠ 0`. -/
example : HasDerivAt (fun x : ℝ => 2 * (0 - x) * x / 0) 0 0 := by
  simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-- `R₀ = 2` with `F`, `V` built literally from the derivatives (`β = 2`, `γ = 1`, `N = 3`). -/
example : MathlibExt.Biology.Epidemiology.NextGenerationMatrix.R0
    !![deriv (fun x : ℝ => 2 * 3 * x / 3) 0] !![deriv (fun x : ℝ => 1 * x) 0] = 2 := by
  rw [R0_deriv_eq (by norm_num) one_pos (by norm_num)]; norm_num

end MathlibExtTest.Biology.Epidemiology.SIS
