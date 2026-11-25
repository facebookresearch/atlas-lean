/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Epidemiology.SISVaccination

/-!
# Tests for the SIS model with leaky vaccination

* `R_v` and the critical coverage `p_c` computed from their definitions, including the boundary
  `p = p_c` (`R_v = 1`) and the perfect-vaccine value `p_c = 1 - 1 / R₀`;
* without transmission (`β = 0`), `R_v = 0`, the threshold equivalence fails, and extinction
  still holds;
* the concrete endemic equilibrium `(I_u*, I_v*) = (1/3, 1/6)` of `β = 4`, `γ = 1`, `ε = 3/4`,
  `N = 1`, `p = 1/2` (`R_v = 5/2`, `p_c = 1`), checked from the equilibrium equations;
* the Lyapunov function and its derivative expression computed from their definitions;
* non-vacuity of the solution hypotheses: constant solutions, and a non-constant solution for a
  perfect vaccine (`ε = 1`) built from the explicit SIS solution `SIS.isSolution_sis`;
* the reduction to SIS for `ε = 0`;
* below threshold there is no endemic equilibrium.
-/

open Real Filter Set Matrix
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SISVaccination

open MathlibExt.Biology.Epidemiology
open MathlibExt.Biology.Epidemiology.SISVaccination

/-! ### `R_v` and the critical coverage, from the definitions -/

example : Rv 4 1 (3 / 4) (1 / 2) = 5 / 2 := by norm_num [Rv]

example : criticalCoverage 4 1 (3 / 4) = 1 := by norm_num [criticalCoverage]

/-- At the critical coverage the vaccinated reproduction number is exactly `1`. -/
example : Rv 4 1 (3 / 4) (criticalCoverage 4 1 (3 / 4)) = 1 := by
  norm_num [Rv, criticalCoverage]

/-- `β = 3/2`, `γ = 1`, `ε = 1/2`: `p_c = 2/3`, computed directly. -/
example : criticalCoverage (3 / 2) 1 (1 / 2) = 2 / 3 := by norm_num [criticalCoverage]

example : Rv (3 / 2) 1 (1 / 2) (2 / 3) = 1 := by norm_num [Rv]

example : Rv (3 / 2) 1 (1 / 2) (3 / 4) = 15 / 16 := by norm_num [Rv]

/-- The threshold lemma agrees with the direct computation on both sides of `p_c = 2/3`. -/
example : Rv (3 / 2) 1 (1 / 2) (3 / 4) < 1 :=
  (Rv_lt_one_iff (by norm_num) one_pos (by norm_num)).2 (by norm_num [criticalCoverage])

example : 1 < Rv (3 / 2) 1 (1 / 2) (1 / 2) :=
  (one_lt_Rv_iff (by norm_num) one_pos (by norm_num)).2 (by norm_num [criticalCoverage])

example : Rv (3 / 2) 1 (1 / 2) (1 / 2) = 9 / 8 := by norm_num [Rv]

/-- A perfect vaccine (`ε = 1`): `p_c = 1 - 1 / R₀`, here `1/2` for `R₀ = 2`. -/
example : criticalCoverage 2 1 1 = 1 / 2 := by norm_num [criticalCoverage]

/-- Herd immunity needs efficacy `≥ 1 - 1 / R₀`: with `R₀ = 4`, `ε = 3/4` is the boundary. -/
example : criticalCoverage 4 1 (3 / 4) ≤ 1 :=
  (criticalCoverage_le_one_iff (by norm_num)).2 (by norm_num)

example : ¬ criticalCoverage 4 1 (1 / 2) ≤ 1 := by norm_num [criticalCoverage]

/-- `R₀ ≤ 1` needs no vaccination. -/
example : criticalCoverage (1 / 2) 1 (1 / 2) = -2 := by norm_num [criticalCoverage]

/-- Without transmission `R_v = 0` at every coverage. -/
example : Rv 0 1 (1 / 2) (3 / 4) = 0 := Rv_zero_transmission 1 (1 / 2) (3 / 4)

/-- The threshold equivalence needs `β > 0`: for `β = 0`, `γ = ε = 1` and `p = 0`, `R_v = 0 < 1`
while `p_c = 1 > p` (Lean's convention `γ / 0 = 0`). -/
example : Rv 0 1 1 0 < 1 ∧ ¬ criticalCoverage 0 1 1 < 0 := by
  norm_num [Rv, criticalCoverage]

/-- Without vaccination `R_v` is the SIS next-generation `R₀`. -/
example : Rv 4 1 (3 / 4) 0 = NextGenerationMatrix.R0 !![4] !![1] :=
  Rv_zero_coverage_eq_R0 (by norm_num) one_pos

/-! ### A concrete endemic equilibrium -/

/-- `(1/3, 1/6)` is an endemic equilibrium of `β = 4`, `γ = 1`, `ε = 3/4`, `N = 1`, `p = 1/2`:
both infected equations vanish, computed directly. -/
theorem endemicEq_example : IsEndemicEq 4 1 (3 / 4) 1 (1 / 2) (1 / 3) (1 / 6) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The perturbed point `(1/3, 1/5)` is not an equilibrium. -/
example : ¬ IsEndemicEq 4 1 (3 / 4) 1 (1 / 2) (1 / 3) (1 / 5) := fun h => by
  have := h.eq_vaccinated
  norm_num at this

/-- Consistency with the threshold: the equilibrium forces `R_v > 1`, and `R_v = 5/2`. -/
example : 1 < Rv 4 1 (3 / 4) (1 / 2) :=
  one_lt_Rv_of_isEndemicEq endemicEq_example (by norm_num) one_pos (by norm_num) one_pos

/-- Existence above threshold, with hypotheses discharged by the concrete parameters. -/
example : ∃ a c, IsEndemicEq 4 1 (3 / 4) 1 (1 / 2) a c :=
  exists_isEndemicEq (by norm_num) one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Rv])

/-- Uniqueness: any endemic equilibrium of these parameters is `(1/3, 1/6)`. -/
example {a c : ℝ} (h : IsEndemicEq 4 1 (3 / 4) 1 (1 / 2) a c) : a = 1 / 3 ∧ c = 1 / 6 :=
  h.unique endemicEq_example (by norm_num) one_pos (by norm_num) one_pos

/-- Below threshold (`R_v = 15/16`) there is no endemic equilibrium. -/
example {a c : ℝ} : ¬ IsEndemicEq (3 / 2) 1 (1 / 2) 1 (3 / 4) a c := fun h => by
  have := one_lt_Rv_of_isEndemicEq h (by norm_num) one_pos (by norm_num) one_pos
  norm_num [Rv] at this

/-! ### The Lyapunov function, from the definitions -/

example : lyapunov (1 / 3) (1 / 6) (1 / 3) (1 / 6) = 0 := by
  simp [lyapunov, SEIRVital.volterra]

example : lyapunovDeriv 4 1 (3 / 4) 1 (1 / 3) (1 / 6) (1 / 3) (1 / 6) = 0 := by
  norm_num [lyapunovDeriv]

/-- Off equilibrium, at `(1/2, 1/2)`: `-(4·1·(1/6)²)/(1/2) - (1·1·(1/3)²)/(1/2)
- (1/2 · 1/6 - 1/2 · 1/3)² / (1/2 · 1/4) = -2/9 - 2/9 - 1/18 = -1/2`. -/
example : lyapunovDeriv 4 1 (3 / 4) 1 (1 / 3) (1 / 6) (1 / 2) (1 / 2) = -1 / 2 := by
  norm_num [lyapunovDeriv]

/-- The derivative identity at `(1/2, 1/2)`, with the vector field evaluated directly. -/
example : (1 - (1 / 3) / (1 / 2)) * (4 * ((1 - 1 / 2) * 1 - 1 / 2) * (1 / 2 + 1 / 2) / 1 -
      1 * (1 / 2)) + (1 - (1 / 6) / (1 / 2)) *
      ((1 - 3 / 4) * 4 * (1 / 2 * 1 - 1 / 2) * (1 / 2 + 1 / 2) / 1 - 1 * (1 / 2)) =
    lyapunovDeriv 4 1 (3 / 4) 1 (1 / 3) (1 / 6) (1 / 2) (1 / 2) := by
  norm_num [lyapunovDeriv]

/-! ### Constant solutions and the main theorems applied to them -/

theorem const_endemic :
    IsSolution 4 1 (3 / 4) 1 (fun _ => (1 - 1 / 2) * 1 - 1 / 3) (fun _ => 1 / 3)
      (fun _ => 1 / 2 * 1 - 1 / 6) (fun _ => 1 / 6) :=
  isSolution_const_endemic endemicEq_example

/-- The endemic attractivity theorem's hypotheses hold for the constant endemic solution. -/
example : Tendsto (fun _ : ℝ => (1 : ℝ) / 3) atTop (𝓝 (1 / 3)) :=
  (const_endemic.tendsto_endemic endemicEq_example (by norm_num) one_pos (by norm_num) one_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2.1

/-- The disease-free equilibrium is a solution satisfying the extinction hypotheses. -/
example : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) :=
  ((isSolution_const_dfe (3 / 2) 1 (1 / 2) 1 (3 / 4)).tendsto_dfe (p := 3 / 4) (by norm_num) one_pos
    (by norm_num) (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) le_rfl (Or.inl (by norm_num [Rv]))).2.1

/-- Without transmission the extinction theorem applies at every coverage. -/
example : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) :=
  ((isSolution_const_dfe 0 1 (1 / 2) 1 (1 / 4)).tendsto_dfe (p := 1 / 4) le_rfl one_pos
    (by norm_num) (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) le_rfl (Or.inl (by simp))).2.1

/-! ### A non-constant solution: a perfect vaccine

With `ε = 1` the vaccinated group stays susceptible (`S_v ≡ p N`, `I_v ≡ 0`) and the
unvaccinated group is an SIS epidemic with transmission `β (1 - p)` in a population `(1 - p) N`.
For `β = 2`, `γ = 1`, `N = 1`, `p = 3/4`: `R_v = 1/2`. -/

/-- The explicit solution, from `SIS.isSolution_sis`, solves the vaccination model. -/
theorem perfect_vaccine_solution :
    IsSolution 2 1 1 1 (SIS.sisSusceptible (1 / 2) 1 (1 / 4) (1 / 8))
      (SIS.sisInfected (1 / 2) 1 (1 / 4) (1 / 8)) (fun _ => 3 / 4) (fun _ => 0) := by
  have hs := SIS.isSolution_sis (β := 1 / 2) (γ := 1) (N := 1 / 4) (I₀ := 1 / 8) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t _ => ?_, fun t _ => ?_⟩
  · convert hs.hasDerivAt_susceptible t ht using 1
    ring
  · convert hs.hasDerivAt_infected t ht using 1
    ring
  · convert hasDerivAt_const t (3 / 4 : ℝ) using 1
    ring
  · convert hasDerivAt_const t (0 : ℝ) using 1
    ring

example : Rv 2 1 1 (3 / 4) = 1 / 2 := by norm_num [Rv]

/-- The extinction theorem applies to the non-constant solution: `I_u → 0`. -/
example : Tendsto (SIS.sisInfected (1 / 2) 1 (1 / 4) (1 / 8)) atTop (𝓝 0) :=
  (perfect_vaccine_solution.tendsto_dfe (p := 3 / 4) (by norm_num) one_pos (by norm_num) le_rfl
    one_pos (by norm_num [SIS.sisSusceptible]) (by norm_num)
    (by norm_num [SIS.sisSusceptible]) (by norm_num) (by norm_num) le_rfl
    (Or.inl (by norm_num [Rv]))).2.1

/-- The exponential bound `I(t) ≤ I(0) e^{-γ (1 - R_v) t}` at `t = 2`. -/
example : SIS.sisInfected (1 / 2) 1 (1 / 4) (1 / 8) 2 + 0 ≤
    (1 / 8 + 0) * exp (-(1 * (1 - Rv 2 1 1 (3 / 4))) * 2) := by
  have := perfect_vaccine_solution.totalInfected_le_exp (p := 3 / 4) (by norm_num) one_pos
    (by norm_num) le_rfl one_pos (by norm_num [SIS.sisSusceptible]) (by norm_num)
    (by norm_num [SIS.sisSusceptible]) (by norm_num) (by norm_num) le_rfl (t := 2)
    (by norm_num)
  simpa using this

/-! ### Zero efficacy reduces to SIS -/

/-- With `ε = 0`, the SIS endemic state `(S, I) = (1/2, 1/2)` of `β = 2`, `γ = 1`, `N = 1`, split
evenly between the groups, is a solution. -/
theorem zero_efficacy_const :
    IsSolution 2 1 0 1 (fun _ => 1 / 4) (fun _ => 1 / 4) (fun _ => 1 / 4) (fun _ => 1 / 4) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun t _ => ?_⟩ <;>
    convert hasDerivAt_const t ((1 : ℝ) / 4) using 1 <;> norm_num

/-- Its totals solve SIS. -/
example : SIS.IsSolution 2 1 1 (fun _ => (1 : ℝ) / 4 + 1 / 4) (fun _ => (1 : ℝ) / 4 + 1 / 4) :=
  zero_efficacy_const.toSIS

/-- The SIS endemic limit `N (1 - γ / β) = 1/2` applies to the total infected. -/
example : Tendsto (fun _ : ℝ => (1 : ℝ) / 4 + 1 / 4) atTop (𝓝 (1 * (1 - 1 / 2))) :=
  zero_efficacy_const.tendsto_totalInfected_endemic_of_efficacy_zero (by norm_num) (by norm_num)
    one_pos (by norm_num) (by norm_num)

end MathlibExtTest.Biology.Epidemiology.SISVaccination
