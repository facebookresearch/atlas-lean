/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SISGlobalStability

/-!
# Tests for the Lyapunov global stability of the SIS endemic equilibrium

Concrete model `β = 2`, `γ = 1`, `N = 1` (`R₀ = 2`), endemic equilibrium `(1/2, 1/2)`:

* values of `lyapunov` computed from its definition: `0` at the equilibrium and `log (4/3) / 2`
  at `(1/4, 3/4)`;
* values of the derivative expression `-β (S - S*)² / S` computed directly;
* non-vacuity of every hypothesis of the main theorems, discharged by the explicit solution
  of `SIS.lean` (`isSolution_sis`) and by the constant endemic solution;
* the attractivity limit agrees with the independent explicit-solution limit
  `tendsto_sisInfected_endemic`;
* the boundary `R₀ = 1` (`β = γ`), where `I* = 0` leaves the open orthant (so the Lyapunov
  function, which needs `log (I / I*)`, is undefined), and `R₀ < 1`, where `I* < 0` while
  `I → 0`, so convergence to `(S*, I*)` fails.
-/

open Real Filter Set
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SISGlobalStability

open MathlibExt.Biology.Epidemiology.SIS

/-! ### `lyapunov` from its definition -/

/-- `V` vanishes at the endemic equilibrium `(1/2, 1/2)` of `β = 2`, `γ = 1`, `N = 1`. -/
example : lyapunov 2 1 1 (1 / 2) (1 / 2) = 0 := by
  norm_num [lyapunov]

/-- Away from the equilibrium, `V(1/4, 3/4) = log (4/3) / 2`, computed from the definition. -/
example : lyapunov 2 1 1 (1 / 4) (3 / 4) = log (4 / 3) / 2 := by
  have h1 : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  have h2 : log (3 / 2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have h3 : log (4 / 3 : ℝ) = 2 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast; ring
  norm_num [lyapunov]
  rw [h1, h2, h3]
  ring

/-- That value is strictly positive (`4/3 > 1`), matching `lyapunov_nonneg` with strictness off
the equilibrium. -/
example : 0 < log (4 / 3 : ℝ) / 2 := by
  have : 0 < log (4 / 3 : ℝ) := log_pos (by norm_num)
  positivity

example : 0 ≤ lyapunov 2 1 1 (1 / 4) (3 / 4) :=
  lyapunov_nonneg one_pos one_lt_two one_pos (by norm_num) (by norm_num)

example : lyapunov 2 1 1 (1 / 4) (3 / 4) ≠ 0 := fun h =>
  absurd ((lyapunov_eq_zero_iff one_pos one_lt_two one_pos (by norm_num) (by norm_num)).1 h).1
    (by norm_num)

example : lyapunov 2 1 1 (1 / 2) (1 / 2) = 0 :=
  (lyapunov_eq_zero_iff one_pos one_lt_two one_pos (by norm_num) (by norm_num)).2
    ⟨by norm_num, by norm_num⟩

/-! ### The derivative expression -/

/-- At the equilibrium the Lyapunov derivative is `0`. -/
example : -((2 : ℝ) * (1 / 2 - 1 * 1 / 2) ^ 2 / (1 / 2)) = 0 := by norm_num

/-- At `S = 1/4` it is `-1/2 < 0`. -/
example : -((2 : ℝ) * (1 / 4 - 1 * 1 / 2) ^ 2 / (1 / 4)) = -1 / 2 := by norm_num

example : ¬ (-((2 : ℝ) * (1 / 4 - 1 * 1 / 2) ^ 2 / (1 / 4)) = 0) := fun h =>
  absurd ((lyapunovDeriv_eq_zero_iff (I := 3 / 4) two_pos (by norm_num) (by norm_num)).1 h).1
    (by norm_num)

/-! ### Non-vacuity: the explicit solution with `I₀ = 1/100` -/

/-- The explicit solution of `SIS.lean`, an independent witness for `IsSolution`. -/
theorem explicit_isSolution :
    IsSolution 2 1 1 (sisSusceptible 2 1 1 (1 / 100)) (sisInfected 2 1 1 (1 / 100)) :=
  isSolution_sis (by norm_num) one_pos (by norm_num)

theorem explicit_total :
    sisSusceptible 2 1 1 (1 / 100) 0 + sisInfected 2 1 1 (1 / 100) 0 = 1 := by
  simp [sisSusceptible]

theorem explicit_S0 : 0 < sisSusceptible 2 1 1 (1 / 100) 0 := by
  simp [sisSusceptible]; norm_num

theorem explicit_I0 : 0 < sisInfected 2 1 1 (1 / 100) 0 := by simp

/-- The Lyapunov derivative formula applies to the explicit solution at `t = 0`. -/
example : HasDerivAt
    (fun s => lyapunov 2 1 1 (sisSusceptible 2 1 1 (1 / 100) s) (sisInfected 2 1 1 (1 / 100) s))
    (-(2 * (sisSusceptible 2 1 1 (1 / 100) 0 - 1 * 1 / 2) ^ 2 /
      sisSusceptible 2 1 1 (1 / 100) 0)) 0 :=
  explicit_isSolution.hasDerivAt_lyapunov one_pos one_lt_two one_pos explicit_total le_rfl
    explicit_S0 explicit_I0

/-- Forward invariance on the explicit solution at `t = 5`. -/
example : 0 < sisSusceptible 2 1 1 (1 / 100) 5 ∧ 0 < sisInfected 2 1 1 (1 / 100) 5 :=
  explicit_isSolution.pos_of_pos (by norm_num) (by norm_num) one_pos explicit_total explicit_S0
    explicit_I0 (by norm_num)

/-- Exponential decay of `V` along the explicit solution. -/
example : ∃ c > 0, ∀ t, 0 ≤ t →
    lyapunov 2 1 1 (sisSusceptible 2 1 1 (1 / 100) t) (sisInfected 2 1 1 (1 / 100) t) ≤
      lyapunov 2 1 1 (sisSusceptible 2 1 1 (1 / 100) 0) (sisInfected 2 1 1 (1 / 100) 0) *
        exp (-(c * t)) :=
  explicit_isSolution.exists_lyapunov_le_exp one_pos one_lt_two one_pos explicit_total
    explicit_S0 explicit_I0

/-- Global attractivity applied to the explicit solution: limit `(1/2, 1/2)`. -/
example : Tendsto (fun t => (sisSusceptible 2 1 1 (1 / 100) t, sisInfected 2 1 1 (1 / 100) t))
    atTop (𝓝 ((1 : ℝ) / 2, (1 : ℝ) / 2)) := by
  have := explicit_isSolution.tendsto_endemic_of_lyapunov one_pos one_lt_two one_pos
    explicit_total explicit_S0 explicit_I0
  norm_num at this ⊢
  exact this

/-- Consistency: the Lyapunov limit of `I` agrees with the explicit-solution limit of `SIS.lean`
(`tendsto_sisInfected_endemic`), proved without the Lyapunov function. -/
example : Tendsto (sisInfected 2 1 1 (1 / 100)) atTop (𝓝 ((1 : ℝ) * (1 - 1 / 2))) :=
  tendsto_sisInfected_endemic (by norm_num) one_lt_two one_ne_zero (by norm_num)

/-! ### Non-vacuity: the constant endemic solution -/

/-- `V` is identically `0` along the constant endemic solution, from the definition. -/
example (t : ℝ) :
    lyapunov 2 1 1 ((fun _ => (1 : ℝ) * 1 / 2) t) ((fun _ => (1 : ℝ) * (1 - 1 / 2)) t) = 0 := by
  norm_num [lyapunov]

/-- Lyapunov stability instantiated at `ε = 1/10` for `β = 2`, `γ = 1`, `N = 1`. -/
example : ∃ δ > 0, ∀ S I : ℝ → ℝ, IsSolution 2 1 1 S I → S 0 + I 0 = 1 → 0 < S 0 → 0 < I 0 →
    dist (S 0, I 0) ((1 : ℝ) * 1 / 2, (1 : ℝ) * (1 - 1 / 2)) < δ →
    ∀ t, 0 ≤ t → dist (S t, I t) ((1 : ℝ) * 1 / 2, (1 : ℝ) * (1 - 1 / 2)) < 1 / 10 :=
  endemic_lyapunovStable one_pos (by norm_num) one_pos _ (by norm_num)

/-- The `δ` from Lyapunov stability, applied to the constant endemic solution: its hypotheses
are all satisfied and it stays within `1/10` of the equilibrium at `t = 3`. -/
example : dist ((fun _ => (1 : ℝ) * 1 / 2) 3, (fun _ => (1 : ℝ) * (1 - 1 / 2)) 3)
    ((1 : ℝ) * 1 / 2, (1 : ℝ) * (1 - 1 / 2)) < 1 / 10 := by
  obtain ⟨δ, hδ, hstab⟩ := endemic_lyapunovStable (β := 2) (γ := 1) (N := 1) one_pos
    (by norm_num) one_pos (1 / 10) (by norm_num)
  exact hstab _ _ (isSolution_const_endemic two_ne_zero) (by norm_num) (by norm_num)
    (by norm_num) (by simpa using hδ) 3 (by norm_num)

example : IsSolution 2 1 1 (fun _ => 1 * 1 / 2) (fun _ => 1 * (1 - 1 / 2)) :=
  isSolution_const_endemic two_ne_zero

/-- The combined global asymptotic stability statement is inhabited for `R₀ = 2`. -/
example := endemic_globallyAsymptoticallyStable (β := 2) (γ := 1) (N := 1) one_pos (by norm_num)
  one_pos

/-! ### Boundaries `R₀ = 1` and `R₀ < 1` -/

/-- At `β = γ` (`R₀ = 1`) the "endemic" level `I* = N (1 - γ / β)` is `0`: the equilibrium
`(N, 0)` leaves the open orthant and `log (I / I*)` in `lyapunov` is meaningless. Strictness of
`1 < β / γ` is needed by this Lyapunov proof, not by the convergence statement, which still
holds at `R₀ = 1` (`IsSolution.tendsto_infected_zero`). -/
example : (1 : ℝ) * (1 - 1 / 1) = 0 := by norm_num

example : ¬ ((1 : ℝ) < 1 / 1) := by norm_num

/-- For `R₀ = 1/2 < 1` (`β = 1`, `γ = 2`, `N = 1`) the formula gives `I* = 1 · (1 - 2/1) = -1`. -/
example : (1 : ℝ) * (1 - 2 / 1) = -1 := by norm_num

/-- ...while every positive solution has `I → 0 ≠ -1`, so for `R₀ < 1` convergence to the
formula point fails and the hypothesis `1 < β / γ` cannot be dropped. -/
example : Tendsto (sisInfected 1 2 1 (1 / 100)) atTop (𝓝 0) :=
  tendsto_sisInfected_zero (by norm_num) (by norm_num) (by norm_num) one_pos (by norm_num)

end MathlibExtTest.Biology.Epidemiology.SISGlobalStability
