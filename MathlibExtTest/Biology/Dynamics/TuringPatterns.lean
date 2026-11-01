/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringPatterns

/-! Tests for Turing patterns: concrete mode matrices, a growing Fourier mode as a non-vacuity
witness for the linearized system, the Schnakenberg kinetics on both sides of the Turing
threshold, a small Neumann domain without pattern, and junk values outside the domains. -/

open Matrix Filter

namespace MathlibExtTest.Biology.Dynamics.TuringPatterns

open MathlibExt.Biology.Dynamics.TuringPatterns

/-- The Schnakenberg Jacobian at `a = 1 / 10`, `b = 9 / 10`: `[[4 / 5, 1], [-9 / 5, -1]]`. -/
example : schnakenbergJacobian (1 / 10) (9 / 10) = !![4 / 5, 1; -9 / 5, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [schnakenbergJacobian]

example : (schnakenbergJacobian (1 / 10) (9 / 10)).det = 1 := by
  rw [det_schnakenbergJacobian (by norm_num)]
  norm_num

/-- `h(q) = 9 q² - 31 q / 5 + 1` for this Jacobian with `d_u = 1`, `d_v = 9`. -/
example (q : ℝ) :
    dispersionDet (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 q = 9 * q ^ 2 - 31 / 5 * q + 1 := by
  rw [dispersionDet, det_schnakenbergJacobian (by norm_num)]
  norm_num [schnakenbergJacobian]

example : criticalWavenumberSq (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 = 31 / 90 := by
  norm_num [criticalWavenumberSq, schnakenbergJacobian]

/-- The homogeneous mode `k = 0` has mode matrix `J`. -/
example (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ) : modeMatrix J du dv 0 = J := by
  simp [modeMatrix]

example : neumannWavenumber 1 2 = 2 * Real.pi := by
  norm_num [neumannWavenumber]

/-- Zero-length edge case: at `L = 0` the totalized division collapses every
labeled Neumann mode to the homogeneous mode. -/
example (n : ℕ) : neumannWavenumber 0 n = 0 := by
  simp [neumannWavenumber]

/-- **Non-vacuity witness for the linearized system.** With `J = diag(2, -1)`, `d_u = d_v = 1`
and `k = 1`, the mode matrix is `diag(1, -2)`; the Fourier mode with `μ = 1`, `v = (1, 0)` solves
`w_t = D w_xx + J w` and grows, so mode `1` is unstable. -/
example : IsLinearizedSolution !![2, 0; 0, -1] 1 1 (fourierMode 1 1 ![1, 0]) ∧
    Tendsto (fun t => ‖fourierMode 1 1 ![1, 0] t 0‖) atTop atTop ∧
    IsUnstableMode !![2, 0; 0, -1] 1 1 1 := by
  have hv : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    simpa using congrFun h 0
  have heig : (modeMatrix !![2, 0; 0, -1] 1 1 1).map ((↑) : ℝ → ℂ) *ᵥ (![1, 0] : Fin 2 → ℂ) =
      (1 : ℂ) • (![1, 0] : Fin 2 → ℂ) := by
    ext i
    fin_cases i <;> norm_num [modeMatrix, diffusionMatrix, Matrix.mulVec, dotProduct]
  have hgrow := (tendsto_norm_fourierMode_iff hv 1 1).2 (by norm_num)
  exact ⟨(fourierMode_isLinearizedSolution_iff _ _ _ _ _ _).2 heig, hgrow,
    isUnstableMode_iff_exists_growing.2
      ⟨1, ![1, 0], hv, (fourierMode_isLinearizedSolution_iff _ _ _ _ _ _).2 heig, hgrow⟩⟩

/-- A stable homogeneous state (`tr J = -1/5 < 0`, `det J = 1 > 0`) for Schnakenberg at
`a = 1 / 10`, `b = 9 / 10`. -/
example : ¬ IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 0 := by
  apply not_isUnstableMode_zero
  · rw [(trace_schnakenbergJacobian_neg_iff (by norm_num))]
    norm_num
  · rw [det_schnakenbergJacobian (by norm_num)]
    norm_num

/-- **Turing instability witness.** Schnakenberg at `a = 1 / 10`, `b = 9 / 10` with
`d_v / d_u = 9`: `2 √9 · 1 = 6 < 9 · 4/5 - 1 = 31/5`, so some mode is unstable. -/
example : ∃ k, IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 k := by
  rw [schnakenberg_turing_iff (by norm_num) (by norm_num) (by norm_num),
    show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Concretely, mode `k = 1 / √3` (`k² = 1 / 3`, `h(1/3) = -1/15`) is unstable. -/
example : IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 (Real.sqrt (1 / 3)) := by
  rw [isUnstableMode_iff_dispersionDet_neg
      ((trace_schnakenbergJacobian_neg_iff (by norm_num)).2 (by norm_num)) zero_le_one
      (by norm_num), Real.sq_sqrt (by norm_num), dispersionDet,
    det_schnakenbergJacobian (by norm_num)]
  norm_num [schnakenbergJacobian]

/-- **Equal diffusion gives no pattern.** With `d_u = d_v = 1` the same kinetics have no unstable
mode (`2 > 4/5 - 1`), as `lt_of_exists_isUnstableMode` predicts for an activator. -/
example : ¬ ∃ k, IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 1 k := by
  rw [schnakenberg_turing_iff (by norm_num) (by norm_num) one_pos, Real.sqrt_one]
  norm_num

/-- The same conclusion from the general theorem: the activator `u` (`f_u = 4/5 > 0`) would need
`d_u < d_v`. -/
example : ¬ ∃ k, IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 2 2 k := fun h =>
  lt_irrefl _ <| lt_of_exists_isUnstableMode
    ((trace_schnakenbergJacobian_neg_iff (by norm_num)).2 (by norm_num))
    (by rw [det_schnakenbergJacobian (by norm_num)]; norm_num) (by norm_num) (by norm_num)
    (by norm_num [schnakenbergJacobian]) h

/-- **Gierer–Meinhardt witness.** At `a = 0`, `b = 1 / 2` the state is stable without diffusion
(`1/2 < 1`), and with `d = 50`: `2 √25 = 10 < 50 · 1/2 - 1 = 24`, so some mode is unstable. -/
example : ∃ k, IsUnstableMode (giererMeinhardtJacobian 0 (1 / 2)) 1 50 k := by
  rw [giererMeinhardt_turing_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    show (50 : ℝ) * (1 / 2) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- With equal diffusion the Gierer–Meinhardt state at `a = 0`, `b = 1 / 2` has no unstable
mode. -/
example : ¬ ∃ k, IsUnstableMode (giererMeinhardtJacobian 0 (1 / 2)) 1 1 k := by
  rw [giererMeinhardt_turing_iff (by norm_num) (by norm_num) (by norm_num) one_pos]
  intro h
  have := Real.sqrt_nonneg (1 * (1 / 2 : ℝ))
  linarith

example : (giererMeinhardtJacobian 0 (1 / 2)).det = 1 / 2 :=
  det_giererMeinhardtJacobian (by norm_num) (by norm_num)

/-- The Gierer–Meinhardt steady state at `a = 0`, `b = 1 / 2` is `(2, 4)`. -/
example : giererMeinhardtSteadyState 0 (1 / 2) = ![2, 4] := by
  ext i
  fin_cases i <;> norm_num [giererMeinhardtSteadyState]

/-- Junk value outside the domain: at `v = 0` the term `u² / v` is `0`. -/
example (a b u : ℝ) : giererMeinhardt a b ![u, 0] 0 = a - b * u := by
  simp [giererMeinhardt]

/-- **Small domain.** On `[0, 1]` the unstable band of the Turing-unstable example ends below
`π²`, so no Neumann mode is unstable. -/
example (n : ℕ) :
    ¬ IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 (neumannWavenumber 1 n) := by
  have htr : (schnakenbergJacobian (1 / 10) (9 / 10)).trace < 0 :=
    (trace_schnakenbergJacobian_neg_iff (by norm_num)).2 (by norm_num)
  have hdet : 0 < (schnakenbergJacobian (1 / 10) (9 / 10)).det := by
    rw [det_schnakenbergJacobian (by norm_num)]; norm_num
  refine not_isUnstableMode_neumannWavenumber_of_le one_pos (by norm_num) htr hdet one_pos ?_ n
  have hΔ : bandDiscriminant (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 ≤ 4 := by
    rw [bandDiscriminant, det_schnakenbergJacobian (by norm_num)]
    norm_num [schnakenbergJacobian]
  have hs : Real.sqrt (bandDiscriminant (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hΔ
  have hpi : (2 : ℝ) ^ 2 ≤ (Real.pi / 1) ^ 2 := by
    rw [div_one]
    exact pow_le_pow_left₀ (by norm_num) Real.two_le_pi 2
  unfold bandUpper
  norm_num [schnakenbergJacobian] at hs ⊢
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- Junk value outside the domain: at `a + b = 0` the steady-state formula divides by zero and
returns `v₀ = 0`. -/
example : schnakenbergSteadyState 1 (-1) = ![0, 0] := by
  ext i
  fin_cases i <;> simp [schnakenbergSteadyState]

/-- Junk value outside the domain: `k_c² = 0` when `d_u = 0`, since division by zero gives `0`. -/
example (J : Matrix (Fin 2) (Fin 2) ℝ) (dv : ℝ) : criticalWavenumberSq J 0 dv = 0 := by
  simp [criticalWavenumberSq]

#print axioms schnakenberg_turing_iff
#print axioms exists_isUnstableMode_iff
#print axioms isUnstableMode_iff_exists_growing

end MathlibExtTest.Biology.Dynamics.TuringPatterns
