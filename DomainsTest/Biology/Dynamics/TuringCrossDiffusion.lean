/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.TuringCrossDiffusion

/-! Tests for Turing instability with cross-diffusion.

* Values: the Keller–Segel coefficient `b`, the mode matrix at `k = 0`, the diagonal bridge, the
  flux linearization and the steady state, all evaluated from the definitions.
* Non-vacuity: for Keller–Segel with `r = α = β = d_u = d_v = 1` and `χ = 9`, the mode matrix at
  `k = 1` is `[[-2, 9], [1, -2]]` with eigenvalue `1` and eigenvector `(3, 1)`, checked by direct
  matrix arithmetic. The Fourier mode solves the linearized cross-diffusion system and grows,
  while the same kinetics with the diagonal diffusion `diag(1, 1)` are stable at `k = 1`.
* Boundary: at the threshold `χ = 4` the dispersion polynomial is `(q - 1)²`, so no mode is
  unstable and `k = 1` is marginal; the theorem's strict inequality `2 < 2` agrees.
* Minimal Keller–Segel (`r = 0`, `α = β = d_u = d_v = u₀ = 1`, `χ = 4`): mode `1` is unstable,
  mode `2` is stable, `k = √3` is marginal (`det = 0`), and no Neumann mode on `[0, π / 2]` is
  unstable, all computed from the mode matrix.
* Junk values: the band ends divide by `2 det D`, so they are `0` at `det D = 0`.
-/

open Matrix Filter

namespace MathlibExtTest.Biology.Dynamics.TuringCrossDiffusion

open MathlibExt.Biology.Dynamics.TuringPatterns
open MathlibExt.Biology.Dynamics.TuringCrossDiffusion

/-! ### Values from the definitions -/

/-- The Keller–Segel coefficient `b = α χ u₀ - r d_v - β d_u` at
`r = 1, α = 2, β = 3, d_u = 5, d_v = 7, χ = 11, u₀ = 13`: `286 - 7 - 15 = 264`. -/
example : crossCoeff (kellerSegelJacobian 1 2 3) (kellerSegelDiffusion 5 7 11 13) = 264 := by
  norm_num [crossCoeff, kellerSegelJacobian, kellerSegelDiffusion]

/-- The homogeneous mode `k = 0` has mode matrix `J`. -/
example (J D : Matrix (Fin 2) (Fin 2) ℝ) : crossModeMatrix J D 0 = J := by
  simp [crossModeMatrix]

/-- The mode matrix of the running example at `k = 1`. -/
example : crossModeMatrix (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 9 1) 1 =
    !![-2, 9; 1, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [crossModeMatrix, kellerSegelJacobian, kellerSegelDiffusion]

/-- The diagonal bridge on numbers: with `D = diag(2, 3)` and `J = [[1, 4], [5, 6]]`, both
dispersion polynomials evaluate to `6 q² - 15 q - 14` at `q = 1`, i.e. `-23`. -/
example : crossDispersionDet !![1, 4; 5, 6] (diffusionMatrix 2 3) 1 = -23 ∧
    dispersionDet !![1, 4; 5, 6] 2 3 1 = -23 := by
  constructor
  · norm_num [crossDispersionDet, crossCoeff, diffusionMatrix, Matrix.det_fin_two]
  · norm_num [dispersionDet, Matrix.det_fin_two]

/-- Without chemotaxis the Keller–Segel diffusion matrix has no cross term. -/
example (du dv u₀ : ℝ) : kellerSegelDiffusion du dv 0 u₀ 0 1 = 0 := by
  simp [kellerSegelDiffusion]

/-- The flux at state `(2, 0)` with gradient `(1, 1)`, `d_u = d_v = 1`, `χ = 3`: `(1 - 6, 1)`,
which is `D(u₀ = 2) g` exactly (no perturbation). -/
example : kellerSegelFlux 1 1 3 ![2, 0] ![1, 1] = ![-5, 1] ∧
    kellerSegelDiffusion 1 1 3 2 *ᵥ ![1, 1] = ![-5, 1] := by
  constructor
  · ext i
    fin_cases i <;> norm_num [kellerSegelFlux]
  · ext i
    fin_cases i <;> norm_num [kellerSegelDiffusion, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `(1, 2 / 4)` is a steady state of `f = u (1 - u)`, `g = 2 u - 4 v`. -/
example : kellerSegelKinetics 1 2 4 ![1, 1 / 2] = 0 := by
  ext i
  fin_cases i <;> norm_num [kellerSegelKinetics]

example : MetaMathlibExt.jacobianMatrix (kellerSegelKinetics 1 2 4)
    (kellerSegelSteadyState 2 4) = !![-1, 0; 2, -4] :=
  jacobianMatrix_kellerSegel 1 2 4

/-! ### Non-vacuity: a growing chemotactic mode -/

/-- The eigen-equation `[[-2, 9], [1, -2]] (3, 1) = 1 · (3, 1)` of the running example. -/
theorem example_eigen :
    (crossModeMatrix (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 9 1) 1).map
        ((↑) : ℝ → ℂ) *ᵥ (![3, 1] : Fin 2 → ℂ) = (1 : ℂ) • (![3, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;>
    norm_num [crossModeMatrix, kellerSegelJacobian, kellerSegelDiffusion, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

theorem example_ne : (![3, 1] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  simpa using congrFun h 1

/-- **Non-vacuity witness.** The Fourier mode `e^t cos(x) (3, 1)` solves the linearized
Keller–Segel system with `χ = 9` and grows, and mode `1` is unstable (witness `μ = 1` checked
directly against the definition). -/
example : IsCrossLinearizedSolution (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 9 1)
      (fourierMode 1 1 ![3, 1]) ∧
    Tendsto (fun t => ‖fourierMode 1 1 ![3, 1] t 0‖) atTop atTop ∧
    IsCrossUnstableMode (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 9 1) 1 :=
  ⟨(fourierMode_isCrossLinearizedSolution_iff _ _ _ _ _).2 example_eigen,
    (tendsto_norm_fourierMode_iff example_ne 1 1).2 (by norm_num),
    ⟨1, by norm_num, ![3, 1], example_ne, example_eigen⟩⟩

/-- The kinetics are stable without diffusion: `tr J = -2`, `det J = 1`. -/
example : (kellerSegelJacobian 1 1 1).trace = -2 ∧ (kellerSegelJacobian 1 1 1).det = 1 := by
  constructor
  · norm_num [kellerSegelJacobian, Matrix.trace_fin_two]
  · norm_num [kellerSegelJacobian, Matrix.det_fin_two_of]

/-- With the diagonal diffusion `diag(1, 1)` the same kinetics are stable at `k = 1`: the mode
matrix `[[-2, 0], [1, -2]]` has trace `-4` and determinant `4`. -/
example : ¬ IsUnstableMode (kellerSegelJacobian 1 1 1) 1 1 1 := by
  rw [isUnstableMode_iff]
  norm_num [modeMatrix, diffusionMatrix, kellerSegelJacobian, Matrix.trace_fin_two,
    Matrix.det_fin_two]

/-- The hypotheses of `kellerSegel_crossDiffusionDriven` hold for the running example
(`(2 √1 + 1 + 1) / 1 = 4 < 9`), and its conclusion agrees with the direct witness above. -/
example : ∃ k, IsCrossUnstableMode (kellerSegelJacobian 1 1 1)
    (kellerSegelDiffusion 1 1 9 1) k :=
  (kellerSegel_crossDiffusionDriven one_pos one_pos one_pos one_pos one_pos
    (by norm_num)).2

/-- The dispersion polynomial of the running example is negative at `q = 1` (value `-5`), so
`1` lies in the unstable band. -/
example : crossDispersionDet (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 9 1) 1 =
    -5 := by
  norm_num [crossDispersionDet, crossCoeff, kellerSegelJacobian, kellerSegelDiffusion,
    Matrix.det_fin_two_of]

/-- On `[0, π]` the first Neumann mode has wavenumber `1`, so it is the unstable mode above. -/
example : IsCrossUnstableMode (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 9 1)
    (neumannWavenumber Real.pi 1) := by
  rw [show neumannWavenumber Real.pi 1 = 1 by simp [neumannWavenumber, Real.pi_ne_zero]]
  exact ⟨1, by norm_num, ![3, 1], example_ne, example_eigen⟩

/-! ### Boundary: the threshold `χ = 4` -/

/-- At `χ = 4` the dispersion polynomial is `(q - 1)²`. -/
theorem threshold_crossDispersionDet (q : ℝ) :
    crossDispersionDet (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 4 1) q =
      (q - 1) ^ 2 := by
  norm_num [crossDispersionDet, crossCoeff, kellerSegelJacobian, kellerSegelDiffusion,
    Matrix.det_fin_two_of]
  ring

/-- At the threshold no mode is unstable: `tr (J - k² D) = -2 - 2 k² < 0` and
`det (J - k² D) = (k² - 1)² ≥ 0`, computed from the definitions. -/
example (k : ℝ) :
    ¬ IsCrossUnstableMode (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 4 1) k := by
  rw [isCrossUnstableMode_iff, det_crossModeMatrix, threshold_crossDispersionDet]
  push Not
  refine ⟨?_, sq_nonneg _⟩
  norm_num [crossModeMatrix, kellerSegelJacobian, kellerSegelDiffusion, Matrix.trace_fin_two]
  nlinarith [sq_nonneg k]

/-- At the threshold `k = 1` is marginal: `det (J - D) = 0`. -/
example :
    (crossModeMatrix (kellerSegelJacobian 1 1 1) (kellerSegelDiffusion 1 1 4 1) 1).det = 0 := by
  norm_num [crossModeMatrix, kellerSegelJacobian, kellerSegelDiffusion, Matrix.det_fin_two]

/-- The criterion's strict inequality fails at the threshold (`2 √1 = 2 = 4 - 1 - 1`). -/
example : ¬ ∃ k, IsCrossUnstableMode (kellerSegelJacobian 1 1 1)
    (kellerSegelDiffusion 1 1 4 1) k := by
  rw [kellerSegel_turing_iff one_pos one_pos one_pos one_pos]
  norm_num

/-! ### Minimal Keller–Segel -/

/-- Mode `1` is unstable: the mode matrix `[[-1, 4], [1, -2]]` has determinant `-2`. -/
example : IsCrossUnstableMode (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1) 1 := by
  rw [isCrossUnstableMode_iff]
  right
  norm_num [crossModeMatrix, kellerSegelJacobian, kellerSegelDiffusion, Matrix.det_fin_two]

/-- Mode `2` is stable: `[[-4, 16], [1, -5]]` has trace `-9` and determinant `4`. -/
example : ¬ IsCrossUnstableMode (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1) 2 := by
  rw [isCrossUnstableMode_iff]
  norm_num [crossModeMatrix, kellerSegelJacobian, kellerSegelDiffusion, Matrix.det_fin_two,
    Matrix.trace_fin_two]

/-- `k = √3` is marginal: `[[-3, 12], [1, -4]]` has determinant `0`, so it is not unstable,
matching the strict condition `1 · 1 · 3 < 4 - 1` failing. -/
example : ¬ IsCrossUnstableMode (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1)
    (Real.sqrt 3) := by
  rw [isCrossUnstableMode_iff]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [crossModeMatrix, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, h3]
  norm_num [kellerSegelJacobian, kellerSegelDiffusion]

/-- The same three cases through the theorem: `k² < 3` exactly. -/
example : (IsCrossUnstableMode (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1) 1) ∧
    ¬ IsCrossUnstableMode (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1) 2 := by
  rw [minimalKellerSegel_isCrossUnstableMode_iff one_pos zero_le_one zero_le_one one_ne_zero,
    minimalKellerSegel_isCrossUnstableMode_iff one_pos zero_le_one zero_le_one two_ne_zero]
  norm_num

/-- The homogeneous mode of the minimal model is neutral, not unstable: the mode matrix at
`k = 0` is `[[0, 0], [1, -1]]`, trace `-1`, determinant `0`. -/
example : ¬ IsCrossUnstableMode (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1) 0 := by
  rw [isCrossUnstableMode_iff]
  norm_num [crossModeMatrix, kellerSegelJacobian, Matrix.det_fin_two, Matrix.trace_fin_two]

/-- Through the theorem: on `[0, π]` the first Neumann mode (`k = 1`) is unstable for the minimal
model, as the Neumann criterion `1 · 1 · 1 < 4 - 1` says (direct check: mode `1` above). -/
example : ∃ n : ℕ, 0 < n ∧ IsCrossUnstableMode (kellerSegelJacobian 0 1 1)
    (kellerSegelDiffusion 1 1 4 1) (neumannWavenumber Real.pi n) := by
  rw [minimalKellerSegel_exists_neumann_iff one_pos zero_le_one zero_le_one Real.pi_pos,
    div_self Real.pi_ne_zero]
  norm_num

/-- Directly from the definitions: on `[0, π / 2]` the Neumann wavenumbers are `k = 2 n`, and
for `n ≥ 1` the mode matrix `[[-k², 4 k²], [1, -1 - k²]]` has trace `-1 - 2 k² < 0` and
determinant `k² (k² - 3) = 4 n² (4 n² - 3) > 0`, so no nonhomogeneous mode is unstable. -/
example : ¬ ∃ n : ℕ, 0 < n ∧ IsCrossUnstableMode (kellerSegelJacobian 0 1 1)
    (kellerSegelDiffusion 1 1 4 1) (neumannWavenumber (Real.pi / 2) n) := by
  rintro ⟨n, hn, h⟩
  have hk : neumannWavenumber (Real.pi / 2) n = 2 * n := by
    rw [neumannWavenumber, div_eq_iff (by positivity)]
    ring
  have htr : (crossModeMatrix (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1)
      (2 * n)).trace = -1 - 2 * (2 * n) ^ 2 := by
    simp [crossModeMatrix, Matrix.trace_fin_two, kellerSegelJacobian, kellerSegelDiffusion]
    ring
  have hdet : (crossModeMatrix (kellerSegelJacobian 0 1 1) (kellerSegelDiffusion 1 1 4 1)
      (2 * n)).det = (2 * n) ^ 2 * ((2 * n) ^ 2 - 3) := by
    simp [crossModeMatrix, Matrix.det_fin_two, kellerSegelJacobian, kellerSegelDiffusion]
    ring
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 4 ≤ (2 * (n : ℝ)) ^ 2 := by nlinarith
  rw [isCrossUnstableMode_iff, hk, htr, hdet] at h
  rcases h with h | h <;> nlinarith

/-- The same `[0, π / 2]` case through the theorem: the first Neumann mode has `k = 2`, beyond
the band (`4 ≥ 3`). -/
example : ¬ ∃ n : ℕ, 0 < n ∧ IsCrossUnstableMode (kellerSegelJacobian 0 1 1)
    (kellerSegelDiffusion 1 1 4 1) (neumannWavenumber (Real.pi / 2) n) := by
  rw [minimalKellerSegel_exists_neumann_iff one_pos zero_le_one zero_le_one
    (by positivity), show Real.pi / (Real.pi / 2) = 2 by field_simp]
  norm_num

/-! ### Junk values -/

/-- With `det D = 0` the band ends divide by zero and evaluate to `0`. -/
example (J : Matrix (Fin 2) (Fin 2) ℝ) : crossBandLower J 0 = 0 ∧ crossBandUpper J 0 = 0 := by
  simp [crossBandLower, crossBandUpper]

end MathlibExtTest.Biology.Dynamics.TuringCrossDiffusion
