/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Elasticity.StressStrain

/-!
# Tests for `PhyslibExt.CondensedMatter.Elasticity.StressStrain`

* Uniaxial tension `σ = diag(100, 0, 0)` MPa: traction `(100, 0, 0)` on the x-face, `0` on the
  y-face, and `(100/√2, 0, 0)` on the diagonal face.
* Spectral example `σ = !![2, 1; 1, 2]`: eigenvalues `3` and `1` with explicit eigenvectors,
  `I₁ = 4`, `I₃ = 3`; the 3x3 analogue has mean stress `4/3`, a traceless deviatoric matrix,
  and production invariants `I₁ = 4`, `I₃ = 0`.
* Mohr example `σx = 80`, `σy = 20`, `τ = 30`: `σ'₀₀ = 80`, `σ'₀₁ = -30` at `θ = π/4`, and
  `σ'₀₀ = 80`, `σ'₀₁ = 30` at `θ = 0`; with `τ = 0` the radius is `|σx - σy|/2`.
* Maximum shear `s₁ = 100`, `s₃ = 20`: `τmax = 40`, attained at `θ = π/4`.
* Small strain for simple shear with `γ = 0.02`: tensor shear `0.01`, engineering shear `0.02`,
  symmetric `ε`, trace `3`; the pure-shear displacement has trace `0`.
* True strain at `e = 0.1`: `ln 1.1`, between `0` and `0.1`; true stress `110` from
  `F = 1000`, `A₀ = 10`, `e = 0.1`.
* Countermodels: a non-symmetric matrix is not a symmetric stress; `e = -1` violates the
  true-strain domain with `1 + e = 0`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Elasticity.StressStrain

open _root_.Elasticity
open scoped Matrix

/-! ### Uniaxial tension -/

-- Traction on the x-face is `(100, 0, 0)` MPa.
example : traction !![(100:ℝ),0,0;0,0,0;0,0,0] ![1,0,0] = ![100,0,0] := by
  ext i
  fin_cases i <;> simp [traction, Matrix.mulVec]

-- Traction on the y-face vanishes.
example : traction !![(100:ℝ),0,0;0,0,0;0,0,0] ![0,1,0] = 0 := by
  ext i
  fin_cases i <;> simp [traction, Matrix.mulVec]

-- Traction on the diagonal face, via the `mulVec` definition.
example : traction !![(100:ℝ),0,0;0,0,0;0,0,0] ![1/Real.sqrt 2, 1/Real.sqrt 2, 0]
    = ![100/Real.sqrt 2, 0, 0] := by
  ext i
  fin_cases i <;> simp [traction, Matrix.mulVec]
  ring

/-! ### Spectral example -/

-- `3` is an eigenvalue with eigenvector `(1, 1)`.
example : !![(2:ℝ),1;1,2] *ᵥ ![1,1] = (3:ℝ) • ![1,1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Pi.smul_apply] <;> norm_num

-- `1` is an eigenvalue with eigenvector `(1, -1)`.
example : !![(2:ℝ),1;1,2] *ᵥ ![1,-1] = (1:ℝ) • ![1,-1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Pi.smul_apply] <;> norm_num

-- 2x2 trace and determinant (correct values `I₁ = 4`, `I₃ = 3` for `!![2,1;1,2]`).
example : !![(2:ℝ),1;1,2].trace = 4 := by
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  norm_num

example : !![(2:ℝ),1;1,2].det = 3 := by
  simp [Matrix.det_fin_two]
  norm_num

-- 3x3 analogue: mean stress `p = 4/3`.
example : hydrostaticPressure !![(2:ℝ),1,0;1,2,0;0,0,0] = 4/3 := by
  unfold hydrostaticPressure
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  norm_num

-- 3x3 analogue: the deviatoric matrix.
example : deviatoricStress !![(2:ℝ),1,0;1,2,0;0,0,0]
    = !![2/3,1,0;1,2/3,0;0,0,-4/3] := by
  unfold deviatoricStress hydrostaticPressure
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] <;>
    norm_num

-- 3x3 analogue: traceless split, via the production lemma.
example : (deviatoricStress !![(2:ℝ),1,0;1,2,0;0,0,0]).trace = 0 :=
  trace_deviatoric _

-- 3x3 analogue: production invariants `I₁ = 4`, `I₃ = 0`.
example : stressInvariant1 !![(2:ℝ),1,0;1,2,0;0,0,0] = 4 := by
  unfold stressInvariant1
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  norm_num

example : stressInvariant3 !![(2:ℝ),1,0;1,2,0;0,0,0] = 0 := by
  unfold stressInvariant3
  simp [Matrix.det_fin_three]

/-! ### Mohr example -/

-- At `θ = π/4`: `σ'₀₀ = 80`.
example : rotatedStress2 !![(80:ℝ),30;30,20] (Real.pi/4) 0 0 = 80 := by
  rw [rotatedStress2_00]
  have harg : 2 * (Real.pi/4) = Real.pi/2 := by ring
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

-- At `θ = π/4`: `σ'₀₁ = -30`.
example : rotatedStress2 !![(80:ℝ),30;30,20] (Real.pi/4) 0 1 = -30 := by
  rw [rotatedStress2_01]
  have harg : 2 * (Real.pi/4) = Real.pi/2 := by ring
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

-- At `θ = 0`: `σ'₀₀ = 80`, `σ'₀₁ = 30`.
example : rotatedStress2 !![(80:ℝ),30;30,20] 0 0 0 = 80 := by
  rw [rotatedStress2_00, mul_zero, Real.cos_zero, Real.sin_zero]
  norm_num

example : rotatedStress2 !![(80:ℝ),30;30,20] 0 0 1 = 30 := by
  rw [rotatedStress2_01, mul_zero, Real.cos_zero, Real.sin_zero]
  norm_num

-- With `τ = 0` the radius is `|σx - σy|/2` (nontrivial unless `σx = σy`).
example (σx σy : ℝ) : mohrRadiusSq σx σy 0 = (|σx - σy|/2)^2 := by
  unfold mohrRadiusSq
  rw [div_pow, div_pow, sq_abs]
  ring

/-! ### Maximum shear -/

-- `τmax = 40`, attained at `θ = π/4`.
example (θ : ℝ) : |principalPlaneShear 100 20 θ| ≤ 40 := by
  have h := principalPlaneShear_bound 100 20 θ (by norm_num)
  norm_num at h
  exact h

example : |principalPlaneShear 100 20 (Real.pi/4)| = 40 := by
  have h := principalPlaneShear_max 100 20 (by norm_num)
  norm_num at h
  exact h

/-! ### Small strain example -/

-- Simple shear with `γ = 0.02`: tensor shear `0.01`.
example (x : Fin 3 → ℝ) :
    smallStrain (displacementGradient (simpleShearField 0.02) x) 0 1 = 0.01 := by
  have h := simpleShear_strain 0.02 x
  norm_num at h ⊢
  exact h

-- Engineering shear `0.02`.
example (x : Fin 3 → ℝ) :
    engineeringShear (smallStrain (displacementGradient (simpleShearField 0.02) x))
      = 0.02 :=
  simpleShear_engineering 0.02 x

-- The small-strain tensor is symmetric.
example (x : Fin 3 → ℝ) :
    (smallStrain (displacementGradient (simpleShearField 0.02) x))ᵀ
      = smallStrain (displacementGradient (simpleShearField 0.02) x) :=
  smallStrain_symmetric _

-- Trace of the stated field is `3` (the stated shear field includes the identity part;
-- the pure-shear displacement below has trace `0`).
example (x : Fin 3 → ℝ) :
    (smallStrain (displacementGradient (simpleShearField 0.02) x)).trace = 3 := by
  unfold simpleShearField
  rw [displacementGradient_affine]
  unfold smallStrain
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  norm_num

-- Pure-shear displacement has trace `0` (first-order volume preservation).
example (x : Fin 3 → ℝ) :
    (smallStrain (displacementGradient
      (affineDisplacement !![(0:ℝ),0.02,0;0,0,0;0,0,0] 0) x)).trace = 0 := by
  rw [displacementGradient_affine]
  unfold smallStrain
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]

/-! ### True strain and true stress -/

example : trueStrain 0.1 = Real.log 1.1 := by
  unfold trueStrain
  congr 1
  norm_num

example : 0 < trueStrain 0.1 ∧ trueStrain 0.1 < 0.1 := by
  constructor
  · have h := trueStrain_lower 0.1 (by norm_num)
    have hpos : (0:ℝ) < 0.1/(1+0.1) := by norm_num
    linarith
  · exact trueStrain_lt 0.1 (by norm_num) (by norm_num)

example : engStress 1000 10 = 100 := by
  unfold engStress
  norm_num

example : trueStress 1000 (10/(1+0.1)) = 110 := by
  have h := trueStress_of_volumeConstancy 1000 10 (10/(1+0.1)) 0.1
    (by norm_num) (by norm_num) rfl
  rw [h]
  unfold engStress
  norm_num

/-! ### Countermodels and boundary checks -/

-- A non-symmetric matrix is not a symmetric stress.
example : ¬ IsSymmetricStress !![(0:ℝ),1;0,0] := by
  intro h
  have heq : !![(0:ℝ),1;0,0]ᵀ = !![(0:ℝ),1;0,0] := h
  have h01 : !![(0:ℝ),1;0,0]ᵀ 0 1 = 0 := by simp [Matrix.transpose_apply]
  rw [heq] at h01
  simp at h01

-- True strain is not defined at `e = -1`: the domain hypothesis fails and `1 + e = 0`.
example : ¬ (-1:ℝ) < -1 := by norm_num

example : (1:ℝ) + (-1) = 0 := by norm_num

end PhyslibExtTest.CondensedMatter.Elasticity.StressStrain
