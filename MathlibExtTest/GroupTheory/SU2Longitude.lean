/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SU2Longitude

namespace MathlibExtTest.GroupTheory.SU2Longitude

open MathlibExt.GroupTheory.SU2Longitude
open Matrix

/-- The longitude isomorphism sends `1` to `1`. -/
theorem longitudeMulEquiv_one : longitudeMulEquiv 1 = 1 := map_one _

/-- The diagonal rotation through `π / 2` is `diag (i, -i)`. -/
theorem longitude_pi_div_two :
    (longitudeMap (Multiplicative.ofAdd (↑(Real.pi / 2) : AddCircle (2 * Real.pi)))).val.val =
      !![Complex.I, 0; 0, -Complex.I] := by
  rw [longitudeMap_apply_ofAdd_mk]
  show diagRotation (Real.pi / 2) = _
  rw [diagRotation_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Complex.exp_pi_div_two_mul_I, Complex.exp_neg]

/-- The diagonal rotation through `π` is `-1`. -/
theorem longitude_pi :
    (diagRotationToLongitude Real.pi).val.val =
      (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  show diagRotation Real.pi = _
  rw [diagRotation_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Complex.exp_pi_mul_I]

/-- The angles `0` and `π` give different longitude elements. -/
theorem longitude_zero_ne_pi :
    longitudeMulEquiv (Multiplicative.ofAdd (↑(0 : ℝ) : AddCircle (2 * Real.pi))) ≠
      longitudeMulEquiv (Multiplicative.ofAdd (↑Real.pi : AddCircle (2 * Real.pi))) := by
  intro h
  have h2 := longitudeMulEquiv.injective h
  have h3 : (↑(0 : ℝ) : AddCircle (2 * Real.pi)) = ↑Real.pi :=
    congrArg Multiplicative.toAdd h2
  rw [QuotientAddGroup.eq] at h3
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h3
  have hk2 : (k : ℝ) * (2 * Real.pi) = Real.pi := by
    simpa [zsmul_eq_mul] using hk
  have hzero : (2 * (k : ℝ) - 1) * Real.pi = 0 := by linarith [hk2]
  have hk3 : 2 * (k : ℝ) - 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right Real.pi_pos.ne'
  have hk4 : 2 * k - 1 = 0 := by exact_mod_cast hk3
  omega

end MathlibExtTest.GroupTheory.SU2Longitude
