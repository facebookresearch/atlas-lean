/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExtTest.LinearAlgebra.Basis.FiniteFiltration
import MathlibExt.LinearAlgebra.Determinant.FiltrationUnipotent
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum

/-!
# A nonidentity shear on the coordinate flag

The map (x,y) ↦ (x+y,y) preserves the proper rational coordinate flag and acts
as the identity on both graded lines. Its determinant is one. The empty
filtration is also tested on the zero-dimensional module.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace MathlibExtTest.FiniteFiltration

def shear : V →ₗ[ℚ] V := Matrix.toLin' !![1, 1; 0, 1]

@[simp]
theorem shear_apply (x : V) : shear x = ![x 0 + x 1, x 1] := by
  rw [shear, Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem shear_sub_mem (i : Fin 2) (x : V) (hx : x ∈ flag (i.val + 1)) :
    shear x - x ∈ flag i.val := by
  fin_cases i
  · have hx1 : x 1 = 0 := by exact hx
    change shear x - x = 0
    ext j
    fin_cases j
    · change (shear x) 0 - x 0 = 0
      rw [shear_apply]
      change x 0 + x 1 - x 0 = 0
      simp only [hx1, add_zero, sub_self]
    · change (shear x) 1 - x 1 = 0
      rw [shear_apply]
      change x 1 - x 1 = 0
      exact sub_self _
  · change (shear x) 1 - x 1 = 0
    rw [shear_apply]
    change x 1 - x 1 = 0
    exact sub_self _

example : shear (Pi.single 1 1) = ![1, 1] := by simp [Pi.single]

example : shear.det = 1 := by
  exact LinearMap.det_eq_one_of_forall_sub_mem
    (κ := GradeIndex) flag flag_zero 2 flag_le gradedBasis flag_two_top shear shear_sub_mem

example : (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)).det = 1 := by
  let F : ℕ → Submodule ℚ (Fin 0 → ℚ) := fun _ => ⊥
  have htop : F 0 = ⊤ := by
    ext x
    simp only [F, Submodule.mem_bot, Submodule.mem_top, iff_true]
    exact Subsingleton.elim x 0
  exact LinearMap.det_eq_one_of_sub_mem_ofFiltration (κ := fun _ => Fin 0)
    F rfl 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) htop
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) (fun i => Fin.elim0 i)

-- Naturals have a commutative multiplication but are not a ring.
example :
    ![(2 : ℕ), 6, 30] (Fin.last 2) =
      2 * ∏ i : Fin 2, ![(3 : ℕ), 5] i := by
  apply Fin.last_eq_first_mul_prod
  intro i
  fin_cases i <;> norm_num

end MathlibExtTest.FiniteFiltration
