/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Homogeneous

open scoped Matrix
open ControlTheory

-- Quarter-turn rotation in the plane, embedded in `Fin 3`,
-- with translation `p = (1, 2, 3)` and `q = (4, 5, 6)`, so
-- `R *ᵥ q = (-5, 4, 6)`.
private def rotZ : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, 0; 1, 0, 0; 0, 0, 1]

-- At `w = 1` this is the point action `R *ᵥ q + p`.
example :
    homogeneousMatrix rotZ (fun i => ![1, 2, 3] i) *ᵥ
        (Sum.elim (fun i => ![4, 5, 6] i) (fun _ => 1))
      = Sum.elim (fun i => ![-4, 6, 9] i) (fun _ => 1) := by
  rw [homogeneousMatrix_mulVec_elim]
  congr 1
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct] <;> norm_num

-- At `w = 0` the translation vanishes: the vector action.
example :
    homogeneousMatrix rotZ (fun i => ![1, 2, 3] i) *ᵥ
        (Sum.elim (fun i => ![4, 5, 6] i) (fun _ => 0))
      = Sum.elim (fun i => ![-5, 4, 6] i) (fun _ => 0) := by
  rw [homogeneousMatrix_mulVec_elim]
  congr 1
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct] <;> norm_num

-- At `w = 2` the translation is scaled, and the bottom
-- coordinate stays `2`.
example :
    homogeneousMatrix rotZ (fun i => ![1, 2, 3] i) *ᵥ
        (Sum.elim (fun i => ![4, 5, 6] i) (fun _ => 2))
      = Sum.elim (fun i => ![-3, 8, 12] i) (fun _ => 2) := by
  rw [homogeneousMatrix_mulVec_elim]
  congr 1
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct] <;> norm_num

#print axioms homogeneousMatrix_mulVec_elim
