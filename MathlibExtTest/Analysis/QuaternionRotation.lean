/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.QuaternionRotation

-- The packaged homomorphism is directly nameable, and its underlying matrix
-- is `rotMatrix`.
example (u : unitary (Quaternion ℝ)) :
    (QuaternionRotation.unitaryHomSpecialOrthogonalGroup u :
      Matrix (Fin 3) (Fin 3) ℝ) = QuaternionRotation.rotMatrix (u : Quaternion ℝ) :=
  QuaternionRotation.coe_unitaryHomSpecialOrthogonalGroup u

-- It can be used as a monoid homomorphism without choosing a witness.
example (u v : unitary (Quaternion ℝ)) :
    QuaternionRotation.unitaryHomSpecialOrthogonalGroup (u * v) =
      QuaternionRotation.unitaryHomSpecialOrthogonalGroup u *
        QuaternionRotation.unitaryHomSpecialOrthogonalGroup v :=
  map_mul _ u v

-- The quarter-turn fixture has determinant one through the determinant theorem.
example :
    (QuaternionRotation.rotMatrix (⟨√2 / 2, √2 / 2, 0, 0⟩ : Quaternion ℝ)).det = 1 :=
  QuaternionRotation.det_rotMatrix QuaternionRotation.quarterTurn_rotMatrix.1

-- The quarter-turn matrix itself, read off from the fixture.
example :
    QuaternionRotation.rotMatrix (⟨√2 / 2, √2 / 2, 0, 0⟩ : Quaternion ℝ) =
      !![1, 0, 0; 0, 0, -1; 0, 1, 0] :=
  QuaternionRotation.quarterTurn_rotMatrix.2.1

-- The nonunit scalar `2` is rejected by the unitary carrier.
example : (2 : Quaternion ℝ) ∉ unitary (Quaternion ℝ) :=
  QuaternionRotation.two_not_rotation.1

-- Kernel: on unit quaternions the identity matrix occurs exactly at `±1`.
example {q : Quaternion ℝ} (hq : ‖q‖ = 1) :
    QuaternionRotation.rotMatrix q = 1 ↔ q = 1 ∨ q = -1 :=
  QuaternionRotation.rotMatrix_eq_one_iff hq

-- In particular `-1` maps to the identity matrix.
example : QuaternionRotation.rotMatrix (-1 : Quaternion ℝ) = 1 :=
  (QuaternionRotation.rotMatrix_eq_one_iff (by simp)).mpr (Or.inr rfl)

-- Sign invariance holds for every quaternion, unit or not.
example (q : Quaternion ℝ) :
    QuaternionRotation.rotMatrix (-q) = QuaternionRotation.rotMatrix q :=
  QuaternionRotation.rotMatrix_neg q

-- The quarter turn is not the identity rotation.
example :
    QuaternionRotation.rotMatrix (⟨√2 / 2, √2 / 2, 0, 0⟩ : Quaternion ℝ) ≠ 1 :=
  QuaternionRotation.quarterTurn_rotMatrix_ne_one
