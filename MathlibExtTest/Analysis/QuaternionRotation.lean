/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.QuaternionRotation

-- The packaged homomorphism into the existing special orthogonal group carrier.
example :
    ∃ R : unitary (Quaternion ℝ) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ u : unitary (Quaternion ℝ),
        (R u : Matrix (Fin 3) (Fin 3) ℝ) = QuaternionRotation.rotMatrix (u : Quaternion ℝ) :=
  QuaternionRotation.exists_unitary_hom_specialOrthogonalGroup

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
