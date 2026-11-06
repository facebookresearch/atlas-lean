/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal finite reflection determinant gives the genuine local sign homomorphism. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Hom
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationAbelianImages
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual source sign is the determinant of its exact characteristic-three matrix image. -/
def y322Orthogonal3Sign : Y322Presentation →* (ZMod 3)ˣ :=
  Matrix.GeneralLinearGroup.det.comp y322Orthogonal3Hom

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- The determinant is computed from the actual seven-dimensional first reflection matrix.
/-- The first literal reflection has determinant minus one in the actual finite field. -/
theorem y322Orthogonal3Generator_zero_det :
    Matrix.GeneralLinearGroup.det (y322Orthogonal3Generator 0) = -1 := by
  apply Units.ext
  change (y322Orthogonal3Reflection 0).det = (-1 : ZMod 3)
  rw [Matrix.det_of_isUpperTriangular]
  · decide +kernel
  · decide +kernel

/-- All eight original source generators have genuine determinant minus one. -/
theorem y322Orthogonal3Sign_generator (i : Fin 8) :
    y322Orthogonal3Sign (PresentedGroup.of i) = -1 := by
  rw [y322AbelianImage_generator y322Orthogonal3Sign i]
  change Matrix.GeneralLinearGroup.det (y322Orthogonal3Hom (PresentedGroup.of 0)) = -1
  rw [y322Orthogonal3Hom_generator, y322Orthogonal3Generator_zero_det]

/-- The genuine finite-field sign is nontrivial. -/
theorem y322Orthogonal3Sign_generator_ne_one :
    y322Orthogonal3Sign (PresentedGroup.of 0) ≠ 1 := by
  rw [y322Orthogonal3Sign_generator]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
