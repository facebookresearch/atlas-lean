/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives

/-! Complete original physical spatial source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every actual original spatial coefficient at source stage 2. -/
theorem generatedAxisGlobalOddRoot03SpatialStep02_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot03Spatial01 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot03Spatial02 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 3. -/
theorem generatedAxisGlobalOddRoot03SpatialStep03_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot03Spatial02 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot03Spatial03 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 5. -/
theorem generatedAxisGlobalOddRoot03SpatialStep05_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot03Spatial04 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot03Spatial05 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 6. -/
theorem generatedAxisGlobalOddRoot03SpatialStep06_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot03Spatial05 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot03Spatial06 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 7. -/
theorem generatedAxisGlobalOddRoot03SpatialStep07_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot03Spatial06 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot03Spatial07 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 8. -/
theorem generatedAxisGlobalOddRoot03SpatialStep08_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot03Spatial07 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot03Spatial08 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 9. -/
theorem generatedAxisGlobalOddRoot03SpatialStep09_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot03Spatial08 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot03Spatial09 i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
