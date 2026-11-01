/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives

/-! Complete original physical spatial source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every actual original spatial coefficient at source stage 1. -/
theorem generatedAxisGlobalOddRoot02SpatialStep01_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot02Spatial00 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spatial01 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 2. -/
theorem generatedAxisGlobalOddRoot02SpatialStep02_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot02Spatial01 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spatial02 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 3. -/
theorem generatedAxisGlobalOddRoot02SpatialStep03_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot02Spatial02 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spatial03 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 4. -/
theorem generatedAxisGlobalOddRoot02SpatialStep04_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot02Spatial03 i =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spatial04 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 5. -/
theorem generatedAxisGlobalOddRoot02SpatialStep05_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot02Spatial04 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot02Spatial05 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 6. -/
theorem generatedAxisGlobalOddRoot02SpatialStep06_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot02Spatial05 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot02Spatial06 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 7. -/
theorem generatedAxisGlobalOddRoot02SpatialStep07_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot02Spatial06 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot02Spatial07 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 9. -/
theorem generatedAxisGlobalOddRoot02SpatialStep09_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot02Spatial08 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot02Spatial09 i := by
  revert i
  decide +kernel

/-- Every actual original spatial coefficient at source stage 10. -/
theorem generatedAxisGlobalOddRoot02SpatialStep10_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot02Spatial09 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot02Spatial10 i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
