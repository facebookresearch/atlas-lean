/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives

/-! Every original physical spatial source coordinate is certified exactly. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Complete original spatial transport at stage 1. -/
theorem generatedAxisGlobalOddRoot04SpatialStep01_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot04Spatial00 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial01 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 2. -/
theorem generatedAxisGlobalOddRoot04SpatialStep02_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 3 generatedAxisGlobalOddRoot04Spatial01 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial02 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 3. -/
theorem generatedAxisGlobalOddRoot04SpatialStep03_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot04Spatial02 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial03 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 4. -/
theorem generatedAxisGlobalOddRoot04SpatialStep04_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot04Spatial03 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial04 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 5. -/
theorem generatedAxisGlobalOddRoot04SpatialStep05_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot04Spatial04 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial05 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 6. -/
theorem generatedAxisGlobalOddRoot04SpatialStep06_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 3 generatedAxisGlobalOddRoot04Spatial05 i =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial06 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 7. -/
theorem generatedAxisGlobalOddRoot04SpatialStep07_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot04Spatial06 i =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spatial07 i := by
  revert i
  decide +kernel

/-- Complete original spatial transport at stage 8. -/
theorem generatedAxisGlobalOddRoot04SpatialStep08_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot04Spatial07 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot04Spatial08 i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
