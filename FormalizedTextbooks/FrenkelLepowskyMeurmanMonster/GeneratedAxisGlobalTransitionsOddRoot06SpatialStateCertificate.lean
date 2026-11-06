/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached

/-! Complete source-derived integer coefficient certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All 24 physical spatial coefficients of original primitive 1 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep01_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot06Spatial00 i =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot06Spatial01 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot06Spatial00 i =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot06Spatial01 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 2 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep02_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot06Spatial01 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial02 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7
      generatedAxisGlobalOddRoot06Spatial01 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial02 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 3 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep03_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot06Spatial02 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial03 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7
      generatedAxisGlobalOddRoot06Spatial02 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial03 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 4 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep04_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot06Spatial03 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial04 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot06Spatial03 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial04 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 5 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep05_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot06Spatial04 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial05 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot06Spatial04 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial05 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 6 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep06_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot06Spatial05 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial06 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9
      generatedAxisGlobalOddRoot06Spatial05 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial06 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 7 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep07_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot06Spatial06 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial07 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot06Spatial06 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial07 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 8 are exact. -/
theorem generatedAxisGlobalOddRoot06SpatialStep08_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot06Spatial07 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial08 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot06Spatial07 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial08 i := by decide +kernel
  exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
