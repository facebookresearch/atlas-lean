/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached

/-! Complete source-derived integer coefficient certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All 24 physical spatial coefficients of original primitive 1 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep01_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot00Spatial00 i =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spatial01 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot00Spatial00 i =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spatial01 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 2 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep02_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot00Spatial01 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial02 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9
      generatedAxisGlobalOddRoot00Spatial01 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial02 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 3 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep03_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot00Spatial02 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial03 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7
      generatedAxisGlobalOddRoot00Spatial02 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial03 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 4 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep04_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot00Spatial03 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial04 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7
      generatedAxisGlobalOddRoot00Spatial03 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial04 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 5 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep05_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7 generatedAxisGlobalOddRoot00Spatial04 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial05 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 7
      generatedAxisGlobalOddRoot00Spatial04 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial05 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 6 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep06_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9 generatedAxisGlobalOddRoot00Spatial05 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial06 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 9
      generatedAxisGlobalOddRoot00Spatial05 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial06 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 7 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep07_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 5 generatedAxisGlobalOddRoot00Spatial06 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial07 i := by
  have h : ∀ i : Fin 24, (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 5
      generatedAxisGlobalOddRoot00Spatial06 i =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial07 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 8 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep08_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot00Spatial07 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial08 i := by
  have h : ∀ i : Fin 24, (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot00Spatial07 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spatial08 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 9 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep09_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot00Spatial08 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial09 i := by
  have h : ∀ i : Fin 24, (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6
      generatedAxisGlobalOddRoot00Spatial08 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial09 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 10 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep10_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6 generatedAxisGlobalOddRoot00Spatial09 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial10 i := by
  have h : ∀ i : Fin 24, (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 6
      generatedAxisGlobalOddRoot00Spatial09 i =
      1 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial10 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 11 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep11_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot00Spatial10 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial11 i := by
  have h : ∀ i : Fin 24, (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot00Spatial10 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial11 i := by decide +kernel
  exact h i

/-- All 24 physical spatial coefficients of original primitive 12 are exact. -/
theorem generatedAxisGlobalOddRoot00SpatialStep12_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot00Spatial11 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial12 i := by
  have h : ∀ i : Fin 24, (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0
      generatedAxisGlobalOddRoot00Spatial11 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial12 i := by decide +kernel
  exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
