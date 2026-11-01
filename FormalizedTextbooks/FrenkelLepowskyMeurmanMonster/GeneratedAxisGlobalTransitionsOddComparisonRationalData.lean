/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRationalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00TensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01TensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02TensorData

/-! Complete rational input and candidate output packets for three original local comparisons. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
open scoped BigOperators

/-- The two actual original roots used by the three comparisons. -/
def generatedAxisGlobalOddRationalRootIndex : Fin 2 → Fin 9 := ![0, 6]

/-- Entire original spin factors from the complete physical source tables. -/
def generatedAxisGlobalOddRationalRootSpin : Fin 2 → Fin 4096 → ℤ :=
  ![generatedAxisGlobalOddRoot00Spin12, generatedAxisGlobalOddRoot06Spin08]

/-- Entire original spatial factors from the same source products. -/
def generatedAxisGlobalOddRationalRootSpatial : Fin 2 → Fin 24 → ℤ :=
  ![generatedAxisGlobalOddRoot00Spatial12, generatedAxisGlobalOddRoot06Spatial08]

/-- Genuine original tensor denominators from the complete source state assemblies. -/
def generatedAxisGlobalOddRationalRootDenominator : Fin 2 → ℕ := ![4, 2]

/-- A complete input packet retains every actual matrix, short and scaled tensor coordinate. -/
def generatedAxisGlobalOddRationalRootPacket (k : Fin 2) : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddRootMatrixQ (generatedAxisGlobalOddRationalRootIndex k),
    (generatedAxisGlobalOddRootShortQ (generatedAxisGlobalOddRationalRootIndex k),
      fun t j => (generatedAxisGlobalOddRationalRootSpin k (generatedAxisGlobalSpinLabel t) : ℚ) *
        (generatedAxisGlobalOddRationalRootSpatial k j : ℚ) /
          (generatedAxisGlobalOddRationalRootDenominator k : ℚ)))

/-- All three comparison short packets include the original preferred basis correction signs. -/
def generatedAxisGlobalOddComparisonShortQ (k : Fin 3) (r : GriessShortIndex) : ℚ :=
  ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
    generatedAxisGlobalOddShortCoefficientQ p *
      (generatedAxisGlobalIntSign (generatedAxisGlobalOddComparisonShortPhases k
        (generatedAxisGlobalOddShortPacketNumber p)) : ℚ) *
      (if generatedAxisGlobalOddComparisonShortLabels k
        (generatedAxisGlobalOddShortPacketNumber p) = r then 1 else 0)

/-- The three complete candidate spin factors are immutable original coordinate tables. -/
def generatedAxisGlobalOddRationalComparisonSpin : Fin 3 → Fin 4096 → ℤ :=
  ![generatedAxisGlobalOddComparison00Spin, generatedAxisGlobalOddComparison01Spin,
    generatedAxisGlobalOddComparison02Spin]

/-- The three complete candidate spatial factors retain the original coordinate orientation. -/
def generatedAxisGlobalOddRationalComparisonSpatial : Fin 3 → Fin 24 → ℤ :=
  ![generatedAxisGlobalOddComparison00Spatial, generatedAxisGlobalOddComparison01Spatial,
    generatedAxisGlobalOddComparison02Spatial]

/-- Original target denominators, including the distinct root-six normalization. -/
def generatedAxisGlobalOddRationalComparisonDenominator : Fin 3 → ℕ := ![8, 8, 4]

/-- Every comparison coordinate is stated, with its genuine square-root tensor normalization. -/
def generatedAxisGlobalOddRationalComparisonPacket (k : Fin 3) :
    GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddComparisonMatrixQ k,
    (generatedAxisGlobalOddComparisonShortQ k,
      fun t j => (generatedAxisGlobalOddRationalComparisonSpin k
          (generatedAxisGlobalSpinLabel t) : ℚ) *
        (generatedAxisGlobalOddRationalComparisonSpatial k j : ℚ) /
          (generatedAxisGlobalOddRationalComparisonDenominator k : ℚ)))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
