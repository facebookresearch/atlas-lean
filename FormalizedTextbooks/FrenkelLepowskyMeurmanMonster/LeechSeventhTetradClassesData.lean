/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTriangleFiveTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhDoubleCoordinateCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration

/-! Ten genuine norm-eight tetrad vectors in the five complementary seventh coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A stated complementary coordinate distinct from the omitted tetrad coordinate. -/
def leechSeventhTetradNegativeCoordinate (t : Fin 24) : Fin 24 := if t = 12 then 13 else 12

/-- Four unit coefficients, with an optional one-coordinate sign reversal. -/
def leechSeventhTetradCoefficients (t : Fin 24) (b : Bool) (i : Fin 24) : ℤ :=
  if i ∈ generatedSeventhFiveFrameCoordinates ∧ i ≠ t then
    if b && decide (i = leechSeventhTetradNegativeCoordinate t) then -1 else 1
  else 0

set_option maxHeartbeats 0 in
-- This finite statement concerns only the five literal coordinate sets and their signs.
/-- Both genuine tetrad sign choices have even integral coordinate sum. -/
theorem leechSeventhTetrad_sum_even : ∀ t : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates → ∀ b : Bool,
      Even (∑ i, leechSeventhTetradCoefficients t b i) := by
  unfold generatedSeventhFiveFrameCoordinates leechSeventhTetradCoefficients
    leechSeventhTetradNegativeCoordinate
  decide +kernel

/-- The two stated signed tetrads are genuine lattice vectors, using source congruences. -/
def leechSeventhTetradLattice (t : {i // i ∈ generatedSeventhFiveFrameCoordinates}) (b : Bool) :
    leechIntegral :=
  ⟨(4 : ℤ) • leechSeventhTetradCoefficients t.val b,
    (leechSeventh_four_coordinate_mem_iff _).mpr (leechSeventhTetrad_sum_even t.val t.property b)⟩

set_option maxHeartbeats 0 in
-- Check all actual coordinate entries of each signed tetrad, not an abstract frame model.
/-- Every stated tetrad has the original integral square sum sixty-four. -/
theorem leechSeventhTetrad_square : ∀ t : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates → ∀ b : Bool,
      leechSquareSum ((4 : ℤ) • leechSeventhTetradCoefficients t b) = 64 := by
  unfold generatedSeventhFiveFrameCoordinates leechSeventhTetradCoefficients
    leechSeventhTetradNegativeCoordinate leechSquareSum
  decide +kernel

set_option maxHeartbeats 0 in
-- Signed common coordinates cancel modulo two; only the two omitted positions differ.
/-- Distinct omitted coordinates give the genuine two-coordinate difference parity. -/
theorem leechSeventhTetrad_difference_parity : ∀ t u : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates → u ∈ generatedSeventhFiveFrameCoordinates →
      t ≠ u → ∀ b c : Bool,
        integerParity (leechSeventhTetradCoefficients t b - leechSeventhTetradCoefficients u c) =
          leechSeventhPairParity t u := by
  unfold generatedSeventhFiveFrameCoordinates leechSeventhTetradCoefficients
    leechSeventhTetradNegativeCoordinate leechSeventhPairParity integerParity
  decide +kernel

/-- The exact coordinate half of the difference of two signs on one tetrad. -/
def leechSeventhTetradSignHalf (t : Fin 24) (b c : Bool) : Fin 24 → ℤ :=
  fun i => (leechSeventhTetradCoefficients t b i - leechSeventhTetradCoefficients t c i) / 2

set_option maxHeartbeats 0 in
-- Each sign difference is zero or plus/minus two at a stated actual coordinate.
/-- The same-tetrad half-difference has exactly the stated integer coordinates. -/
theorem leechSeventhTetrad_sign_half : ∀ t : Fin 24, ∀ b c : Bool,
    (2 : ℤ) • (leechSeventhTetradCoefficients t b - leechSeventhTetradCoefficients t c) =
      (4 : ℤ) • leechSeventhTetradSignHalf t b c := by
  unfold leechSeventhTetradSignHalf leechSeventhTetradCoefficients
    leechSeventhTetradNegativeCoordinate
  decide +kernel

set_option maxHeartbeats 0 in
-- A single actual sign reversal has odd total in its integral half-difference.
/-- The two signs on a stated tetrad have an odd half-difference coordinate sum. -/
theorem leechSeventhTetrad_sign_half_odd : ∀ t : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates → ∀ b c : Bool, b ≠ c →
      ¬Even (∑ i, leechSeventhTetradSignHalf t b c i) := by
  unfold generatedSeventhFiveFrameCoordinates leechSeventhTetradSignHalf
    leechSeventhTetradCoefficients leechSeventhTetradNegativeCoordinate
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
