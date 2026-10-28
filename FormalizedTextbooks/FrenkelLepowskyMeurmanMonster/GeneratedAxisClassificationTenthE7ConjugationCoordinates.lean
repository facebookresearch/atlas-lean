/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7Conjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFlagData

/-! Exact original seven-pair projector after the certified physical coordinate transport. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The physical octad support of the transported seven-dimensional subspace. -/
def generatedTenthE7OctadSupport : Finset (Fin 24) := {5, 6, 12, 15, 16, 17, 21, 23}

/-- The actual perpendicular root direction inside that coordinate octad. -/
def generatedTenthE7NormalDirection : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]

/-- Twice the projector onto the actual coordinate octad hyperplane. -/
def generatedTenthE7ProjectionInteger : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  (if i = j ∧ i ∈ generatedTenthE7OctadSupport then 2 else 0) -
    generatedTenthE7NormalDirection i * generatedTenthE7NormalDirection j

/-- The original signed norm-twelve direction in transported physical coordinates. -/
def generatedTenthE7LineDirection : Fin 24 → ℤ := ![0, 0, 0, 0, -1, 0, 0, 1, -1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]

set_option maxHeartbeats 8000000 in
-- Check the whole original physical projector identity, including all zero entries.
/-- The seven actual pair lines become the octad hyperplane perpendicular to the actual root. -/
theorem generatedTenth_e7_pair_projection_integer :
    generatedTenthE7Numerator * generatedTenthPairProjectionInteger *
      generatedTenthE7Numerator.transpose = (4 : ℤ) • generatedTenthE7ProjectionInteger := by
  decide +kernel

/-- The complete actual distinguished physical line transforms with its specified orientation. -/
theorem generatedTenth_e7_line_direction_integer :
    generatedTenthE7Numerator *ᵥ generatedTenthLineDirection =
      (2 : ℤ) • generatedTenthE7LineDirection := by
  decide +kernel

/-- The distinguished norm-twelve line is supported outside the actual coordinate octad. -/
theorem generatedTenth_e7_line_outside :
    ∀ i ∈ generatedTenthE7OctadSupport, generatedTenthE7LineDirection i = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
