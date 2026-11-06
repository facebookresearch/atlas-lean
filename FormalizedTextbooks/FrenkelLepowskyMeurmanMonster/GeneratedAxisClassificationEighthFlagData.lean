/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! The original eighth coordinate subspace is an actual Golay dodecad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The genuine Golay word with the twelve medium diagonal coordinates. -/
def generatedEighthDodecadWord : golayCode := golayCodeLabelEquiv 2292

/-- The original encoder gives exactly the twelve stated physical coordinates. -/
theorem generatedEighth_dodecad_mask : golayEncodedMask 2292 = 0xc5066f := by
  decide +kernel

/-- Every actual dodecad bit is bound to the original encoder. -/
theorem generatedEighth_dodecad_coordinate (i : Fin 24) :
    generatedEighthDodecadWord.val i = golayBooleanCast (Nat.testBit 0xc5066f i.val) := by
  change golayEncoder (golayLabelCoefficients 2292) i = _
  rw [golayLabelEncoder_boolean]
  change golayBooleanCast (Nat.testBit (golayEncodedMask 2292) i.val) = _
  rw [generatedEighth_dodecad_mask]

/-- The actual support has twelve coordinates. -/
theorem generatedEighth_dodecad_card :
    (Finset.univ.filter fun i : Fin 24 => generatedEighthDodecadWord.val i ≠ 0).card = 12 := by
  simp_rw [generatedEighth_dodecad_coordinate]
  decide +kernel

/-- The actual distinguished coordinate lies outside the dodecad. -/
theorem generatedEighth_dodecad_outside : generatedEighthDodecadWord.val 20 = 0 := by
  rw [generatedEighth_dodecad_coordinate]
  decide +kernel

/-- The orthogonal projection onto this genuine coordinate dodecad subspace. -/
def generatedEighthDodecadProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal fun i => if Nat.testBit 0xc5066f i.val then 1 else 0

/-- The orthogonal projection onto the distinguished coordinate line. -/
def generatedEighthCoordinateLineProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal fun i => if i = 20 then 1 else 0

/-- The dodecad coordinate projection is idempotent. -/
theorem generatedEighth_dodecad_projection_square :
    generatedEighthDodecadProjection * generatedEighthDodecadProjection =
      generatedEighthDodecadProjection := by
  unfold generatedEighthDodecadProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases Nat.testBit 0xc5066f i.val <;> simp

/-- The distinguished coordinate projection is idempotent. -/
theorem generatedEighth_coordinate_line_projection_square :
    generatedEighthCoordinateLineProjection * generatedEighthCoordinateLineProjection =
      generatedEighthCoordinateLineProjection := by
  unfold generatedEighthCoordinateLineProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = 20 <;> simp [hi]

/-- These two genuine coordinate subspaces are orthogonal. -/
theorem generatedEighth_dodecad_coordinate_line_mul :
    generatedEighthDodecadProjection * generatedEighthCoordinateLineProjection = 0 ∧
      generatedEighthCoordinateLineProjection * generatedEighthDodecadProjection = 0 := by
  have h20 : Nat.testBit 0xc5066f 20 = false := by decide
  constructor
  all_goals
    unfold generatedEighthDodecadProjection generatedEighthCoordinateLineProjection
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_zero]
    funext i
    by_cases hi : i = 20
    · subst i
      simp [h20]
    · simp [hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
