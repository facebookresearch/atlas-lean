/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ComplementSign

/-! A complete small binary restriction certificate for the actual E7 octad and outside line. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Matrix

/-- The eight actual octad coordinates followed by the six nonzero outside-line coordinates. -/
def generatedTenthE7RestrictionCoordinates : Fin 14 → Fin 24 :=
  ![5, 6, 12, 15, 16, 17, 21, 23, 4, 7, 8, 11, 18, 20]

/-- The original twelve Golay generators restricted to those fourteen actual coordinates. -/
def generatedTenthE7RestrictionMatrix : Matrix (Fin 14) (Fin 12) (ZMod 2) :=
  fun i j => (golayGeneratorBit j (generatedTenthE7RestrictionCoordinates i) : ZMod 2)

/-- A complete binary left inverse, checked against the original Golay generators. -/
def generatedTenthE7RestrictionInverse : Matrix (Fin 12) (Fin 14) (ZMod 2) :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0]]

/-- The fourteen actual coordinates determine every original Golay codeword. -/
theorem generatedTenth_e7_restriction_inverse :
    generatedTenthE7RestrictionInverse * generatedTenthE7RestrictionMatrix = 1 := by
  decide +kernel

/-- Restriction uses the original Golay encoder, with no alternate code convention. -/
theorem generatedTenth_e7_restriction_encoder (a : Fin 12 → ZMod 2) :
    generatedTenthE7RestrictionMatrix *ᵥ a =
      fun i => golayEncoder a (generatedTenthE7RestrictionCoordinates i) := by
  ext i
  change (∑ j, (golayGeneratorBit j (generatedTenthE7RestrictionCoordinates i) : ZMod 2) * a j) =
    ∑ j, a j * (golayGeneratorBit j (generatedTenthE7RestrictionCoordinates i) : ZMod 2)
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- An actual Golay codeword vanishing on these fourteen coordinates is zero. -/
theorem generatedTenth_e7_code_zero_of_restriction (c : golayCode)
    (hc : ∀ i : Fin 14, c.val (generatedTenthE7RestrictionCoordinates i) = 0) : c = 0 := by
  obtain ⟨a, ha⟩ := c.property
  have hz : generatedTenthE7RestrictionMatrix *ᵥ a = 0 := by
    rw [generatedTenth_e7_restriction_encoder, ha]
    exact funext hc
  have h := congrArg (generatedTenthE7RestrictionInverse *ᵥ ·) hz
  rw [Matrix.mulVec_mulVec, generatedTenth_e7_restriction_inverse,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  apply Subtype.ext
  change c.val = 0
  rw [← ha, h, map_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
