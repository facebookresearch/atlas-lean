/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCoordinates

/-! Complete executable physical integer formulas for the original preferred short-vector catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The exact original octad sign mask, using its certified increasing coordinate catalogue. -/
def generatedAxisGlobalShortOctadSignMask (o : Fin 759) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedAxisGlobalOctadCoordinatesData o k).val else 0) ||| m) 0

/-- Every original octad sign coordinate is retained. -/
theorem generatedAxisGlobalShortOctadSignMask_actual (o : Fin 759) (e : Fin 64) :
    generatedAxisGlobalShortOctadSignMask o e = griessOctadSignMask o e := by
  simp only [generatedAxisGlobalShortOctadSignMask, griessOctadSignMask,
    generatedAxisGlobalOctadCoordinatesData_actual]

/-- All three physical integer families use the original pair, octad and odd labels. -/
def generatedAxisGlobalShortIntegral : GriessShortIndex → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i =>
      4 * (if i = (generatedAxisGlobalPairCoordinates p).1 then 1 else 0) +
        (if s = 0 then -4 else 4) *
          (if i = (generatedAxisGlobalPairCoordinates p).2 then 1 else 0)
  | Sum.inr (Sum.inl (o, e)) => fun i =>
      if (golayEncodedMask (generatedAxisGlobalOctadCodeData o).val).testBit i.val then
        if (generatedAxisGlobalShortOctadSignMask o e).testBit i.val then -2 else 2
      else 0
  | Sum.inr (Sum.inr (d, j)) => fun i =>
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (if i = j then -3 else 1)

/-- Every executable integer coordinate is exactly its genuine original preferred-short coordinate. -/
theorem generatedAxisGlobalShortIntegral_actual (r : GriessShortIndex) :
    generatedAxisGlobalShortIntegral r = griessShortIntegral r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · simp only [generatedAxisGlobalShortIntegral, griessShortIntegral,
      generatedAxisGlobalPairCoordinates_actual]
  · simp only [generatedAxisGlobalShortIntegral, griessShortIntegral,
      generatedAxisGlobalOctadCodeData_actual, generatedAxisGlobalShortOctadSignMask_actual]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
