/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowDescriptorData

/-! Finite source and target integral vectors reuse the checked original pair and octad
catalogues. These equalities remove sorted catalogue computations from the row certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original source integral vectors with the genuine preferred pair table already substituted. -/
def generatedNinthShortRowSourceIntegral : generatedNinthOriginalShortLabel → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i =>
      4 * (if i = (generatedNinthCoordinatePairData p).1 then 1 else 0) +
        (if s = 0 then -4 else 4) * (if i = (generatedNinthCoordinatePairData p).2 then 1 else 0)
  | Sum.inr r => generatedNinthOriginalShortIntegral (Sum.inr r)

/-- The finite source vector is exactly the original genuine integral vector. -/
theorem generatedNinth_short_row_source_integral_actual (a : generatedNinthOriginalShortLabel) :
    generatedNinthShortRowSourceIntegral a = generatedNinthOriginalShortIntegral a := by
  cases a with
  | inl a => simp only [generatedNinthShortRowSourceIntegral, generatedNinthOriginalShortIntegral,
      generatedNinth_coordinate_pair_actual]
  | inr a => rfl

/-- Scatter an octad sign using the checked increasing coordinate table of the actual catalogue. -/
def generatedNinthShortRowOctadSign (o : Fin 759) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedAxisGlobalOctadCoordinatesData o k).val else 0) ||| m) 0

/-- The finite scatter is the exact genuine preferred octad sign mask. -/
theorem generatedNinth_short_row_octad_sign_actual (o : Fin 759) (e : Fin 64) :
    generatedNinthShortRowOctadSign o e = griessOctadSignMask o e := by
  simp only [generatedNinthShortRowOctadSign, griessOctadSignMask,
    generatedAxisGlobalOctadCoordinatesData_actual]

/-- Finite actual preferred target vectors in the complete pair, octad and odd catalogues. -/
def generatedNinthShortRowTargetIntegral : GriessShortIndex → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i =>
      4 * (if i = (generatedNinthCoordinatePairData p).1 then 1 else 0) +
        (if s = 0 then -4 else 4) * (if i = (generatedNinthCoordinatePairData p).2 then 1 else 0)
  | Sum.inr (Sum.inl (o, e)) => fun i =>
      if (golayEncodedMask (generatedAxisGlobalOctadCodeData o).val).testBit i.val then
        if (generatedNinthShortRowOctadSign o e).testBit i.val then -2 else 2
      else 0
  | Sum.inr (Sum.inr r) => griessShortIntegral (Sum.inr (Sum.inr r))

/-- Every finite target vector is exactly its actual preferred integral short vector. -/
theorem generatedNinth_short_row_target_integral_actual (s : GriessShortIndex) :
    generatedNinthShortRowTargetIntegral s = griessShortIntegral s := by
  rcases s with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedNinthShortRowTargetIntegral, griessShortIntegral,
      generatedNinth_coordinate_pair_actual]
  · simp only [generatedNinthShortRowTargetIntegral, griessShortIntegral,
      generatedAxisGlobalOctadCodeData_actual, generatedNinth_short_row_octad_sign_actual]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
