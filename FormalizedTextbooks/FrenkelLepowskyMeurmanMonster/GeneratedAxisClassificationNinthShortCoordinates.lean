/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadLabels

/-! Finite physical short formulas retain the actual pair, octad and odd catalogue labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Ordered pairs, the two hundred sixty-four actual octads, and the original odd short family. -/
abbrev generatedNinthInputShortLabel :=
  (Fin 2 × {p : Fin 24 × Fin 24 // p.1 < p.2}) ⊕
    ((Fin 264 × Fin 64) ⊕ (Fin 2048 × Fin 24))

/-- The finite input cache embeds into the actual preferred-short catalogue. -/
noncomputable def generatedNinthInputShortIndex : generatedNinthInputShortLabel → GriessShortIndex
  | Sum.inl (s, p) => Sum.inl (s, griessPairIndex p.val.1 p.val.2 (ne_of_lt p.property))
  | Sum.inr (Sum.inl (j, e)) => Sum.inr (Sum.inl (generatedNinthInputOctad j, e))
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inr p)

/-- The original even sign mask scattered over the verified increasing octad coordinates. -/
def generatedNinthInputOctadSignMask (j : Fin 264) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedNinthInputOctadCoordinates j k).val else 0) ||| m) 0

/-- The finite mask is exactly the actual preferred octad sign mask. -/
theorem generatedNinth_input_octad_sign_mask (j : Fin 264) (e : Fin 64) :
    generatedNinthInputOctadSignMask j e = griessOctadSignMask (generatedNinthInputOctad j) e := by
  simp only [generatedNinthInputOctadSignMask, griessOctadSignMask,
    generatedNinth_input_octad_coordinates]

/-- Exact finite physical integers for every cached actual preferred-short vector. -/
def generatedNinthInputShortIntegral : generatedNinthInputShortLabel → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i => 4 * (if i = p.val.1 then 1 else 0) +
      (if s = 0 then -4 else 4) * (if i = p.val.2 then 1 else 0)
  | Sum.inr (Sum.inl (j, e)) => fun i =>
      if (golayEncodedMask (generatedNinthInputOctadCode j).val).testBit i.val then
        if (generatedNinthInputOctadSignMask j e).testBit i.val then -2 else 2
      else 0
  | Sum.inr (Sum.inr (d, j)) => fun i =>
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (if i = j then -3 else 1)

/-- The cache uses the genuine preferred short vectors in all three source families. -/
theorem generatedNinthInputShortIntegral_actual (r : generatedNinthInputShortLabel) :
    generatedNinthInputShortIntegral r = griessShortIntegral (generatedNinthInputShortIndex r) := by
  rcases r with ⟨s, p⟩ | (⟨j, e⟩ | ⟨d, i⟩)
  · simp only [generatedNinthInputShortIntegral, generatedNinthInputShortIndex,
      griessShortIntegral, griessPairIndex_coordinates, p.property, ite_true]
  · simp only [generatedNinthInputShortIntegral, generatedNinthInputShortIndex,
      griessShortIntegral, generatedNinthInputOctad_label, generatedNinth_input_octad_sign_mask]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
