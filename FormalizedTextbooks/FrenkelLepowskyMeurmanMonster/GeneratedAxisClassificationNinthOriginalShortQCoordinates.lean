/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootLabels

/-! Finite actual preferred-Q coordinates for the complete original short source catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Scatter any original six-bit sign label over its genuine eight octad coordinates. -/
def generatedNinthOriginalOctadSignMask (j : Fin 56) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFifthEvenRootCoordinates j k).val else 0) ||| m) 0

/-- Original signed integer vectors in the checked physical coordinates of each source family. -/
def generatedNinthOriginalShortIntegral : generatedNinthOriginalShortLabel → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i =>
      4 * (if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if s = 0 then -4 else 4) * (if i = (griessCoordinatePair p).2 then 1 else 0)
  | Sum.inr (j, e) => fun i =>
      if (golayEncodedMask (generatedFifthEvenRootCode j).val).testBit i.val then
        if (generatedNinthOriginalOctadSignMask j e).testBit i.val then -2 else 2
      else 0

/-- Every displayed source vector is the actual preferred integral short vector. -/
theorem generatedNinth_original_short_integral_actual (a : generatedNinthOriginalShortLabel) :
    generatedNinthOriginalShortIntegral a =
      griessShortIntegral (generatedNinthOriginalShortIndex a) := by
  rcases a with ⟨s, p⟩ | ⟨j, e⟩
  · rfl
  · simp only [generatedNinthOriginalShortIntegral, generatedNinthOriginalShortIndex,
      griessShortIntegral, griessOctadSignMask, generatedFifthEvenRootOctad_label,
      generatedFifth_even_coordinates_certificate, generatedNinthOriginalOctadSignMask]

/-- The original preferred lift computed using the actual denominator-eight Leech inverse. -/
def generatedNinthOriginalShortQ (a : generatedNinthOriginalShortLabel) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedNinthOriginalShortIntegral a))), 1⟩

/-- Each finite source label is the intrinsic preferred short lift, with coefficient zero. -/
theorem generatedNinth_original_short_Q_actual (a : generatedNinthOriginalShortLabel) :
    generatedNinthOriginalShortQ a = griessShortQ (generatedNinthOriginalShortIndex a) := by
  rw [← monsterNortonShortQ_eq]
  unfold generatedNinthOriginalShortQ monsterNortonShortQ
  rw [generatedNinth_original_short_integral_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
