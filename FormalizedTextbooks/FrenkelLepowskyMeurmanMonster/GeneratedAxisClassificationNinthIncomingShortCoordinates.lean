/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingOctadComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortNumerator

/-! Actual source short coordinates include the additional incoming odd-column octads. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Previously bound source families together with the additional actual incoming octads. -/
abbrev generatedNinthIncomingShortLabel := generatedNinthInputShortLabel ⊕ (Fin 165 × Fin 64)

/-- Each source label identifies an original preferred short-catalogue entry. -/
noncomputable def generatedNinthIncomingShortIndex :
    generatedNinthIncomingShortLabel → GriessShortIndex
  | Sum.inl r => generatedNinthInputShortIndex r
  | Sum.inr (j, e) => Sum.inr (Sum.inl (generatedNinthIncomingOctad j, e))

/-- Scatter the original even sign mask over the new actual increasing octad coordinates. -/
def generatedNinthIncomingOctadSignMask (j : Fin 165) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedNinthIncomingOctadCoordinates j k).val else 0) ||| m) 0

/-- The scattered sign is the exact original preferred octad sign mask. -/
theorem generatedNinth_incoming_octad_sign_mask (j : Fin 165) (e : Fin 64) :
    generatedNinthIncomingOctadSignMask j e =
      griessOctadSignMask (generatedNinthIncomingOctad j) e := by
  simp only [generatedNinthIncomingOctadSignMask, griessOctadSignMask,
    generatedNinth_incoming_octad_coordinates]

/-- Exact preferred integral short vectors for both old and additional source families. -/
def generatedNinthIncomingShortIntegral : generatedNinthIncomingShortLabel → Fin 24 → ℤ
  | Sum.inl r => generatedNinthInputShortIntegral r
  | Sum.inr (j, e) => fun i =>
      if (golayEncodedMask (generatedNinthIncomingOctadCode j).val).testBit i.val then
        if (generatedNinthIncomingOctadSignMask j e).testBit i.val then -2 else 2
      else 0

/-- Every executable source vector is the actual preferred integral short vector. -/
theorem generatedNinthIncomingShortIntegral_actual (r : generatedNinthIncomingShortLabel) :
    generatedNinthIncomingShortIntegral r =
      griessShortIntegral (generatedNinthIncomingShortIndex r) := by
  rcases r with r | ⟨j, e⟩
  · exact generatedNinthInputShortIntegral_actual r
  · simp only [generatedNinthIncomingShortIntegral, generatedNinthIncomingShortIndex,
      griessShortIntegral, generatedNinthIncomingOctad_label,
      generatedNinth_incoming_octad_sign_mask]

/-- Sixteen times the original Fifth coefficient on every additional source family. -/
def generatedNinthIncomingShortNumerator : generatedNinthIncomingShortLabel → ℤ
  | Sum.inl r => generatedNinthInputShortNumerator r
  | Sum.inr (j, e) =>
      if h : (generatedNinthIncomingOctadComparison j).val < 56 then
        generatedFifthFinalOctadNumerator ⟨(generatedNinthIncomingOctadComparison j).val, h⟩ e
      else 0

/-- The source numerator includes the complete genuine Fifth short support and its zeros. -/
theorem generatedNinthIncomingShortNumerator_actual (r : generatedNinthIncomingShortLabel) :
    (griessConwayEncode generatedFifthAxis).2.1 (generatedNinthIncomingShortIndex r) =
      (generatedNinthIncomingShortNumerator r : ℝ) / 16 := by
  rcases r with r | ⟨j, e⟩
  · exact generatedNinthInputShortNumerator_actual r
  · simp only [generatedNinthIncomingShortIndex, generatedNinthIncomingShortNumerator]
    split
    · rename_i h
      rw [generatedNinth_incoming_octad_eq j h]
      exact generatedFifth_final_octad_numerator _ _
    · rename_i h
      rw [generatedNinth_incoming_octad_zero j e h]
      norm_num

/-- The original preferred Q lift retains its central coefficient one. -/
def generatedNinthIncomingShortQ (r : generatedNinthIncomingShortLabel) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedNinthIncomingShortIntegral r))), 1⟩

/-- Source coordinates identify the actual preferred lift, including its central phase. -/
theorem generatedNinthIncomingShortQ_actual (r : generatedNinthIncomingShortLabel) :
    generatedNinthIncomingShortQ r = griessShortQ (generatedNinthIncomingShortIndex r) := by
  rw [← monsterNortonShortQ_eq]
  unfold generatedNinthIncomingShortQ monsterNortonShortQ
  rw [generatedNinthIncomingShortIntegral_actual]

/-- The literal nine-factor Q image determines the full actual short phase. -/
theorem generatedNinth_incoming_short_phase (r : generatedNinthIncomingShortLabel) :
    localShortPhase generatedNinthLocalFiber (generatedNinthIncomingShortIndex r) =
      toAdd (generatedNinthQImage (generatedNinthIncomingShortQ r)).coeff := by
  unfold localShortPhase
  rw [← generatedNinthIncomingShortQ_actual, generatedNinthQImage_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
