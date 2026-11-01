/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingOctadLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator

/-! Exact comparison with the fifty-six genuinely supported fifth-axis octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- A genuine original fifth-family index, or 56 when the octad is outside that support. -/
def generatedNinthIncomingOctadComparison : Fin 165 → Fin 57 :=
  ![56, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 5, 56, 56,
    56, 46, 38, 56, 56, 56, 56, 56, 56, 49, 30, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 11, 56,
    56, 56, 56, 56, 6, 56, 56, 56, 56, 56, 33, 41, 56, 56,
    56, 56, 56, 56, 54, 25, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56]

/-- The finite comparison preserves exact source code equality and support exclusion. -/
theorem generatedNinth_incoming_octad_comparison : ∀ j : Fin 165,
    if h : (generatedNinthIncomingOctadComparison j).val < 56 then
      generatedNinthIncomingOctadCode j =
        generatedFifthEvenRootCode ⟨(generatedNinthIncomingOctadComparison j).val, h⟩
    else ∀ k : Fin 56, generatedNinthIncomingOctadCode j ≠ generatedFifthEvenRootCode k := by
  decide +kernel

/-- Equal actual encoder labels identify the original supported octad catalogue entries. -/
theorem generatedNinth_incoming_octad_eq (j : Fin 165)
    (h : (generatedNinthIncomingOctadComparison j).val < 56) :
    generatedNinthIncomingOctad j =
      generatedFifthEvenRootOctad ⟨(generatedNinthIncomingOctadComparison j).val, h⟩ := by
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  apply Subtype.ext
  change golayOctadLabel _ = golayOctadLabel _
  rw [generatedNinthIncomingOctad_label, generatedFifthEvenRootOctad_label]
  simpa only [dite_eq_left h] using generatedNinth_incoming_octad_comparison j

/-- Every other original inverse odd-short octad is outside the genuine fifth short support. -/
theorem generatedNinth_incoming_octad_zero (j : Fin 165) (e : Fin 64)
    (h : ¬ (generatedNinthIncomingOctadComparison j).val < 56) :
    (griessConwayEncode generatedFifthAxis).2.1
      (Sum.inr (Sum.inl (generatedNinthIncomingOctad j, e))) = 0 := by
  apply generatedFifth_final_octad_zero
  rintro ⟨k, hk⟩
  have hc := congrArg golayOctadLabel hk
  rw [generatedFifthEvenRootOctad_label, generatedNinthIncomingOctad_label] at hc
  have hx := generatedNinth_incoming_octad_comparison j
  rw [dite_eq_right h] at hx
  exact hx k hc.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
