/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator

/-! Exact comparison with the fifty-six genuinely supported fifth-axis octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- A genuine original fifth-family index, or 56 when the octad is outside that support. -/
def generatedNinthInputOctadComparison : Fin 264 → Fin 57 :=
  ![56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 20, 14, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    8, 9, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 15, 21, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 3, 2, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56]

/-- The finite comparison preserves exact source code equality and support exclusion. -/
theorem generatedNinth_input_octad_comparison : ∀ j : Fin 264,
    if h : (generatedNinthInputOctadComparison j).val < 56 then
      generatedNinthInputOctadCode j =
        generatedFifthEvenRootCode ⟨(generatedNinthInputOctadComparison j).val, h⟩
    else ∀ k : Fin 56, generatedNinthInputOctadCode j ≠ generatedFifthEvenRootCode k := by
  decide +kernel

/-- Equal actual encoder labels identify the original supported octad catalogue entries. -/
theorem generatedNinth_input_octad_eq (j : Fin 264)
    (h : (generatedNinthInputOctadComparison j).val < 56) :
    generatedNinthInputOctad j =
      generatedFifthEvenRootOctad ⟨(generatedNinthInputOctadComparison j).val, h⟩ := by
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  apply Subtype.ext
  change golayOctadLabel _ = golayOctadLabel _
  rw [generatedNinthInputOctad_label, generatedFifthEvenRootOctad_label]
  simpa only [dite_eq_left h] using generatedNinth_input_octad_comparison j

/-- Every other original inverse octad is outside the genuine fifth short support. -/
theorem generatedNinth_input_octad_zero (j : Fin 264) (e : Fin 64)
    (h : ¬ (generatedNinthInputOctadComparison j).val < 56) :
    (griessConwayEncode generatedFifthAxis).2.1
      (Sum.inr (Sum.inl (generatedNinthInputOctad j, e))) = 0 := by
  apply generatedFifth_final_octad_zero
  rintro ⟨k, hk⟩
  have hc := congrArg golayOctadLabel hk
  rw [generatedFifthEvenRootOctad_label, generatedNinthInputOctad_label] at hc
  have hx := generatedNinth_input_octad_comparison j
  rw [dite_eq_right h] at hx
  exact hx k hc.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
