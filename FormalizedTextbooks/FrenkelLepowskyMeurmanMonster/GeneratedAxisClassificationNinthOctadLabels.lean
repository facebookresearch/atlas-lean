/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadData

/-! Actual preferred catalogue bindings for the 264 inverse-pair octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual Golay octad having the displayed original code label. -/
noncomputable def generatedNinthInputOctad (j : Fin 264) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedNinthInputOctadCode j, generatedNinthInputOctadCode_mem j⟩

/-- The actual catalogue index retains the exact finite code label. -/
theorem generatedNinthInputOctad_label (j : Fin 264) :
    golayOctadLabel (generatedNinthInputOctad j) = generatedNinthInputOctadCode j := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨generatedNinthInputOctadCode j, generatedNinthInputOctadCode_mem j⟩)

set_option maxHeartbeats 8000000 in
-- Verify the 2112 displayed coordinates against their original octad masks and ordering.
/-- The displayed coordinates are the actual increasing octad catalogue coordinates. -/
theorem generatedNinth_input_octad_coordinates (j : Fin 264) (k : Fin 8) :
    golayOctadCoordinate (generatedNinthInputOctad j) k =
      generatedNinthInputOctadCoordinates j k := by
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedNinthInputOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedNinthInputOctad j))
  have hm : (golayEncodedMask (generatedNinthInputOctadCode j).val).testBit
      (generatedNinthInputOctadCoordinates j k).val = true := by
    have hc : ∀ j' : Fin 264, ∀ k' : Fin 8,
        (golayEncodedMask (generatedNinthInputOctadCode j').val).testBit
          (generatedNinthInputOctadCoordinates j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedNinthInputOctadCoordinates j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedNinthInputOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedNinthInputOctad j)).val)).sort.idxOf
        (generatedNinthInputOctadCoordinates j k) = k.val
    rw [generatedNinthInputOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedNinthInputOctadCode j).val)).sort =
        List.ofFn (generatedNinthInputOctadCoordinates j) := by
      have hsorted : ∀ j' : Fin 264,
          List.SortedLT (List.ofFn (generatedNinthInputOctadCoordinates j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedNinthInputOctadCode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 264, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedNinthInputOctadCode j').val) ↔
            i' ∈ List.ofFn (generatedNinthInputOctadCoordinates j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 264, ∀ k' : Fin 8,
        (List.ofFn (generatedNinthInputOctadCoordinates j')).idxOf
          (generatedNinthInputOctadCoordinates j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
