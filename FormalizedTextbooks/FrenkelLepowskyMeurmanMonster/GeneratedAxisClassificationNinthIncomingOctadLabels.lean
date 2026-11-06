/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingOctadData

/-! Actual preferred catalogue bindings for the 165 inverse odd-short octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual Golay octad having the displayed original code label. -/
noncomputable def generatedNinthIncomingOctad (j : Fin 165) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedNinthIncomingOctadCode j, generatedNinthIncomingOctadCode_mem j⟩

/-- The actual catalogue index retains the exact finite code label. -/
theorem generatedNinthIncomingOctad_label (j : Fin 165) :
    golayOctadLabel (generatedNinthIncomingOctad j) = generatedNinthIncomingOctadCode j := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨generatedNinthIncomingOctadCode j, generatedNinthIncomingOctadCode_mem j⟩)

set_option maxHeartbeats 8000000 in
-- Verify the 1320 displayed coordinates against their original octad masks and ordering.
/-- The displayed coordinates are the actual increasing octad catalogue coordinates. -/
theorem generatedNinth_incoming_octad_coordinates (j : Fin 165) (k : Fin 8) :
    golayOctadCoordinate (generatedNinthIncomingOctad j) k =
      generatedNinthIncomingOctadCoordinates j k := by
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedNinthIncomingOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedNinthIncomingOctad j))
  have hm : (golayEncodedMask (generatedNinthIncomingOctadCode j).val).testBit
      (generatedNinthIncomingOctadCoordinates j k).val = true := by
    have hc : ∀ j' : Fin 165, ∀ k' : Fin 8,
        (golayEncodedMask (generatedNinthIncomingOctadCode j').val).testBit
          (generatedNinthIncomingOctadCoordinates j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedNinthIncomingOctadCoordinates j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedNinthIncomingOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedNinthIncomingOctad j)).val)).sort.idxOf
        (generatedNinthIncomingOctadCoordinates j k) = k.val
    rw [generatedNinthIncomingOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedNinthIncomingOctadCode j).val)).sort =
        List.ofFn (generatedNinthIncomingOctadCoordinates j) := by
      have hsorted : ∀ j' : Fin 165,
          List.SortedLT (List.ofFn (generatedNinthIncomingOctadCoordinates j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedNinthIncomingOctadCode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 165, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedNinthIncomingOctadCode j').val) ↔
            i' ∈ List.ofFn (generatedNinthIncomingOctadCoordinates j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 165, ∀ k' : Fin 8,
        (List.ofFn (generatedNinthIncomingOctadCoordinates j')).idxOf
          (generatedNinthIncomingOctadCoordinates j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
