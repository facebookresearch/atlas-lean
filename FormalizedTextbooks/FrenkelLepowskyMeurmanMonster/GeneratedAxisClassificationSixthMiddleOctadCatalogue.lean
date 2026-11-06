/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadData

/-! Binding original codewords and ordered octad coordinates to the genuine catalogue.
The ordered-coordinate bridge follows the frozen FifthEvenRootLabels formulation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual catalogue index retains the exact finite code label. -/
theorem generatedSixthMiddleOctad_label (j : Fin 273) :
    golayOctadLabel (generatedSixthMiddleOctad j) = generatedSixthMiddleOctadCode j := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨generatedSixthMiddleOctadCode j, generatedSixth_middle_octad_code_mem j⟩)

set_option maxHeartbeats 2000000 in
-- Verify the 2184 displayed coordinates against their original octad masks and ordering.
/-- The displayed coordinates are the actual increasing octad catalogue coordinates. -/
theorem generatedSixth_middle_octad_coordinates_certificate (j : Fin 273) (k : Fin 8) :
    golayOctadCoordinate (generatedSixthMiddleOctad j) k =
      generatedSixthMiddleOctadCoordinates j k := by
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedSixthMiddleOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedSixthMiddleOctad j))
  have hm : (golayEncodedMask (generatedSixthMiddleOctadCode j).val).testBit
      (generatedSixthMiddleOctadCoordinates j k).val = true := by
    have hc : ∀ j' : Fin 273, ∀ k' : Fin 8,
        (golayEncodedMask (generatedSixthMiddleOctadCode j').val).testBit
          (generatedSixthMiddleOctadCoordinates j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedSixthMiddleOctadCoordinates j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedSixthMiddleOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedSixthMiddleOctad j)).val)).sort.idxOf
        (generatedSixthMiddleOctadCoordinates j k) = k.val
    rw [generatedSixthMiddleOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedSixthMiddleOctadCode j).val)).sort =
        List.ofFn (generatedSixthMiddleOctadCoordinates j) := by
      have hsorted : ∀ j' : Fin 273,
          List.SortedLT (List.ofFn (generatedSixthMiddleOctadCoordinates j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedSixthMiddleOctadCode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 273, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedSixthMiddleOctadCode j').val) ↔
            i' ∈ List.ofFn (generatedSixthMiddleOctadCoordinates j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 273, ∀ k' : Fin 8,
        (List.ofFn (generatedSixthMiddleOctadCoordinates j')).idxOf
          (generatedSixthMiddleOctadCoordinates j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The finite physical sign mask is the genuine preferred octad sign mask. -/
theorem generatedSixth_middle_octad_sign_mask (j : Fin 273) :
    griessOctadSignMask (generatedSixthMiddleOctad j) (generatedSixthMiddleOctadSign j) =
      generatedSixthMiddleOctadSignMask j := by
  simp only [griessOctadSignMask, generatedSixth_middle_octad_coordinates_certificate,
    generatedSixthMiddleOctadSignMask]

/-- Every displayed output integral vector is the actual preferred short vector. -/
theorem generatedSixthMiddleOctadOutput_integral (j : Fin 273) :
    griessShortIntegral (generatedSixthMiddleOctadOutput j) =
      generatedSixthMiddleOctadIntegral j := by
  unfold generatedSixthMiddleOctadIntegral
  simp only [generatedSixthMiddleOctadOutput, generatedSixthMiddleOctadTargetCoordinates,
    griessShortIntegral,
    generatedSixthMiddleOctad_label, generatedSixth_middle_octad_sign_mask]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
