/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenRootData

/-! Actual preferred catalogue bindings for the 63 finite octad image certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual Golay octad having the displayed original code label. -/
noncomputable def generatedFourthEvenRootOctad (j : Fin 63) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedFourthEvenRootCode j, generatedFourthEvenRootCode_mem j⟩

/-- The actual catalogue index retains the exact finite code label. -/
theorem generatedFourthEvenRootOctad_label (j : Fin 63) :
    golayOctadLabel (generatedFourthEvenRootOctad j) = generatedFourthEvenRootCode j := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨generatedFourthEvenRootCode j, generatedFourthEvenRootCode_mem j⟩)

set_option maxHeartbeats 2000000 in
-- Verify the 504 displayed coordinates against their original octad masks and ordering.
/-- The displayed coordinates are the actual increasing octad catalogue coordinates. -/
theorem generatedFourth_even_coordinates_certificate (j : Fin 63) (k : Fin 8) :
    golayOctadCoordinate (generatedFourthEvenRootOctad j) k =
      generatedFourthEvenRootCoordinates j k := by
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedFourthEvenRootOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedFourthEvenRootOctad j))
  have hm : (golayEncodedMask (generatedFourthEvenRootCode j).val).testBit
      (generatedFourthEvenRootCoordinates j k).val = true := by
    have hc : ∀ j' : Fin 63, ∀ k' : Fin 8,
        (golayEncodedMask (generatedFourthEvenRootCode j').val).testBit
          (generatedFourthEvenRootCoordinates j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedFourthEvenRootCoordinates j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedFourthEvenRootOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedFourthEvenRootOctad j)).val)).sort.idxOf
        (generatedFourthEvenRootCoordinates j k) = k.val
    rw [generatedFourthEvenRootOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedFourthEvenRootCode j).val)).sort =
        List.ofFn (generatedFourthEvenRootCoordinates j) := by
      have hsorted : ∀ j' : Fin 63,
          List.SortedLT (List.ofFn (generatedFourthEvenRootCoordinates j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedFourthEvenRootCode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 63, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedFourthEvenRootCode j').val) ↔
            i' ∈ List.ofFn (generatedFourthEvenRootCoordinates j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 63, ∀ k' : Fin 8,
        (List.ofFn (generatedFourthEvenRootCoordinates j')).idxOf
          (generatedFourthEvenRootCoordinates j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The finite physical sign mask is the genuine preferred octad sign mask. -/
theorem generatedFourth_even_root_sign_mask (j : Fin 63) :
    griessOctadSignMask (generatedFourthEvenRootOctad j) (generatedFourthEvenRootSign j) =
      generatedFourthEvenRootSignMask j := by
  simp only [griessOctadSignMask, generatedFourth_even_coordinates_certificate,
    generatedFourthEvenRootSignMask]

/-- Genuine preferred octad output labels in the actual short catalogue. -/
noncomputable def generatedFourthEvenRootOutputLabel (j : Fin 63) : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, generatedFourthEvenRootSign j))

/-- Every displayed output integral vector is the actual preferred short vector. -/
theorem generatedFourthEvenRootOutputLabel_integral (j : Fin 63) :
    griessShortIntegral (generatedFourthEvenRootOutputLabel j) =
      generatedFourthEvenRootIntegral j := by
  unfold generatedFourthEvenRootIntegral
  simp only [generatedFourthEvenRootOutputLabel, griessShortIntegral,
    generatedFourthEvenRootOctad_label, generatedFourth_even_root_sign_mask]

/-- The recorded pair coordinates are genuinely increasing. -/
theorem generatedFourthEvenRootInputData_lt (j : Fin 63) :
    match generatedFourthEvenRootInputData j with
    | Sum.inl (_, a, b) => a < b
    | Sum.inr _ => True := by
  have ho := generatedFourthEvenRootInput_ordered j
  cases h : generatedFourthEvenRootInputData j with
  | inl z =>
    rcases z with ⟨s, a, b⟩
    simpa only [h, decide_eq_true_eq] using ho
  | inr e => trivial

/-- Genuine preferred input labels for the 63 checked octad outputs. -/
noncomputable def generatedFourthEvenRootInputLabel (j : Fin 63) : GriessShortIndex :=
  match h : generatedFourthEvenRootInputData j with
  | Sum.inl (s, a, b) => Sum.inl (s, griessPairIndex a b (by
      have hl := generatedFourthEvenRootInputData_lt j
      rw [h] at hl
      exact ne_of_lt hl))
  | Sum.inr e => Sum.inr (Sum.inl (generatedFourthOctad, e))

/-- Every input certificate is the genuine preferred physical input vector. -/
theorem generatedFourthEvenRootInputLabel_integral (j : Fin 63) :
    griessShortIntegral (generatedFourthEvenRootInputLabel j) =
      generatedFourthInputIntegral (generatedFourthEvenRootInputData j) := by
  have hl := generatedFourthEvenRootInputData_lt j
  unfold generatedFourthEvenRootInputLabel
  split <;> simp_all [griessShortIntegral, generatedFourthInputIntegral,
    griessPairIndex_coordinates, generatedFourthOctad_mask, generatedFourth_root_sign_mask]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
