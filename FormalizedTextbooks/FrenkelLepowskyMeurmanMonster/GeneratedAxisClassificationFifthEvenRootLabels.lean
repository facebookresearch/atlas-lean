/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootData

/-! Actual preferred catalogue bindings for the 56 finite octad image certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual Golay octad having the displayed original code label. -/
noncomputable def generatedFifthEvenRootOctad (j : Fin 56) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedFifthEvenRootCode j, generatedFifthEvenRootCode_mem j⟩

/-- The actual catalogue index retains the exact finite code label. -/
theorem generatedFifthEvenRootOctad_label (j : Fin 56) :
    golayOctadLabel (generatedFifthEvenRootOctad j) = generatedFifthEvenRootCode j := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨generatedFifthEvenRootCode j, generatedFifthEvenRootCode_mem j⟩)

set_option maxHeartbeats 2000000 in
-- Verify the 504 displayed coordinates against their original octad masks and ordering.
/-- The displayed coordinates are the actual increasing octad catalogue coordinates. -/
theorem generatedFifth_even_coordinates_certificate (j : Fin 56) (k : Fin 8) :
    golayOctadCoordinate (generatedFifthEvenRootOctad j) k =
      generatedFifthEvenRootCoordinates j k := by
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedFifthEvenRootOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedFifthEvenRootOctad j))
  have hm : (golayEncodedMask (generatedFifthEvenRootCode j).val).testBit
      (generatedFifthEvenRootCoordinates j k).val = true := by
    have hc : ∀ j' : Fin 56, ∀ k' : Fin 8,
        (golayEncodedMask (generatedFifthEvenRootCode j').val).testBit
          (generatedFifthEvenRootCoordinates j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedFifthEvenRootCoordinates j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedFifthEvenRootOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedFifthEvenRootOctad j)).val)).sort.idxOf
        (generatedFifthEvenRootCoordinates j k) = k.val
    rw [generatedFifthEvenRootOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedFifthEvenRootCode j).val)).sort =
        List.ofFn (generatedFifthEvenRootCoordinates j) := by
      have hsorted : ∀ j' : Fin 56,
          List.SortedLT (List.ofFn (generatedFifthEvenRootCoordinates j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedFifthEvenRootCode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 56, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedFifthEvenRootCode j').val) ↔
            i' ∈ List.ofFn (generatedFifthEvenRootCoordinates j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 56, ∀ k' : Fin 8,
        (List.ofFn (generatedFifthEvenRootCoordinates j')).idxOf
          (generatedFifthEvenRootCoordinates j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The finite physical sign mask is the genuine preferred octad sign mask. -/
theorem generatedFifth_even_root_sign_mask (j : Fin 56) :
    griessOctadSignMask (generatedFifthEvenRootOctad j) (generatedFifthEvenRootSign j) =
      generatedFifthEvenRootSignMask j := by
  simp only [griessOctadSignMask, generatedFifth_even_coordinates_certificate,
    generatedFifthEvenRootSignMask]

/-- Genuine preferred octad output labels in the actual short catalogue. -/
noncomputable def generatedFifthEvenRootOutputLabel (j : Fin 56) : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, generatedFifthEvenRootSign j))

/-- Every displayed output integral vector is the actual preferred short vector. -/
theorem generatedFifthEvenRootOutputLabel_integral (j : Fin 56) :
    griessShortIntegral (generatedFifthEvenRootOutputLabel j) =
      generatedFifthEvenRootIntegral j := by
  unfold generatedFifthEvenRootIntegral
  simp only [generatedFifthEvenRootOutputLabel, griessShortIntegral,
    generatedFifthEvenRootOctad_label, generatedFifth_even_root_sign_mask]

/-- The recorded pair coordinates are genuinely increasing. -/
theorem generatedFifthEvenRootInputData_lt (j : Fin 56) :
    match generatedFifthEvenRootInputData j with
    | Sum.inl (_, a, b) => a < b
    | Sum.inr _ => True := by
  have ho := generatedFifthEvenRootInput_ordered j
  cases h : generatedFifthEvenRootInputData j with
  | inl z =>
    rcases z with ⟨s, a, b⟩
    simpa only [h, decide_eq_true_eq] using ho
  | inr e => trivial

/-- Genuine preferred input labels for the 56 checked octad outputs. -/
noncomputable def generatedFifthEvenRootInputLabel (j : Fin 56) : GriessShortIndex :=
  match h : generatedFifthEvenRootInputData j with
  | Sum.inl (s, a, b) => Sum.inl (s, griessPairIndex a b (by
      have hl := generatedFifthEvenRootInputData_lt j
      rw [h] at hl
      exact ne_of_lt hl))
  | Sum.inr e => Sum.inr (Sum.inl (generatedFourthOctad, e))

/-- Every input certificate is the genuine preferred physical input vector. -/
theorem generatedFifthEvenRootInputLabel_integral (j : Fin 56) :
    griessShortIntegral (generatedFifthEvenRootInputLabel j) =
      generatedFourthInputIntegral (generatedFifthEvenRootInputData j) := by
  have hl := generatedFifthEvenRootInputData_lt j
  unfold generatedFifthEvenRootInputLabel
  split <;> simp_all [griessShortIntegral, generatedFourthInputIntegral,
    griessPairIndex_coordinates, generatedFourthOctad_mask, generatedFourth_root_sign_mask]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
