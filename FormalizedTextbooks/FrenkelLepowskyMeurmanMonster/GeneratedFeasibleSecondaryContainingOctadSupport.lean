/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOddOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadSigns

/-! Actual containing-pair octad normalization by the original five-point Golay action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original encoder label 2063 is an actual octad. -/
theorem generatedFeasibleContainingOctad_standard_mem : (2063 : Fin 4096) ∈ golayOctads := by
  decide +kernel

/-- The original dictionary index of the actual first-eight-coordinate octad. -/
def generatedFeasibleContainingOctadPrototypeIndex : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨2063, generatedFeasibleContainingOctad_standard_mem⟩

/-- The prototype is bound to the original encoder label 2063. -/
theorem generatedFeasibleContainingOctadPrototypeIndex_label :
    golayOctadLabel generatedFeasibleContainingOctadPrototypeIndex = 2063 :=
  congrArg Subtype.val
    ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨2063, generatedFeasibleContainingOctad_standard_mem⟩)

/-- The original positive signed standard octad preferred label. -/
def generatedFeasibleContainingOctadPrototypeLabel : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))

private theorem zero_octad_sign_mask (o : Fin 759) : griessOctadSignMask o 0 = 0 := by
  have he : trialityEvenMask 0 = 0 := by decide +kernel
  unfold griessOctadSignMask
  rw [he]
  have hf (xs : List (Fin 8)) : xs.foldr (fun k m =>
      (if (0 : ℕ).testBit k.val then 2 ^ (golayOctadCoordinate o k).val else 0) ||| m) 0 = 0 := by
    induction xs with
    | nil => rfl
    | cons k xs _ih => simp [List.foldr_cons]
  exact hf _

/-- The prototype represents the actual integral vector twice the standard octad support. -/
theorem generatedFeasibleContainingOctadPrototype_integral (i : Fin 24) :
    griessShortIntegral generatedFeasibleContainingOctadPrototypeLabel i =
      if i.val < 8 then 2 else 0 := by
  have hm : golayEncodedMask 2063 = 255 := by decide +kernel
  have hb : ∀ j : Fin 24, (255 : ℕ).testBit j.val = decide (j.val < 8) := by
    decide +kernel
  simp only [generatedFeasibleContainingOctadPrototypeLabel, griessShortIntegral,
    generatedFeasibleContainingOctadPrototypeIndex_label, zero_octad_sign_mask,
    Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  change (if (golayEncodedMask 2063).testBit i.val then (2 : ℤ) else 0) = _
  rw [hm, hb]
  simp

/-- The prototype lies in the actual containing-pair physical sector. -/
theorem generatedFeasibleContainingOctadPrototypeLabel_mem :
    generatedFeasibleContainingOctadPrototypeLabel ∈ generatedFeasibleSecondaryNonPairLabels 0 := by
  have ho : generatedFeasibleContainingOctadPrototypeIndex ∈
      generatedFeasibleOctadContainingLabels := by
    have hm : golayEncodedMask 2063 = 255 := by decide +kernel
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [generatedFeasibleContainingOctadPrototypeIndex_label]
    change (golayEncodedMask 2063).testBit 0 = true ∧
      (golayEncodedMask 2063).testBit 1 = true
    rw [hm]
    decide +kernel
  change _ ∈ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadContainingLabels).map _
  refine Finset.mem_map.mpr ⟨(generatedFeasibleContainingOctadPrototypeIndex, 0), ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho, ?_⟩
  change griessShortIntegral generatedFeasibleContainingOctadPrototypeLabel 0 =
    griessShortIntegral generatedFeasibleContainingOctadPrototypeLabel 1
  rw [generatedFeasibleContainingOctadPrototype_integral,
    generatedFeasibleContainingOctadPrototype_integral]
  rfl

/-- Actual encoder words of the original octad catalogue. -/
def generatedFeasibleOctadCode (o : Fin 759) : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients (golayOctadLabel o)), ⟨_, rfl⟩⟩

/-- Original octad masks and actual encoder coordinates describe the same support. -/
theorem generatedFeasibleOctadCode_support (o : Fin 759) (i : Fin 24) :
    (generatedFeasibleOctadCode o).val i = 1 ↔
      i ∈ golayMaskSupport (golayEncodedMask (golayOctadLabel o).val) := by
  simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  change golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i = 1 ↔ _
  rw [← (ZMod.val_injective 2).eq_iff, golayLabelEncoder_match]
  cases (golayEncodedMask (golayOctadLabel o).val).testBit i.val <;> decide

/-- Every original containing-pair octad can be sent to the standard octad while
fixing both ordered root coordinates, using genuine five-transitivity and octad uniqueness. -/
theorem generatedFeasibleContainingOctad_to_standard (o : Fin 759)
    (ho : o ∈ generatedFeasibleOctadContainingLabels) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧ p.val 1 = 1 ∧
      golayPermute p.val (generatedFeasibleOctadCode o).val = golayStandardOctad := by
  let s := golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)
  have h0 : (0 : Fin 24) ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ho).2.1⟩
  have h1 : (1 : Fin 24) ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ho).2.2⟩
  let t := (s.erase 0).erase 1
  have ht : t.card = 6 := by
    have h1' : (1 : Fin 24) ∈ s.erase 0 := Finset.mem_erase.mpr ⟨by decide, h1⟩
    rw [Finset.card_erase_of_mem h1', Finset.card_erase_of_mem h0]
    change (golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)).card - 1 - 1 = 6
    rw [golayOctad_support_card]
  have hn : Nonempty (Fin 3 ↪ t) :=
    Function.Embedding.nonempty_of_card_le (by simp [Fintype.card_coe, ht])
  let e : Fin 3 ↪ t := Classical.choice hn
  let f : Fin 3 → Fin 24 := fun j => (e j).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hf0 : (0 : Fin 24) ∉ Set.range f := by
    rintro ⟨j, hj⟩
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp (e j).property).2).1 hj
  have hf1 : (1 : Fin 24) ∉ Set.range f := by
    rintro ⟨j, hj⟩
    exact (Finset.mem_erase.mp (e j).property).1 hj
  let a : Fin 5 → Fin 24 := Fin.cons 0 (Fin.cons 1 f)
  have ha : Function.Injective a := by
    apply Fin.cons_injective_of_injective
    · rintro ⟨j, hj⟩
      cases j using Fin.cases with
      | zero => simp at hj
      | succ k => exact hf0 ⟨k, hj⟩
    · exact Fin.cons_injective_of_injective hf1 hf
  let b : Fin 5 → Fin 24 := fun j => Fin.castAdd 19 j
  have hb : Function.Injective b := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive a b ha hb
  have hw : ∑ i, ((generatedFeasibleOctadCode o).val i).val = 8 := by
    simp only [generatedFeasibleOctadCode]
    simp_rw [golayLabelEncoder_match]
    exact (golayMaskSupport_card _).symm.trans (golayOctad_support_card o)
  have hs (j : Fin 5) : (generatedFeasibleOctadCode o).val (a j) = 1 := by
    rw [generatedFeasibleOctadCode_support]
    refine Fin.cases h0 (fun k => Fin.cases h1 (fun l => ?_) k) j
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp (e l).property).2).2
  refine ⟨p, hp 0, hp 1, ?_⟩
  apply golayOctad_unique_through_first_five _ _
    ((p.property _).mp (generatedFeasibleOctadCode o).property) golayStandardOctad_mem
    ((Equiv.sum_comp p.val.symm (fun i => ((generatedFeasibleOctadCode o).val i).val)).trans hw)
    golayStandardOctad_weight
  intro i hi
  let j : Fin 5 := ⟨i.val, hi⟩
  have hbi : b j = i := Fin.ext rfl
  have hpi : p.val.symm i = a j := by rw [← hbi, ← hp j, p.val.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · change (generatedFeasibleOctadCode o).val (p.val.symm i) = 1
    rw [hpi]
    exact hs j
  · simp [golayStandardOctad, show i.val < 8 by omega]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
