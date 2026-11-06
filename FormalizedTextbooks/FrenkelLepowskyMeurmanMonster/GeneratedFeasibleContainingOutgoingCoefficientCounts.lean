/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedShortCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingFrameShortProjection

/-! Actual containing transition input fibers, measured by their original first coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original first coefficient descends through the entire genuine first-axis action. -/
def generatedFeasibleContainingAClassFirst :
    generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair → ℝ :=
  Quotient.lift (fun x => (griessConwayEncode x).2.1
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))) (by
      intro x y hrel
      obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.mp hrel
      have hi := generatedFeasibleContaining_first_coordinate_invariant
        generatedFeasiblePhysicalRootPair h y
      change rhoLocal h.val y = x at hh
      rwa [hh] at hi)

/-- First coefficient of the actual triality destination of an original containing input coset.
-/
def generatedFeasibleContainingInputFirst
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) : ℝ :=
  generatedFeasibleContainingAClassFirst
    (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c)

/-- Every coset representative evaluates the original whole-word vector followed by triality.
-/
theorem generatedFeasibleContainingInputFirst_apply
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    generatedFeasibleContainingInputFirst
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) =
        (griessConwayEncode (sExtra
          (rhoLocal h.val generatedFeasibleContainingOctadDestination))).2.1
            (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := rfl

/-- Noncoordinate input fibers for the three actual outgoing first coefficients. -/
def generatedFeasibleContainingOutgoingCoefficientInputs (k : Fin 3) :
    Set (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :=
  {c | c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
    generatedFeasibleContainingInputFirst c = (![(0 : ℝ), 1 / 8, 1 / 4] : Fin 3 → ℝ) k}

/-- On every genuine noncoordinate input word, the first coefficient is its selected short
square divided by sixty-four. -/
theorem generatedFeasibleContainingInputFirst_word_square
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hm : (griessConwayEncode (rhoLocal h.val generatedFeasibleContainingOctadDestination)).2.1
      generatedFeasibleMateLabel = 0) :
    generatedFeasibleContainingInputFirst
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) =
          (generatedFeasibleContainingSelectedShortSquare
            (generatedFeasibleContainingInverseSecondaryAddresses
              (Quotient.mk (QuotientGroup.rightRel
                (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 :
                  ℝ) /
                  64 := by
  have hx : rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination := ⟨h, rfl⟩
  have hr := generatedFeasibleContaining_first_diagonal_relation _ hx
  have hd := generatedFeasibleContaining_whole_word_diagonal h
  have ht := generatedFeasibleContaining_noncoordinate_triality_first _ ⟨hx, hm⟩
  rw [generatedFeasibleContainingInputFirst_apply, ht]
  linarith

private theorem coefficient_square_iff (n : ℤ) (k : Fin 3) :
    (n ≠ 32 ∧ (n : ℝ) / 64 = (![(0 : ℝ), 1 / 8, 1 / 4] : Fin 3 → ℝ) k) ↔
      n = (![(0 : ℤ), 8, 16] : Fin 3 → ℤ) k := by
  fin_cases k
  · change (n ≠ 32 ∧ (n : ℝ) / 64 = 0) ↔ n = 0
    constructor
    · intro h
      have hh : (n : ℝ) = 0 := by linarith [h.2]
      exact_mod_cast hh
    · intro h
      rw [h]
      norm_num
  · change (n ≠ 32 ∧ (n : ℝ) / 64 = 1 / 8) ↔ n = 8
    constructor
    · intro h
      have hh : (n : ℝ) = 8 := by linarith [h.2]
      exact_mod_cast hh
    · intro h
      rw [h]
      norm_num
  · change (n ≠ 32 ∧ (n : ℝ) / 64 = 1 / 4) ↔ n = 16
    constructor
    · intro h
      have hh : (n : ℝ) = 16 := by linarith [h.2]
      exact_mod_cast hh
    · intro h
      rw [h]
      norm_num

/-- The actual coefficient fiber of every original coset representative has its exact short bin.
-/
theorem generatedFeasibleContainingOutgoingCoefficientInputs_word_iff
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) (k : Fin 3) :
    Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h ∈
        generatedFeasibleContainingOutgoingCoefficientInputs k ↔
          generatedFeasibleContainingSelectedShortSquare
            (generatedFeasibleContainingInverseSecondaryAddresses
              (Quotient.mk (QuotientGroup.rightRel
                (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 =
                  (![(0 : ℤ), 8, 16] : Fin 3 → ℤ) k := by
  let c := Quotient.mk (QuotientGroup.rightRel
    (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h
  let n := generatedFeasibleContainingSelectedShortSquare
    (generatedFeasibleContainingInverseSecondaryAddresses c).val.1
  have hm := generatedFeasibleContaining_word_mate_zero_iff h
  change (griessConwayEncode (rhoLocal h.val generatedFeasibleContainingOctadDestination)).2.1
    generatedFeasibleMateLabel = 0 ↔ n ≠ 32 at hm
  constructor
  · rintro ⟨hc, hf⟩
    have hres := (generatedFeasibleContaining_noncoordinate_input_word_iff h).mp hc
    have hzero := hres.2
    have hs := generatedFeasibleContainingInputFirst_word_square h hzero
    rw [hs] at hf
    exact (coefficient_square_iff n k).mp ⟨hm.mp hzero, hf⟩
  · intro hn
    have hs := (coefficient_square_iff n k).mpr hn
    have hzero := hm.mpr hs.1
    refine ⟨(generatedFeasibleContaining_noncoordinate_input_word_iff h).mpr
      ⟨⟨h, rfl⟩, hzero⟩, ?_⟩
    rw [generatedFeasibleContainingInputFirst_word_square h hzero]
    exact hs.2

private theorem selected_short_value_castSucc (k : Fin 3) :
    generatedFeasibleContainingSelectedShortValues k.castSucc =
      (![(0 : ℤ), 8, 16] : Fin 3 → ℤ) k := by
  fin_cases k <;> rfl

private theorem selected_signed_mem_iff (a : generatedFeasibleOrthogonalSignedShortLabels)
    (k : Fin 4) :
    a.val ∈ generatedFeasibleContainingSelectedSignedShortLabels k ↔
      generatedFeasibleContainingSelectedShortSquare a.val.1 =
        generatedFeasibleContainingSelectedShortValues k := by
  have ha := a.property
  change a.val ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ at ha
  rw [Finset.mem_product] at ha
  simp only [generatedFeasibleContainingSelectedSignedShortLabels,
    generatedFeasibleContainingSelectedShortLabels, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, and_true]
  exact and_iff_right ha.1

/-- Every actual coefficient fiber is exactly the inverse image of its entire original signed bin.
-/
theorem generatedFeasibleContainingOutgoingCoefficientInputs_eq_preimage (k : Fin 3) :
    generatedFeasibleContainingOutgoingCoefficientInputs k =
      generatedFeasibleContainingInverseSecondaryAddresses ⁻¹'
        {a : generatedFeasibleOrthogonalSignedShortLabels |
          a.val ∈ generatedFeasibleContainingSelectedSignedShortLabels k.castSucc} := by
  ext c
  induction c using Quotient.inductionOn with
  | h h =>
    rw [generatedFeasibleContainingOutgoingCoefficientInputs_word_iff]
    change _ ↔ (generatedFeasibleContainingInverseSecondaryAddresses
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val ∈
          generatedFeasibleContainingSelectedSignedShortLabels k.castSucc
    rw [selected_signed_mem_iff, selected_short_value_castSucc]

private def preimage_equiv {α β : Type*} (e : α ≃ β) (s : Set β) : (e ⁻¹' s) ≃ s where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by
    change e (e.symm y.val) ∈ s
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

private def finset_subtype_equiv {α : Type*} (s t : Finset α) (ht : t ⊆ s) :
    {a : s // a.val ∈ t} ≃ t where
  toFun a := ⟨a.val.val, a.property⟩
  invFun b := ⟨⟨b.val, ht b.property⟩, b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem selected_signed_subset (k : Fin 4) :
    generatedFeasibleContainingSelectedSignedShortLabels k ⊆
      generatedFeasibleOrthogonalSignedShortLabels := by
  intro a ha
  rw [generatedFeasibleContainingSelectedSignedShortLabels, Finset.mem_product] at ha
  rw [generatedFeasibleOrthogonalSignedShortLabels, Finset.mem_product]
  exact ⟨(Finset.mem_filter.mp ha.1).1, ha.2⟩

/-- Exact whole input counts for coefficients zero, one eighth and one quarter in the actual
noncoordinate containing remainder. Class transitivity is a separate geometric obligation. -/
theorem generatedFeasibleContainingOutgoingCoefficientInputs_card (k : Fin 3) :
    Nat.card (generatedFeasibleContainingOutgoingCoefficientInputs k) =
      (![4320, 64512, 24192] : Fin 3 → ℕ) k := by
  rw [generatedFeasibleContainingOutgoingCoefficientInputs_eq_preimage]
  rw [Nat.card_congr (preimage_equiv generatedFeasibleContainingInverseSecondaryAddresses _)]
  have he := finset_subtype_equiv generatedFeasibleOrthogonalSignedShortLabels
    (generatedFeasibleContainingSelectedSignedShortLabels k.castSucc)
    (selected_signed_subset k.castSucc)
  change Nat.card {a : generatedFeasibleOrthogonalSignedShortLabels //
    a.val ∈ generatedFeasibleContainingSelectedSignedShortLabels k.castSucc} = _
  rw [Nat.card_congr he]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe,
    generatedFeasibleContainingSelectedSignedShortLabels_card]
  fin_cases k <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
