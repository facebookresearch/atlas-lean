/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPhysicalCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPairReturnCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyTransition

/-! The actual secondary feasible vectors which return to the secondary orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
-- Elaboration retains the complete finite 93,150-address subtype.
/-- Membership of an original signed-short vector is exactly the physical root condition. -/
theorem generatedFeasibleOrthogonalSignedShortAxes_mem (r : GriessShortIndex) (c : ZMod 2) :
    conwayShortAxis r c ∈ generatedFeasibleOrthogonalSignedShortAxes ↔
      griessShortIntegral r 0 = griessShortIntegral r 1 := by
  rw [← generatedFeasibleOrthogonalShortLabels_mem]
  constructor
  · rintro ⟨a, ha⟩
    have he : a.val = (r, c) := @generatedAxis_signed_injective a.val (r, c) ha
    have hp : (r, c) ∈ generatedFeasibleOrthogonalSignedShortLabels := he ▸ a.property
    change (r, c) ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ at hp
    exact (Finset.mem_product.mp hp).1
  · intro hr
    have ha : (r, c) ∈ generatedFeasibleOrthogonalSignedShortLabels := by
      change (r, c) ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ
      exact Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩
    exact ⟨⟨(r, c), ha⟩, rfl⟩

/-- Every physical catalogue vector is an actual original signed-short axis. -/
theorem generatedFeasibleOrthogonalSignedShortAxes_subset_signed :
    generatedFeasibleOrthogonalSignedShortAxes ⊆ generatedSignedShortAxes := by
  rintro x ⟨a, rfl⟩
  exact ⟨a.val, rfl⟩

/-- Actual vectors over the proved 925 original secondary-return pair addresses. -/
def generatedFeasibleSecondaryPairReturnAxes : Set GriessSpace :=
  Set.range (fun a : generatedFeasibleSecondaryPairReturnLabels =>
    conwayShortAxis (Sum.inl (a.val.1, a.val.2.1)) a.val.2.2)

/-- The 925 actual addresses represent 925 distinct original Griess vectors. -/
theorem generatedFeasibleSecondaryPairReturnAxes_card :
    Nat.card generatedFeasibleSecondaryPairReturnAxes = 925 := by
  let f := fun a : generatedFeasibleSecondaryPairReturnLabels =>
    conwayShortAxis (Sum.inl (a.val.1, a.val.2.1)) a.val.2.2
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have hfull := @generatedAxis_signed_injective
      (Sum.inl (a.val.1, a.val.2.1), a.val.2.2)
      (Sum.inl (b.val.1, b.val.2.1), b.val.2.2) he
    have hpair := Sum.inl.inj (congrArg Prod.fst hfull)
    have hs : a.val.1 = b.val.1 := congrArg (fun z : Fin 2 × Fin 276 => z.1) hpair
    have hp : a.val.2.1 = b.val.2.1 := congrArg (fun z : Fin 2 × Fin 276 => z.2) hpair
    have hc : a.val.2.2 = b.val.2.2 :=
      congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hfull
    exact Prod.ext hs (Prod.ext hp hc)
  change Nat.card (Set.range f) = 925
  rw [← Nat.card_congr (Equiv.ofInjective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact generatedFeasibleSecondaryPairReturnLabels_card

set_option maxRecDepth 10000 in
-- Keep the finite physical catalogue opaque when constructing its range witnesses.
/-- Every actual secondary return is one of the proved pair-return addresses. -/
theorem generatedFeasibleSecondaryReturn_eq_pair_axes :
    {x : GriessSpace | x ∈ generatedFeasibleOrthogonalSignedShortAxes ∧
      sExtra x ∈ generatedFeasibleOrthogonalSignedShortAxes} =
      generatedFeasibleSecondaryPairReturnAxes := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hτ⟩
    obtain ⟨s, p, hp⟩ := (generatedAxis_triality_first_return_iff a.val.1 a.val.2).mp
      (generatedFeasibleOrthogonalSignedShortAxes_subset_signed hτ)
    have hx := (generatedFeasibleOrthogonalSignedShortAxes_mem a.val.1 a.val.2).mp
      (show conwayShortAxis a.val.1 a.val.2 ∈ generatedFeasibleOrthogonalSignedShortAxes from
        ⟨a, rfl⟩)
    change sExtra (conwayShortAxis a.val.1 a.val.2) ∈
      generatedFeasibleOrthogonalSignedShortAxes at hτ
    rw [hp] at hx hτ
    rw [generatedAxis_triality_pair_exact] at hτ
    have hy := (generatedFeasibleOrthogonalSignedShortAxes_mem _ _).mp hτ
    have ha : (s, p, a.val.2) ∈ generatedFeasibleSecondaryPairReturnLabels := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (generatedFeasiblePairOrthogonal_iff s p).mpr hx
      · exact (generatedFeasiblePairOrthogonal_iff _ p).mpr hy
    refine ⟨⟨(s, p, a.val.2), ha⟩, ?_⟩
    change conwayShortAxis (Sum.inl (s, p)) a.val.2 = conwayShortAxis a.val.1 a.val.2
    rw [hp]
  · rintro ⟨a, rfl⟩
    change conwayShortAxis (Sum.inl (a.val.1, a.val.2.1)) a.val.2.2 ∈
      generatedFeasibleOrthogonalSignedShortAxes ∧
        sExtra (conwayShortAxis (Sum.inl (a.val.1, a.val.2.1)) a.val.2.2) ∈
          generatedFeasibleOrthogonalSignedShortAxes
    have h := (Finset.mem_filter.mp a.property).2
    constructor
    · apply (generatedFeasibleOrthogonalSignedShortAxes_mem _ _).mpr
      exact (generatedFeasiblePairOrthogonal_iff _ _).mp h.1
    · rw [generatedAxis_triality_pair_exact]
      apply (generatedFeasibleOrthogonalSignedShortAxes_mem _ _).mpr
      exact (generatedFeasiblePairOrthogonal_iff _ _).mp h.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
