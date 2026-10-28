/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPhysicalGeometry

/-! The actual secondary feasible orbit is the entire finite perpendicular signed-short catalogue.
Coverage uses original isometry preservation and equality of the two proved actual counts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original signed-short vectors over the full actual perpendicular physical catalogue. -/
def generatedFeasibleOrthogonalSignedShortAxes : Set GriessSpace :=
  Set.range (fun a : generatedFeasibleOrthogonalSignedShortLabels =>
    conwayShortAxis a.val.1 a.val.2)

/-- The catalogue contains 93,150 distinct actual Griess vectors. -/
theorem generatedFeasibleOrthogonalSignedShortAxes_card :
    Nat.card generatedFeasibleOrthogonalSignedShortAxes = 93150 := by
  let f := fun a : generatedFeasibleOrthogonalSignedShortLabels =>
    conwayShortAxis a.val.1 a.val.2
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact @generatedAxis_signed_injective a.val b.val he
  change Nat.card (Set.range f) = 93150
  rw [← Nat.card_congr (Equiv.ofInjective f hf)]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact generatedFeasibleOrthogonalSignedShortLabels_card

set_option maxRecDepth 10000 in
-- Elaborate the subtype of the complete 93,150-address finite physical catalogue.
/-- Every genuine secondary local-orbit vector has an actual perpendicular signed-short address. -/
theorem generatedFeasibleSecondaryLocalOrbit_subset_physical :
    generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ⊆
      generatedFeasibleOrthogonalSignedShortAxes := by
  rintro x ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hmem : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    rw [hf]
    exact h.property
  have hp := (localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp hmem
  let r := griessShortPermutation f.val.2 (Sum.inl (1, generatedFeasiblePhysicalRootPair))
  let c := localShortPhase f (Sum.inl (1, generatedFeasiblePhysicalRootPair)) + 1
  have hr : r ∈ generatedFeasibleOrthogonalShortLabels := by
    rw [generatedFeasibleOrthogonalShortLabels_mem]
    exact generatedFeasiblePhysicalRoot_image_orthogonal f.val.2 hp.1
  have haddr : (r, c) ∈ generatedFeasibleOrthogonalSignedShortLabels := by
    change (r, c) ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ
    exact Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩
  refine ⟨⟨(r, c), haddr⟩, ?_⟩
  change conwayShortAxis r c = rhoLocal h.val
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
  rw [generatedFeasibleSecondaryAxis_eq_short, ← hf]
  change conwayShortAxis r c = localGriessRepresentation f
    (conwayShortAxis (Sum.inl (1, generatedFeasiblePhysicalRootPair)) 1)
  exact (generatedAxis_localFiber_image f
    (Sum.inl (1, generatedFeasiblePhysicalRootPair)) 1).symm

/-- The genuine secondary feasible orbit covers every original perpendicular signed-short vector. -/
theorem generatedFeasibleSecondaryLocalOrbit_eq_physical :
    generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair =
      generatedFeasibleOrthogonalSignedShortAxes := by
  apply Set.Finite.eq_of_subset_of_card_le (Set.finite_range _)
    generatedFeasibleSecondaryLocalOrbit_subset_physical
  change Nat.card generatedFeasibleOrthogonalSignedShortAxes ≤
    Nat.card (generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair)
  rw [generatedFeasibleOrthogonalSignedShortAxes_card, generatedFeasibleSecondaryLocalOrbit_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
