/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryDisjointPairSupport

/-! The original924 signed disjoint coordinate-pair axes form one genuine simultaneous orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Every original disjoint-pair signed input belongs to the actual secondary feasible orbit. -/
theorem generatedFeasibleDisjointPair_axis_mem (z : Fin 2 × Fin 276)
    (hz : z ∈ generatedFeasibleDisjointPairLabels) (c : ZMod 2) :
    conwayShortAxis (Sum.inl z) c ∈
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleSecondaryLocalOrbit_eq_physical]
  refine ⟨⟨(Sum.inl z, c), ?_⟩, rfl⟩
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  simpa only [generatedFeasibleOrthogonalShortLabels, Finset.inl_mem_disjSum] using
    Finset.mem_of_mem_erase hz

/-- Every actual disjoint-pair signed input reaches the source prototype inside the simultaneous
first-axis and Omega stabilizer. -/
theorem generatedFeasibleDisjointPair_to_prototype (z : Fin 2 × Fin 276)
    (hz : z ∈ generatedFeasibleDisjointPairLabels) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis (Sum.inl z) c) =
        conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel d := by
  obtain ⟨e, he, hf, hrs⟩ := generatedFeasibleDisjointPair_monomial z.1 z.2 hz
  have hi := generatedFeasibleDisjointPair_independent 0 _
    generatedFeasibleDisjointPairPrototype_mem
  exact generatedFeasible_monomial_independent_signed _ _ _ e he hf hrs hi.1 hi.2 c d

/-- All original disjoint-pair signed inputs are connected inside the genuine simultaneous group. -/
theorem generatedFeasibleDisjointPair_transitive (z w : Fin 2 × Fin 276)
    (hz : z ∈ generatedFeasibleDisjointPairLabels) (hw : w ∈ generatedFeasibleDisjointPairLabels)
    (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis (Sum.inl z) c) = conwayShortAxis (Sum.inl w) d := by
  obtain ⟨a, ha⟩ := generatedFeasibleDisjointPair_to_prototype z hz c 0
  obtain ⟨b, hb⟩ := generatedFeasibleDisjointPair_to_prototype w hw d 0
  refine ⟨b⁻¹ * a, ?_⟩
  change rhoLocal (b.val⁻¹ * a.val) _ = _
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ha, ← hb]
  rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel, map_one]
  rfl

/-- The462 original preferred disjoint-pair addresses and their two actual binary signs. -/
def GeneratedFeasibleDisjointPairAddress := generatedFeasibleDisjointPairLabels × ZMod 2

/-- The actual disjoint-pair signed sector in the original Griess space. -/
def generatedFeasibleDisjointPairAxes : Set GriessSpace :=
  Set.range (fun a : GeneratedFeasibleDisjointPairAddress => conwayShortAxis (Sum.inl a.1.val) a.2)

/-- The original disjoint coordinate-pair sector contains exactly924 distinct signed axes. -/
theorem generatedFeasibleDisjointPairAxes_card :
    Nat.card generatedFeasibleDisjointPairAxes = 924 := by
  let f := fun a : GeneratedFeasibleDisjointPairAddress => conwayShortAxis (Sum.inl a.1.val) a.2
  have hf : Function.Injective f := by
    intro a b he
    have hh := @generatedAxis_signed_injective (Sum.inl a.1.val, a.2) (Sum.inl b.1.val, b.2) he
    have hl : a.1 = b.1 := Subtype.ext (Sum.inl_injective (congrArg Prod.fst hh))
    exact Prod.ext hl (congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh)
  change Nat.card (Set.range f) = 924
  rw [← Nat.card_congr (Equiv.ofInjective f hf)]
  change Nat.card (generatedFeasibleDisjointPairLabels × ZMod 2) = 924
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe,
    generatedFeasibleDisjointPairLabels_card]
  norm_num [Nat.card_eq_fintype_card]

/-- The genuine simultaneous stabilizer orbit of the original disjoint minus-pair prototype. -/
def generatedFeasibleDisjointPairOrbit : Set GriessSpace :=
  Set.range (fun h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓
      localOmegaStabilizer) =>
    rhoLocal h.val (conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0))

/-- All genuine disjoint-pair physical axes lie in the original simultaneous orbit. -/
theorem generatedFeasibleDisjointPairAxes_subset_orbit :
    generatedFeasibleDisjointPairAxes ⊆ generatedFeasibleDisjointPairOrbit := by
  rintro x ⟨a, rfl⟩
  obtain ⟨h, hh⟩ := generatedFeasibleDisjointPair_transitive
    (0, generatedFeasibleDisjointPairPrototypeIndex) a.1.val
    generatedFeasibleDisjointPairPrototype_mem a.1.property 0 a.2
  exact ⟨h, hh⟩

/-- The actual simultaneous orbit acquires neither another family nor either signed mate axis. -/
theorem generatedFeasibleDisjointPairOrbit_subset_axes :
    generatedFeasibleDisjointPairOrbit ⊆ generatedFeasibleDisjointPairAxes := by
  rintro x ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hmon := generatedFeasible_localOmega_lift_monomial f (hf.symm ▸ h.property.2)
  have hfirst : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    hf.symm ▸ h.property.1
  have hp := (localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp hfirst
  have hplus := (generatedFeasible_monomial_pair_fix_iff f.val.2 hmon).mp hp.1
  let r := griessShortPermutation f.val.2 generatedFeasibleDisjointPairPrototypeLabel
  let c := localShortPhase f generatedFeasibleDisjointPairPrototypeLabel + 0
  have himage : rhoLocal h.val (conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0) =
      conwayShortAxis r c := by
    rw [← hf]
    exact generatedAxis_localFiber_image f _ _
  have hmate : r ≠ Sum.inl (1, generatedFeasiblePhysicalRootPair) := by
    intro he
    apply generatedFeasibleDisjointPair_ne_root 0 _ generatedFeasibleDisjointPairPrototype_mem 1
    exact (griessShortPermutation f.val.2).injective (he.trans hplus.symm)
  have hphys : conwayShortAxis r c ∈ generatedFeasibleOrthogonalSignedShortAxes := by
    rw [← generatedFeasibleSecondaryLocalOrbit_eq_physical]
    obtain ⟨k, hk⟩ := generatedFeasibleDisjointPair_axis_mem
      (0, generatedFeasibleDisjointPairPrototypeIndex) generatedFeasibleDisjointPairPrototype_mem 0
    change rhoLocal k.val (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
      conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0 at hk
    refine ⟨⟨h.val, h.property.1⟩ * k, ?_⟩
    change rhoLocal (h.val * k.val) _ = _
    rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hk]
    exact himage
  obtain ⟨z, hz⟩ := hphys
  have hzc : z.val = (r, c) := generatedAxis_signed_injective hz
  have hr : r ∈ generatedFeasibleOrthogonalShortLabels := by
    have hm := (Finset.mem_product.mp z.property).1
    simpa only [hzc] using hm
  have hfamily : leechRootedA2NeighborFamily r = 0 :=
    leechRootedA2_monomial_preserves_family f.val.2 hmon _
  rcases r with z | z
  · have hz : z ∈ generatedFeasibleOrthogonalPairLabels := by
      simpa only [generatedFeasibleOrthogonalShortLabels, Finset.inl_mem_disjSum] using hr
    have hn : z ≠ (1, generatedFeasiblePhysicalRootPair) := by
      intro he
      exact hmate (congrArg Sum.inl he)
    let a : GeneratedFeasibleDisjointPairAddress := (⟨z, Finset.mem_erase.mpr ⟨hn, hz⟩⟩, c)
    exact ⟨a, himage.symm⟩
  · rcases z with z | z
    · change (1 : Fin 3) = 0 at hfamily
      contradiction
    · change (2 : Fin 3) = 0 at hfamily
      contradiction

/-- The original disjoint-pair physical sector is exactly one genuine simultaneous orbit. -/
theorem generatedFeasibleDisjointPairOrbit_eq_axes :
    generatedFeasibleDisjointPairOrbit = generatedFeasibleDisjointPairAxes :=
  Set.Subset.antisymm generatedFeasibleDisjointPairOrbit_subset_axes
    generatedFeasibleDisjointPairAxes_subset_orbit

/-- The actual disjoint-pair simultaneous orbit has exactly924 elements. -/
theorem generatedFeasibleDisjointPairOrbit_card :
    Nat.card generatedFeasibleDisjointPairOrbit = 924 := by
  rw [generatedFeasibleDisjointPairOrbit_eq_axes, generatedFeasibleDisjointPairAxes_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
