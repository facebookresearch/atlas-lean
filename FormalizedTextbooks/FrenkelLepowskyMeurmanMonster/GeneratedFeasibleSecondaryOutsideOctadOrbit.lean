/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOutsideOctadSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadOrbit

/-! Exact genuine simultaneous orbit of the 42240 outside-pair secondary octad axes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every actual outside-pair signed input reaches the original prototype inside
the simultaneous first-axis and Omega stabilizer. -/
theorem generatedFeasibleOutsideOctad_to_prototype (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 1) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) =
        conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel d := by
  obtain ⟨⟨o, t⟩, hz, rfl⟩ := Finset.mem_map.mp hr
  have hp := (Finset.mem_filter.mp hz).2
  obtain ⟨e, he, hf, hrs⟩ := generatedFeasibleOutsideOctad_monomial o t hp.1
  have hi := generatedFeasibleSecondaryNonPair_independent 1 _
    generatedFeasibleOutsideOctadPrototypeLabel_mem
  exact generatedFeasible_monomial_independent_signed _ _ _ e he hf hrs hi.1 hi.2 c d

/-- All actual outside-pair signed inputs are connected inside the genuine simultaneous group. -/
theorem generatedFeasibleOutsideOctad_transitive (r s : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 1)
    (hs : s ∈ generatedFeasibleSecondaryNonPairLabels 1) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis s d := by
  obtain ⟨a, ha⟩ := generatedFeasibleOutsideOctad_to_prototype r hr c 0
  obtain ⟨b, hb⟩ := generatedFeasibleOutsideOctad_to_prototype s hs d 0
  refine ⟨b⁻¹ * a, ?_⟩
  change rhoLocal (b.val⁻¹ * a.val) _ = _
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ha, ← hb]
  rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel, map_one]
  rfl

/-- Original outside octads, all64 canonical signs, and the two genuine axis signs. -/
def GeneratedFeasibleOutsideOctadAddress :=
  (generatedFeasibleOctadOutsideLabels × Fin 64) × ZMod 2

/-- The actual preferred short label at an original outside-octad factor address. -/
def generatedFeasibleOutsideOctadAddressLabel (a : GeneratedFeasibleOutsideOctadAddress) :
    GriessShortIndex := Sum.inr (Sum.inl (a.1.1.val, a.1.2))

/-- Every factor address belongs to the original outside-pair physical catalogue. -/
theorem generatedFeasibleOutsideOctadAddressLabel_mem (a : GeneratedFeasibleOutsideOctadAddress) :
    generatedFeasibleOutsideOctadAddressLabel a ∈ generatedFeasibleSecondaryNonPairLabels 1 := by
  change _ ∈ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadOutsideLabels).map _
  refine Finset.mem_map.mpr ⟨(a.1.1.val, a.1.2), ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.1.1.property, ?_⟩
  have h := (Finset.mem_filter.mp a.1.1.property).2
  simp only [griessShortIntegral, Fin.val_zero, Fin.val_one, h.1, h.2,
    Bool.false_eq_true, ite_false]

/-- The actual signed outside-octad sector in the original Griess space. -/
def generatedFeasibleOutsideOctadAxes : Set GriessSpace :=
  Set.range (fun a : GeneratedFeasibleOutsideOctadAddress =>
    conwayShortAxis (generatedFeasibleOutsideOctadAddressLabel a) a.2)

/-- There are exactly42240 distinct actual outside-pair octad signed axes. -/
theorem generatedFeasibleOutsideOctadAxes_card :
    Nat.card generatedFeasibleOutsideOctadAxes = 42240 := by
  let f := fun a : GeneratedFeasibleOutsideOctadAddress =>
    conwayShortAxis (generatedFeasibleOutsideOctadAddressLabel a) a.2
  have hf : Function.Injective f := by
    rintro ⟨⟨o, t⟩, c⟩ ⟨⟨p, s⟩, d⟩ he
    have hh := @generatedAxis_signed_injective
      (Sum.inr (Sum.inl (o.val, t)), c)
      (Sum.inr (Sum.inl (p.val, s)), d) he
    have hl : (o.val, t) = (p.val, s) :=
      Sum.inl_injective (Sum.inr_injective (congrArg Prod.fst hh))
    have ho : o = p := Subtype.ext (congrArg Prod.fst hl)
    subst p
    have ht : t = s := congrArg Prod.snd hl
    subst s
    have hc : c = d := congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh
    subst d
    rfl
  change Nat.card (Set.range f) = 42240
  rw [← Nat.card_congr (Equiv.ofInjective f hf)]
  change Nat.card ((generatedFeasibleOctadOutsideLabels × Fin 64) × ZMod 2) = 42240
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe,
    generatedFeasibleOctadOutsideLabels_card]
  norm_num [Nat.card_eq_fintype_card]

/-- The actual simultaneous stabilizer orbit of the original positive outside octad. -/
def generatedFeasibleOutsideOctadOrbit : Set GriessSpace :=
  Set.range (fun h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓
      localOmegaStabilizer) =>
    rhoLocal h.val (conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0))

/-- All genuine physical outside-pair axes lie in the original simultaneous orbit. -/
theorem generatedFeasibleOutsideOctadAxes_subset_orbit :
    generatedFeasibleOutsideOctadAxes ⊆ generatedFeasibleOutsideOctadOrbit := by
  rintro x ⟨a, rfl⟩
  obtain ⟨h, hh⟩ := generatedFeasibleOutsideOctad_transitive
    generatedFeasibleOutsideOctadPrototypeLabel (generatedFeasibleOutsideOctadAddressLabel a)
    generatedFeasibleOutsideOctadPrototypeLabel_mem
    (generatedFeasibleOutsideOctadAddressLabel_mem a) 0 a.2
  exact ⟨h, hh⟩

/-- The actual positive outside-pair prototype is not a standard-root neighbor. -/
theorem generatedFeasibleOutsideOctadPrototype_not_neighbor :
    ¬ leechRootedA2NeighborPredicate generatedFeasibleOutsideOctadPrototypeLabel := by
  change ¬(griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 0 +
    griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 1 = 4 ∨
      griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 0 +
        griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 1 = -4)
  rw [generatedFeasibleOutsideOctadPrototype_integral,
    generatedFeasibleOutsideOctadPrototype_integral]
  decide

/-- The actual simultaneous orbit acquires neither another family nor a containing-pair octad. -/
theorem generatedFeasibleOutsideOctadOrbit_subset_axes :
    generatedFeasibleOutsideOctadOrbit ⊆ generatedFeasibleOutsideOctadAxes := by
  rintro x ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hmon := generatedFeasible_localOmega_lift_monomial f (hf.symm ▸ h.property.2)
  have hfirst : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    hf.symm ▸ h.property.1
  have hp := (localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp hfirst
  have hplus := (generatedFeasible_monomial_pair_fix_iff f.val.2 hmon).mp hp.1
  have hline : f.val.2 ∈ leechRootedA2RootLineSubgroup := hplus
  have hroot := (leechRootedA2RootLineSubgroup_mem _).mp hline
  let r := griessShortPermutation f.val.2 generatedFeasibleOutsideOctadPrototypeLabel
  let c := localShortPhase f generatedFeasibleOutsideOctadPrototypeLabel + 0
  have himage : rhoLocal h.val
      (conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0) =
        conwayShortAxis r c := by
    rw [← hf]
    exact generatedAxis_localFiber_image f _ _
  have hneighbor : ¬ leechRootedA2NeighborPredicate r := by
    intro hr
    have hh := leechRootedA2_root_action_neighbor (f.val.2⁻¹)
      (leechRootedA2PreservesRootLine_inv _ hroot) r hr
    have hi : griessShortPermutation (f.val.2⁻¹) r =
        generatedFeasibleOutsideOctadPrototypeLabel := by
      change griessShortPermutation (f.val.2⁻¹)
        (griessShortPermutation f.val.2 generatedFeasibleOutsideOctadPrototypeLabel) = _
      rw [map_inv]
      exact Equiv.symm_apply_apply _ _
    rw [hi] at hh
    exact generatedFeasibleOutsideOctadPrototype_not_neighbor hh
  have hphys : conwayShortAxis r c ∈ generatedFeasibleOrthogonalSignedShortAxes := by
    rw [← generatedFeasibleSecondaryLocalOrbit_eq_physical]
    obtain ⟨k, hk⟩ := generatedFeasibleSecondaryNonPair_axis_mem 1 _
      generatedFeasibleOutsideOctadPrototypeLabel_mem 0
    change rhoLocal k.val (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
      conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0 at hk
    refine ⟨⟨h.val, h.property.1⟩ * k, ?_⟩
    change rhoLocal (h.val * k.val) _ = _
    rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hk]
    exact himage
  obtain ⟨z, hz⟩ := hphys
  have hzc : z.val = (r, c) := generatedAxis_signed_injective hz
  have hr : r ∈ generatedFeasibleOrthogonalShortLabels := by
    have hm := (Finset.mem_product.mp z.property).1
    simpa only [hzc] using hm
  have hfamily : leechRootedA2NeighborFamily r = 1 :=
    leechRootedA2_monomial_preserves_family f.val.2 hmon _
  rcases r with z | z
  · change (0 : Fin 3) = 1 at hfamily
    contradiction
  · rcases z with ⟨o, t⟩ | z
    · have ht := (generatedFeasibleOrthogonalShortLabels_mem _).mp hr
      have hn : o ∉ generatedFeasibleOctadContainingLabels := by
        intro ho
        have hm := (Finset.mem_filter.mp ho).2
        have hcoord : griessShortIntegral (Sum.inr (Sum.inl (o, t))) 0 = -2 ∨
            griessShortIntegral (Sum.inr (Sum.inl (o, t))) 0 = 2 := by
          simp only [griessShortIntegral, Fin.val_zero, hm.1, ite_true]
          split_ifs <;> simp
        apply hneighbor
        change griessShortIntegral (Sum.inr (Sum.inl (o, t))) 0 +
          griessShortIntegral (Sum.inr (Sum.inl (o, t))) 1 = 4 ∨
            griessShortIntegral (Sum.inr (Sum.inl (o, t))) 0 +
              griessShortIntegral (Sum.inr (Sum.inl (o, t))) 1 = -4
        rw [← ht]
        rcases hcoord with he | he <;> rw [he] <;> norm_num
      have hc : 0 < (Finset.univ.filter fun s : Fin 64 =>
          griessShortIntegral (Sum.inr (Sum.inl (o, s))) 0 =
            griessShortIntegral (Sum.inr (Sum.inl (o, s))) 1).card :=
        Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
      rw [generatedFeasibleOctad_physical_count] at hc
      have ho : o ∈ generatedFeasibleOctadOutsideLabels := by
        by_contra hh
        simp [hh, hn] at hc
      let a : GeneratedFeasibleOutsideOctadAddress := ((⟨o, ho⟩, t), c)
      refine ⟨a, ?_⟩
      exact himage.symm
    · change (2 : Fin 3) = 1 at hfamily
      contradiction

/-- The genuine outside-pair physical sector is exactly one actual simultaneous orbit. -/
theorem generatedFeasibleOutsideOctadOrbit_eq_axes :
    generatedFeasibleOutsideOctadOrbit = generatedFeasibleOutsideOctadAxes :=
  Set.Subset.antisymm generatedFeasibleOutsideOctadOrbit_subset_axes
    generatedFeasibleOutsideOctadAxes_subset_orbit

/-- The actual outside-pair octad simultaneous orbit has exactly 42240 elements. -/
theorem generatedFeasibleOutsideOctadOrbit_card :
    Nat.card generatedFeasibleOutsideOctadOrbit = 42240 := by
  rw [generatedFeasibleOutsideOctadOrbit_eq_axes, generatedFeasibleOutsideOctadAxes_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
