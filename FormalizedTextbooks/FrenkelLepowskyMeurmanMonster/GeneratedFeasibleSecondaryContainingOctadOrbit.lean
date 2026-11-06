/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadSigns

/-! Exact genuine simultaneous orbit of the 4928 containing-pair secondary octad axes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every actual containing-pair signed input reaches the original prototype inside
the simultaneous first-axis and Omega stabilizer. -/
theorem generatedFeasibleContainingOctad_to_prototype (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 0) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) =
        conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel d := by
  obtain ⟨⟨o, t⟩, hz, rfl⟩ := Finset.mem_map.mp hr
  have hp := (Finset.mem_filter.mp hz).2
  obtain ⟨e, he, hf, hrs⟩ := generatedFeasibleContainingOctad_monomial o t hp.1 hp.2
  have hi := generatedFeasibleSecondaryNonPair_independent 0 _
    generatedFeasibleContainingOctadPrototypeLabel_mem
  exact generatedFeasible_monomial_independent_signed _ _ _ e he hf hrs hi.1 hi.2 c d

/-- All actual containing-pair signed inputs are connected inside the genuine simultaneous group. -/
theorem generatedFeasibleContainingOctad_transitive (r s : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 0)
    (hs : s ∈ generatedFeasibleSecondaryNonPairLabels 0) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis s d := by
  obtain ⟨a, ha⟩ := generatedFeasibleContainingOctad_to_prototype r hr c 0
  obtain ⟨b, hb⟩ := generatedFeasibleContainingOctad_to_prototype s hs d 0
  refine ⟨b⁻¹ * a, ?_⟩
  change rhoLocal (b.val⁻¹ * a.val) _ = _
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ha, ← hb]
  rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel, map_one]
  rfl

/-- Original containing octads, their genuine perpendicular canonical signs,
and the two actual binary axis signs. -/
def GeneratedFeasibleContainingOctadAddress :=
  (Σ o : generatedFeasibleOctadContainingLabels,
    {t : Fin 64 // griessShortIntegral (Sum.inr (Sum.inl (o.val, t))) 0 =
      griessShortIntegral (Sum.inr (Sum.inl (o.val, t))) 1}) × ZMod 2

/-- The actual preferred short label determined by an original containing-octad address. -/
def generatedFeasibleContainingOctadAddressLabel (a : GeneratedFeasibleContainingOctadAddress) :
    GriessShortIndex := Sum.inr (Sum.inl (a.1.1.val, a.1.2.val))

/-- Every factor address belongs to the original containing-pair physical catalogue. -/
theorem generatedFeasibleContainingOctadAddressLabel_mem
    (a : GeneratedFeasibleContainingOctadAddress) :
    generatedFeasibleContainingOctadAddressLabel a ∈ generatedFeasibleSecondaryNonPairLabels 0 := by
  change _ ∈ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadContainingLabels).map _
  refine Finset.mem_map.mpr ⟨(a.1.1.val, a.1.2.val), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.1.1.property, a.1.2.property⟩

/-- The actual signed containing-octad sector in the original Griess space. -/
def generatedFeasibleContainingOctadAxes : Set GriessSpace :=
  Set.range (fun a : GeneratedFeasibleContainingOctadAddress =>
    conwayShortAxis (generatedFeasibleContainingOctadAddressLabel a) a.2)

/-- There are exactly 4928 distinct actual containing-pair octad axes. -/
theorem generatedFeasibleContainingOctadAxes_card :
    Nat.card generatedFeasibleContainingOctadAxes = 4928 := by
  let f := fun a : GeneratedFeasibleContainingOctadAddress =>
    conwayShortAxis (generatedFeasibleContainingOctadAddressLabel a) a.2
  have hf : Function.Injective f := by
    rintro ⟨⟨o, t⟩, c⟩ ⟨⟨p, s⟩, d⟩ he
    have hh := @generatedAxis_signed_injective
      (Sum.inr (Sum.inl (o.val, t.val)), c)
      (Sum.inr (Sum.inl (p.val, s.val)), d) he
    have hl : (o.val, t.val) = (p.val, s.val) :=
      Sum.inl_injective (Sum.inr_injective (congrArg Prod.fst hh))
    have ho : o = p := Subtype.ext (congrArg Prod.fst hl)
    subst p
    have ht : t = s := Subtype.ext (congrArg Prod.snd hl)
    subst s
    have hc : c = d := congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh
    subst d
    rfl
  change Nat.card (Set.range f) = 4928
  rw [← Nat.card_congr (Equiv.ofInjective f hf)]
  change Nat.card ((Σ o : generatedFeasibleOctadContainingLabels,
    {t : Fin 64 // griessShortIntegral (Sum.inr (Sum.inl (o.val, t))) 0 =
      griessShortIntegral (Sum.inr (Sum.inl (o.val, t))) 1}) × ZMod 2) = 4928
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hs (o : generatedFeasibleOctadContainingLabels) :
      Fintype.card {t : Fin 64 // griessShortIntegral (Sum.inr (Sum.inl (o.val, t))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o.val, t))) 1} = 32 := by
    rw [Fintype.card_subtype]
    exact generatedFeasibleOctadContaining_physical_count o.val o.property
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [generatedFeasibleOctadContainingLabels_card, Nat.card_eq_fintype_card, ZMod.card]
  norm_num

/-- The actual simultaneous stabilizer orbit of the original positive standard octad. -/
def generatedFeasibleContainingOctadOrbit : Set GriessSpace :=
  Set.range (fun h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓
      localOmegaStabilizer) =>
    rhoLocal h.val (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0))

/-- All genuine physical containing-pair axes lie in the original simultaneous orbit. -/
theorem generatedFeasibleContainingOctadAxes_subset_orbit :
    generatedFeasibleContainingOctadAxes ⊆ generatedFeasibleContainingOctadOrbit := by
  rintro x ⟨a, rfl⟩
  obtain ⟨h, hh⟩ := generatedFeasibleContainingOctad_transitive
    generatedFeasibleContainingOctadPrototypeLabel (generatedFeasibleContainingOctadAddressLabel a)
    generatedFeasibleContainingOctadPrototypeLabel_mem
    (generatedFeasibleContainingOctadAddressLabel_mem a) 0 a.2
  exact ⟨h, hh⟩

/-- Any original fiber lift fixing the actual Omega vector is genuinely monomial. -/
theorem generatedFeasible_localOmega_lift_monomial (f : localFiberSubgroup)
    (hf : localFiberIntoH f ∈ localOmegaStabilizer) :
    f.val.2 ∈ golayMonomialSubgroup := by
  have hc := localOmegaStabilizer_projection_mem ⟨localFiberIntoH f, hf⟩
  change leechBinaryAction f.val.2 (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    Multiplicative.toAdd (qQuotHom sourceOmegaQ) at hc
  rw [sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates] at hc
  rw [← leechFrameClass_stabilizer_eq_monomial]
  exact leechHyperbolicCoordinates.injective hc

/-- The original positive standard octad has the genuine standard-root neighbor condition. -/
theorem generatedFeasibleContainingOctadPrototype_neighbor :
    leechRootedA2NeighborPredicate generatedFeasibleContainingOctadPrototypeLabel := by
  left
  rw [generatedFeasibleContainingOctadPrototype_integral,
    generatedFeasibleContainingOctadPrototype_integral]
  rfl

/-- The actual simultaneous orbit acquires neither another family nor an outside-pair octad. -/
theorem generatedFeasibleContainingOctadOrbit_subset_axes :
    generatedFeasibleContainingOctadOrbit ⊆ generatedFeasibleContainingOctadAxes := by
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
  let r := griessShortPermutation f.val.2 generatedFeasibleContainingOctadPrototypeLabel
  let c := localShortPhase f generatedFeasibleContainingOctadPrototypeLabel + 0
  have himage : rhoLocal h.val
      (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0) =
        conwayShortAxis r c := by
    rw [← hf]
    exact generatedAxis_localFiber_image f _ _
  have hneighbor : leechRootedA2NeighborPredicate r := leechRootedA2_root_action_neighbor _
    hroot _ generatedFeasibleContainingOctadPrototype_neighbor
  have hphys : conwayShortAxis r c ∈ generatedFeasibleOrthogonalSignedShortAxes := by
    rw [← generatedFeasibleSecondaryLocalOrbit_eq_physical]
    obtain ⟨k, hk⟩ := generatedFeasibleSecondaryNonPair_axis_mem 0 _
      generatedFeasibleContainingOctadPrototypeLabel_mem 0
    change rhoLocal k.val (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
      conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0 at hk
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
    · have ho : o ∈ generatedFeasibleOctadContainingLabels :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((leechRootedA2Octad_neighbor_iff o t).mp hneighbor).1⟩
      have ht := (generatedFeasibleOrthogonalShortLabels_mem _).mp hr
      let a : GeneratedFeasibleContainingOctadAddress := (⟨⟨o, ho⟩, ⟨t, ht⟩⟩, c)
      refine ⟨a, ?_⟩
      exact himage.symm
    · change (2 : Fin 3) = 1 at hfamily
      contradiction

/-- The genuine containing-pair physical sector is exactly one actual simultaneous orbit. -/
theorem generatedFeasibleContainingOctadOrbit_eq_axes :
    generatedFeasibleContainingOctadOrbit = generatedFeasibleContainingOctadAxes :=
  Set.Subset.antisymm generatedFeasibleContainingOctadOrbit_subset_axes
    generatedFeasibleContainingOctadAxes_subset_orbit

/-- The actual containing-pair octad simultaneous orbit has exactly 4928 elements. -/
theorem generatedFeasibleContainingOctadOrbit_card :
    Nat.card generatedFeasibleContainingOctadOrbit = 4928 := by
  rw [generatedFeasibleContainingOctadOrbit_eq_axes, generatedFeasibleContainingOctadAxes_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
