/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryBinaryIndependence
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OddMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2RootStabilizer

/-! Genuine monomial and extraspecial transport of the actual secondary odd sector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original preferred odd line with zero encoder word and exceptional coordinate two. -/
def generatedFeasibleSecondaryOddPrototypeLabel : GriessShortIndex := Sum.inr (Sum.inr (0, 2))

/-- The prototype belongs to the actual physical odd sector. -/
theorem generatedFeasibleSecondaryOddPrototypeLabel_mem :
    generatedFeasibleSecondaryOddPrototypeLabel ∈ generatedFeasibleSecondaryNonPairLabels 2 := by
  change _ ∈ generatedFeasibleOrthogonalOddLabels.map _
  refine Finset.mem_map.mpr ⟨(0, 2), ?_, rfl⟩
  rw [generatedFeasibleOrthogonalOddLabels_mem]
  decide +kernel

private theorem prototype_integral (i : Fin 24) :
    griessShortIntegral generatedFeasibleSecondaryOddPrototypeLabel i =
      if i = 2 then -3 else 1 := by
  have h : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [generatedFeasibleSecondaryOddPrototypeLabel, griessShortIntegral, Fin.val_zero, h,
    Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte, one_mul]

/-- Every original perpendicular odd preferred label admits an actual Golay monomial
transport to the prototype fixing the original first preferred root line. -/
theorem generatedFeasibleSecondaryOdd_monomial (d : Fin 2048) (j : Fin 24)
    (hr : (d, j) ∈ generatedFeasibleOrthogonalOddLabels) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧
      griessShortPermutation e (Sum.inr (Sum.inr (d, j))) =
        generatedFeasibleSecondaryOddPrototypeLabel := by
  have hh := (generatedFeasibleOdd_orthogonal_iff d j).mp
    ((generatedFeasibleOrthogonalOddLabels_mem d j).mp hr)
  let a : Fin 3 → Fin 24 := ![0, 1, j]
  let b : Fin 3 → Fin 24 := ![0, 1, 2]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
  have hb : Function.Injective b := by decide +kernel
  obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a b ha hb
  have hp0 : p.val 0 = 0 := hp 0
  have hp1 : p.val 1 = 1 := hp 1
  have hpj : p.val j = 2 := hp 2
  have hs0 : p.val.symm 0 = 0 := p.val.symm_apply_eq.mpr hp0.symm
  have hs1 : p.val.symm 1 = 1 := p.val.symm_apply_eq.mpr hp1.symm
  let c : golayCode :=
    ⟨golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)), ⟨_, rfl⟩⟩
  let cp : golayCode := golayCodePermutation p c
  have hc : c.val 0 = c.val 1 := by
    apply ZMod.val_injective
    change (golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) 0).val =
      (golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) 1).val
    rw [golayLabelEncoder_match, golayLabelEncoder_match]
    have he := (Finset.mem_filter.mp hh.2.2).2
    simp only [Fin.val_zero, Fin.val_one, he]
  have hcp : cp.val 0 = cp.val 1 := by
    change c.val (p.val.symm 0) = c.val (p.val.symm 1)
    rwa [hs0, hs1]
  let e : leechIsomSubgroup := golaySignIsometry cp * golayPermutationIsometry p
  refine ⟨e, ⟨cp, p, rfl⟩, ?_, ?_⟩
  · rw [leechRootedA2_short_perm_eq_iff]
    have hperm : leechIntegralAction (golayPermutationIsometry p)
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
      apply Subtype.ext
      rw [leechIntegralAction_golayPermutation]
      funext i
      simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
        generatedFeasiblePhysicalRootPair_coordinates]
      have hi0 : p.val.symm i = 0 ↔ i = 0 := by rw [p.val.symm_apply_eq, hp0]
      have hi1 : p.val.symm i = 1 ↔ i = 1 := by rw [p.val.symm_apply_eq, hp1]
      simp only [hi0, hi1]
    change leechIntegralAction (golaySignIsometry cp * golayPermutationIsometry p) _ = _ ∨ _
    rw [map_mul, LinearEquiv.mul_apply, hperm]
    by_cases hz : cp.val 0 = 0
    · left
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      simp only [griessShortLatticeVector, griessShortIntegral,
        generatedFeasiblePhysicalRootPair_coordinates]
      have hz1 : cp.val 1 = 0 := hcp.symm.trans hz
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [golayIntegerSign, hi0, hi1, hz, hz1]
    · right
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      simp only [griessShortLatticeVector, griessShortIntegral,
        generatedFeasiblePhysicalRootPair_coordinates, Submodule.coe_neg, Pi.neg_apply]
      have hz1 : cp.val 1 ≠ 0 := fun h => hz (hcp.trans h)
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [golayIntegerSign, hi0, hi1, hz, hz1]
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    funext i
    have hpi : p.val.symm i = j ↔ i = 2 := by rw [p.val.symm_apply_eq, hpj]
    have hv : golayIntegerPermute p.val
        (griessShortLatticeVector (Sum.inr (Sum.inr (d, j)))).val i =
          leechRootedA2CodeSign (cp.val i) * (if i = 2 then -3 else 1) := by
      simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
        leechRootedA2Odd_encoder_sign, hpi]
      rfl
    change (if cp.val i = 0 then
        golayIntegerPermute p.val (griessShortLatticeVector _).val i
      else -golayIntegerPermute p.val (griessShortLatticeVector _).val i) = _
    rw [hv]
    change _ = griessShortIntegral generatedFeasibleSecondaryOddPrototypeLabel i
    rw [prototype_integral]
    by_cases hz : cp.val i = 0 <;>
      simp only [leechRootedA2CodeSign, hz, ite_true, ite_false, one_mul, neg_one_mul,
        neg_neg]

/-- Every actual odd signed input reaches the original prototype inside the simultaneous
first-axis and Omega stabilizer. -/
theorem generatedFeasibleSecondaryOdd_to_prototype (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 2) (c t : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) =
        conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel t := by
  obtain ⟨⟨d, j⟩, hz, rfl⟩ := Finset.mem_map.mp hr
  obtain ⟨e, he, hp, hrs⟩ := generatedFeasibleSecondaryOdd_monomial d j hz
  have hi := generatedFeasibleSecondaryNonPair_independent 2 _
    generatedFeasibleSecondaryOddPrototypeLabel_mem
  exact generatedFeasible_monomial_independent_signed _ _ _ e he hp hrs hi.1 hi.2 c t

/-- All 45056 actual odd signed inputs lie in one genuine simultaneous orbit. -/
theorem generatedFeasibleSecondaryOdd_transitive (r s : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 2)
    (hs : s ∈ generatedFeasibleSecondaryNonPairLabels 2) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis s d := by
  obtain ⟨a, ha⟩ := generatedFeasibleSecondaryOdd_to_prototype r hr c 0
  obtain ⟨b, hb⟩ := generatedFeasibleSecondaryOdd_to_prototype s hs d 0
  refine ⟨b⁻¹ * a, ?_⟩
  change rhoLocal (b.val⁻¹ * a.val) _ = _
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ha, ← hb]
  rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel, map_one]
  rfl

/-- Original odd addresses: the actual equal-sign half-codeword, an outside coordinate,
and its genuine binary axis sign. -/
def GeneratedFeasibleSecondaryOddAddress :=
  generatedFeasibleOddEqualSignCodes × {j : Fin 24 // j ≠ 0 ∧ j ≠ 1} × ZMod 2

/-- The actual preferred short label determined by an original odd address. -/
def generatedFeasibleSecondaryOddAddressLabel (a : GeneratedFeasibleSecondaryOddAddress) :
    GriessShortIndex := Sum.inr (Sum.inr (a.1.val, a.2.1.val))

/-- Each original address lies in the actual physical odd sector. -/
theorem generatedFeasibleSecondaryOddAddressLabel_mem (a : GeneratedFeasibleSecondaryOddAddress) :
    generatedFeasibleSecondaryOddAddressLabel a ∈ generatedFeasibleSecondaryNonPairLabels 2 := by
  change _ ∈ generatedFeasibleOrthogonalOddLabels.map _
  refine Finset.mem_map.mpr ⟨(a.1.val, a.2.1.val), ?_, rfl⟩
  rw [generatedFeasibleOrthogonalOddLabels_mem, generatedFeasibleOdd_orthogonal_iff]
  exact ⟨a.2.1.property.1, a.2.1.property.2, a.1.property⟩

/-- The actual signed odd sector as a set of genuine Griess vectors. -/
def generatedFeasibleSecondaryOddAxes : Set GriessSpace :=
  Set.range (fun a : GeneratedFeasibleSecondaryOddAddress =>
    conwayShortAxis (generatedFeasibleSecondaryOddAddressLabel a) a.2.2)

/-- The physical odd sector consists of exactly 45056 distinct actual axes. -/
theorem generatedFeasibleSecondaryOddAxes_card :
    Nat.card generatedFeasibleSecondaryOddAxes = 45056 := by
  let f := fun a : GeneratedFeasibleSecondaryOddAddress =>
    conwayShortAxis (generatedFeasibleSecondaryOddAddressLabel a) a.2.2
  have hf : Function.Injective f := by
    rintro ⟨d, j, c⟩ ⟨e, k, t⟩ he
    have hh := @generatedAxis_signed_injective
      (Sum.inr (Sum.inr (d.val, j.val)), c)
      (Sum.inr (Sum.inr (e.val, k.val)), t) he
    have hl : (d.val, j.val) = (e.val, k.val) :=
      Sum.inr_injective (Sum.inr_injective (congrArg Prod.fst hh))
    have hd : d = e := Subtype.ext (congrArg Prod.fst hl)
    have hj : j = k := Subtype.ext (congrArg Prod.snd hl)
    have hc : c = t := congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh
    exact Prod.ext hd (Prod.ext hj hc)
  change Nat.card (Set.range f) = 45056
  rw [← Nat.card_congr (Equiv.ofInjective f hf)]
  change Nat.card (generatedFeasibleOddEqualSignCodes ×
    {j : Fin 24 // j ≠ 0 ∧ j ≠ 1} × ZMod 2) = 45056
  rw [Nat.card_prod, Nat.card_prod]
  have hcode : Nat.card generatedFeasibleOddEqualSignCodes = 1024 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, generatedFeasibleOddEqualSignCodes_card]
  have hout : Nat.card {j : Fin 24 // j ≠ 0 ∧ j ≠ 1} = 22 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcode, hout, Nat.card_eq_fintype_card, ZMod.card]

/-- The genuine simultaneous stabilizer orbit of the original odd prototype. -/
def generatedFeasibleSecondaryOddOrbit : Set GriessSpace :=
  Set.range (fun h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓
      localOmegaStabilizer) =>
    rhoLocal h.val (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0))

/-- Every actual physical odd signed input belongs to the genuine prototype orbit. -/
theorem generatedFeasibleSecondaryOddAxes_subset_orbit :
    generatedFeasibleSecondaryOddAxes ⊆ generatedFeasibleSecondaryOddOrbit := by
  rintro x ⟨a, rfl⟩
  obtain ⟨h, hh⟩ := generatedFeasibleSecondaryOdd_transitive
    generatedFeasibleSecondaryOddPrototypeLabel (generatedFeasibleSecondaryOddAddressLabel a)
    generatedFeasibleSecondaryOddPrototypeLabel_mem
    (generatedFeasibleSecondaryOddAddressLabel_mem a) 0 a.2.2
  exact ⟨h, hh⟩

/-- Fixing actual Omega forces every original isometry lift to be genuinely monomial. -/
private theorem omega_lift_monomial (f : localFiberSubgroup)
    (hf : localFiberIntoH f ∈ localOmegaStabilizer) :
    f.val.2 ∈ golayMonomialSubgroup := by
  have hc := localOmegaStabilizer_projection_mem ⟨localFiberIntoH f, hf⟩
  change leechBinaryAction f.val.2 (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    Multiplicative.toAdd (qQuotHom sourceOmegaQ) at hc
  rw [sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates] at hc
  rw [← leechFrameClass_stabilizer_eq_monomial]
  exact leechHyperbolicCoordinates.injective hc

/-- No additional physical family enters the genuine odd prototype orbit. -/
theorem generatedFeasibleSecondaryOddOrbit_subset_axes :
    generatedFeasibleSecondaryOddOrbit ⊆ generatedFeasibleSecondaryOddAxes := by
  rintro x ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hmon := omega_lift_monomial f (hf.symm ▸ h.property.2)
  let r := griessShortPermutation f.val.2 generatedFeasibleSecondaryOddPrototypeLabel
  let c := localShortPhase f generatedFeasibleSecondaryOddPrototypeLabel + 0
  have himage : rhoLocal h.val
      (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0) =
        conwayShortAxis r c := by
    rw [← hf]
    exact generatedAxis_localFiber_image f _ _
  have hphys : conwayShortAxis r c ∈ generatedFeasibleOrthogonalSignedShortAxes := by
    rw [← generatedFeasibleSecondaryLocalOrbit_eq_physical]
    obtain ⟨k, hk⟩ := generatedFeasibleSecondaryNonPair_axis_mem 2 _
      generatedFeasibleSecondaryOddPrototypeLabel_mem 0
    change rhoLocal k.val (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
      conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0 at hk
    refine ⟨⟨h.val, h.property.1⟩ * k, ?_⟩
    change rhoLocal (h.val * k.val) _ = _
    rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hk]
    exact himage
  obtain ⟨z, hz⟩ := hphys
  have hzc : z.val = (r, c) := generatedAxis_signed_injective hz
  have hr : r ∈ generatedFeasibleOrthogonalShortLabels := by
    have hm := (Finset.mem_product.mp z.property).1
    simpa only [hzc] using hm
  have hfamily : leechRootedA2NeighborFamily r = 2 :=
    leechRootedA2_monomial_preserves_family f.val.2 hmon _
  rcases r with z | z
  · change (0 : Fin 3) = 2 at hfamily
    contradiction
  · rcases z with z | ⟨d, j⟩
    · change (1 : Fin 3) = 2 at hfamily
      contradiction
    · have hp := (generatedFeasibleOdd_orthogonal_iff d j).mp
        ((generatedFeasibleOrthogonalShortLabels_mem _).mp hr)
      let a : GeneratedFeasibleSecondaryOddAddress :=
        (⟨d, hp.2.2⟩, ⟨j, hp.1, hp.2.1⟩, c)
      refine ⟨a, ?_⟩
      exact himage.symm

/-- The actual 45056-axis odd physical sector is exactly one genuine simultaneous orbit. -/
theorem generatedFeasibleSecondaryOddOrbit_eq_axes :
    generatedFeasibleSecondaryOddOrbit = generatedFeasibleSecondaryOddAxes :=
  Set.Subset.antisymm generatedFeasibleSecondaryOddOrbit_subset_axes
    generatedFeasibleSecondaryOddAxes_subset_orbit

/-- The genuine odd prototype orbit has exactly 45056 elements. -/
theorem generatedFeasibleSecondaryOddOrbit_card :
    Nat.card generatedFeasibleSecondaryOddOrbit = 45056 := by
  rw [generatedFeasibleSecondaryOddOrbit_eq_axes, generatedFeasibleSecondaryOddAxes_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
