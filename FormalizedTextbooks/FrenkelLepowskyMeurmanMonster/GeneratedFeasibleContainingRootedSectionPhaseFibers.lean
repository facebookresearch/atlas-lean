/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingRootedSectionGeometry

/-! Actual coset projection to the complete rooted-section geometry and its phase fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- A genuine homomorphism induces the original left-coset map to a subgroup quotient. -/
def generatedFeasibleContainingCosetMap {Γ Δ : Type*} [Group Γ] [Group Δ]
    (f : Γ →* Δ) (K : Subgroup Δ) : Γ ⧸ K.comap f → Δ ⧸ K :=
  Quotient.map' f (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    change f (a⁻¹ * b) ∈ K at h
    rwa [map_mul, map_inv] at h)

/-- Surjectivity of the original homomorphism makes its preimage-coset map bijective. -/
theorem generatedFeasibleContainingCosetMap_bijective {Γ Δ : Type*} [Group Γ] [Group Δ]
    (f : Γ →* Δ) (K : Subgroup Δ) (hf : Function.Surjective f) :
    Function.Bijective (generatedFeasibleContainingCosetMap f K) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        intro h
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        have hh := Quotient.exact' h
        rw [QuotientGroup.leftRel_apply] at hh
        change (f a)⁻¹ * f b ∈ K at hh
        change f (a⁻¹ * b) ∈ K
        simpa only [map_mul, map_inv] using hh
  · intro y
    induction y using Quotient.inductionOn with
    | h b =>
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨QuotientGroup.mk a, rfl⟩

/-- Actual preimage cosets retain all original quotient values under a surjective map. -/
def generatedFeasibleContainingCosetEquiv {Γ Δ : Type*} [Group Γ] [Group Δ]
    (f : Γ →* Δ) (K : Subgroup Δ) (hf : Function.Surjective f) :
    Γ ⧸ K.comap f ≃ Δ ⧸ K :=
  Equiv.ofBijective (generatedFeasibleContainingCosetMap f K)
    (generatedFeasibleContainingCosetMap_bijective f K hf)

/-- Actual A elements whose projected geometry fixes the original rooted E8 section. -/
def generatedFeasibleContainingSectionPreimage :
    Subgroup (localAxisStabilizer generatedFeasibleContainingIncidentPair) :=
  generatedFeasibleContainingRootedCo1Flag.comap
    (localAxisStabilizerProjection generatedFeasibleContainingIncidentPair)

/-- Every whole-axis fixer fixes the actual projected rooted-section geometry. -/
theorem generatedFeasibleContaining_axis_le_section :
    generatedFeasibleContainingIncidentStabilizer ≤ generatedFeasibleContainingSectionPreimage := by
  intro a ha
  exact generatedFeasibleContainingIncident_projection_mem ⟨a, ha⟩

/-- Actual section cosets in A are equivalent to the complete genuine rooted E8 sections. -/
def generatedFeasibleContainingSectionCosetEquiv :
    (localAxisStabilizer generatedFeasibleContainingIncidentPair) ⧸
        generatedFeasibleContainingSectionPreimage ≃ generatedFeasibleContainingRootedSections :=
  (generatedFeasibleContainingCosetEquiv
    (localAxisStabilizerProjection generatedFeasibleContainingIncidentPair)
    generatedFeasibleContainingRootedCo1Flag
    (localAxisStabilizerProjection_surjective _)).trans
  ((generatedFeasibleContainingCosetEquiv generatedFeasibleContainingRootProjection
    generatedFeasibleContainingRootedCo1Flag
    generatedFeasibleContainingRootProjection_surjective).symm.trans
  ((Subgroup.quotientEquivOfEq generatedFeasibleContainingRootedFlag_preimage).trans
  ((MulAction.orbitEquivQuotientStabilizer generatedFeasibleContainingRootGroup
    (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))).symm.trans
    (Set.equivOfEq generatedFeasibleContainingRootedSections_orbit))))

/-- The coset geometry is the actual original section image of every matching spatial lift. -/
theorem generatedFeasibleContainingSectionCosetEquiv_apply
    (a : localAxisStabilizer generatedFeasibleContainingIncidentPair)
    (g : generatedFeasibleContainingRootGroup)
    (hg : generatedFeasibleContainingRootProjection g =
      localAxisStabilizerProjection generatedFeasibleContainingIncidentPair a) :
    (generatedFeasibleContainingSectionCosetEquiv (QuotientGroup.mk a)).val =
      generatedAxisE8ImageSection g.val (golayOctadWord generatedOctadBasisOctad) := by
  unfold generatedFeasibleContainingSectionPreimage
  unfold generatedFeasibleContainingSectionCosetEquiv
  simp only [Equiv.trans_apply]
  have ha : generatedFeasibleContainingCosetEquiv
      (localAxisStabilizerProjection generatedFeasibleContainingIncidentPair)
      generatedFeasibleContainingRootedCo1Flag
      (localAxisStabilizerProjection_surjective _)
      (QuotientGroup.mk a) =
    generatedFeasibleContainingCosetEquiv generatedFeasibleContainingRootProjection
      generatedFeasibleContainingRootedCo1Flag
      generatedFeasibleContainingRootProjection_surjective (QuotientGroup.mk g) := by
    change QuotientGroup.mk (localAxisStabilizerProjection _ a) =
      QuotientGroup.mk (generatedFeasibleContainingRootProjection g)
    rw [hg]
  rw [ha, Equiv.symm_apply_apply, Subgroup.quotientEquivOfEq_mk]
  rfl

/-- The actual geometric section quotient has exactly 56,925 values. -/
theorem generatedFeasibleContainingSectionPreimage_index :
    generatedFeasibleContainingSectionPreimage.index = 56925 := by
  rw [Subgroup.index_eq_card, Nat.card_congr generatedFeasibleContainingSectionCosetEquiv,
    generatedFeasibleContainingRootedSections_card]

/-- The original projection restricted to section fixers keeps the entire genuine flag image. -/
def generatedFeasibleContainingSectionProjection : generatedFeasibleContainingSectionPreimage →*
    generatedFeasibleContainingRootedCo1Flag :=
  ((localAxisStabilizerProjection generatedFeasibleContainingIncidentPair).comp
    generatedFeasibleContainingSectionPreimage.subtype).codRestrict _ (fun g => g.property)

/-- Every original projected flag admits an actual section-fixing A lift. -/
theorem generatedFeasibleContainingSectionProjection_surjective :
    Function.Surjective generatedFeasibleContainingSectionProjection := by
  intro b
  obtain ⟨a, ha⟩ := localAxisStabilizerProjection_surjective
    generatedFeasibleContainingIncidentPair b.val
  have hp : a ∈ generatedFeasibleContainingSectionPreimage := by
    change localAxisStabilizerProjection _ a ∈ generatedFeasibleContainingRootedCo1Flag
    rw [ha]
    exact b.property
  exact ⟨⟨a, hp⟩, Subtype.ext ha⟩

/-- Restriction to a preimage subgroup retains the entire actual projection kernel. -/
def generatedFeasibleContainingPreimageKernelEquiv {Γ Δ : Type*} [Group Γ] [Group Δ]
    (f : Γ →* Δ) (K : Subgroup Δ) :
    ((f.comp (K.comap f).subtype).codRestrict K (fun g => g.property)).ker ≃ f.ker where
  toFun g := ⟨g.val.val, congrArg Subtype.val g.property⟩
  invFun g := ⟨⟨g.val, by change f g.val ∈ K; rw [g.property]; exact K.one_mem⟩,
    Subtype.ext g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual section projection retains all 2^24 original first-fixed Q phases. -/
theorem generatedFeasibleContainingSectionProjection_kernel_card :
    Nat.card generatedFeasibleContainingSectionProjection.ker = 2 ^ 24 := by
  unfold generatedFeasibleContainingSectionProjection generatedFeasibleContainingSectionPreimage
  rw [Nat.card_congr (generatedFeasibleContainingPreimageKernelEquiv
    (localAxisStabilizerProjection generatedFeasibleContainingIncidentPair)
    generatedFeasibleContainingRootedCo1Flag)]
  exact localAxisStabilizerProjection_kernel_card _

/-- A subgroup included in another has the same elements under its nested subtype. -/
def generatedFeasibleContainingIncludedSubgroupEquiv {Γ : Type*} [Group Γ]
    (K R : Subgroup Γ) (hle : K ≤ R) : K.subgroupOf R ≃ K where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, hle g.property⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The entire genuine incident Co1 flag already fixes the original preferred root. -/
theorem generatedFeasibleContaining_flag_le_root :
    generatedFeasibleContainingIncidentFlag ≤
      co2ShortStabilizer (Sum.inl (0, generatedFeasibleContainingIncidentPair)) := by
  rintro c ⟨g, hg, rfl⟩
  change co1ShortPermutation (QuotientGroup.mk g) _ = _
  rw [co1ShortPermutation_mk]
  exact ((generatedAxisE8ShortFlagStabilizer_mem _ _ _).mp hg).2

/-- Viewing the genuine flag inside the root group preserves its actual order. -/
theorem generatedFeasibleContainingRootedCo1Flag_card :
    Nat.card generatedFeasibleContainingRootedCo1Flag = 743178240 := by
  unfold generatedFeasibleContainingRootedCo1Flag
  rw [Nat.card_congr (generatedFeasibleContainingIncludedSubgroupEquiv _ _
    generatedFeasibleContaining_flag_le_root)]
  exact generatedFeasibleContainingIncidentFlag_card

/-- The full section fixer contains all original first-fixed Q phases above the actual flag. -/
theorem generatedFeasibleContainingSectionPreimage_card :
    Nat.card generatedFeasibleContainingSectionPreimage = 2 ^ 24 * 743178240 := by
  have h := generatedFeasibleContainingSectionProjection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    generatedFeasibleContainingSectionProjection_surjective, Subgroup.card_top,
    generatedFeasibleContainingSectionProjection_kernel_card,
    generatedFeasibleContainingRootedCo1Flag_card] at h
  exact h.symm

/-- Each section has 128 whole-axis cosets from the actual 2^24 and 2^17 projection kernels. -/
theorem generatedFeasibleContainingSection_phase_cosets_card :
    Nat.card (generatedFeasibleContainingSectionPreimage ⧸
      generatedFeasibleContainingIncidentStabilizer.subgroupOf
        generatedFeasibleContainingSectionPreimage) = 128 := by
  have h := (generatedFeasibleContainingIncidentStabilizer.subgroupOf
    generatedFeasibleContainingSectionPreimage).card_mul_index
  rw [Nat.card_congr (generatedFeasibleContainingIncludedSubgroupEquiv _ _
    generatedFeasibleContaining_axis_le_section),
    generatedFeasibleContainingIncidentStabilizer_card,
    generatedFeasibleContainingSectionPreimage_card] at h
  change 97409858273280 * Nat.card (generatedFeasibleContainingSectionPreimage ⧸
    generatedFeasibleContainingIncidentStabilizer.subgroupOf
      generatedFeasibleContainingSectionPreimage) = 2 ^ 24 * 743178240 at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 97409858273280)
    (h.trans (by decide : 2 ^ 24 * 743178240 = 97409858273280 * 128))

/-- Every fiber of an actual subgroup-tower coset map is the corresponding relative quotient. -/
def generatedFeasibleContainingTowerFiberEquiv {Γ : Type*} [Group Γ]
    (K R : Subgroup Γ) (hle : K ≤ R) (y : Γ ⧸ R) :
    (Subgroup.quotientMapOfLE hle ⁻¹' {y}) ≃ R ⧸ K.subgroupOf R where
  toFun x := (Subgroup.quotientEquivProdOfLE hle x.val).2
  invFun z := ⟨(Subgroup.quotientEquivProdOfLE hle).symm (y, z), by
    change Subgroup.quotientMapOfLE hle _ = y
    change (Subgroup.quotientEquivProdOfLE hle
      ((Subgroup.quotientEquivProdOfLE hle).symm (y, z))).1 = y
    rw [Equiv.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply (Subgroup.quotientEquivProdOfLE hle).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact x.property.symm
    · rfl
  right_inv z := by
    change (Subgroup.quotientEquivProdOfLE hle
      ((Subgroup.quotientEquivProdOfLE hle).symm (y, z))).2 = z
    rw [Equiv.apply_symm_apply]

/-- The genuine whole-axis cosets project to their original rooted-section cosets. -/
def generatedFeasibleContainingAxisSectionCosetMap :
    (localAxisStabilizer generatedFeasibleContainingIncidentPair) ⧸
        generatedFeasibleContainingIncidentStabilizer →
      (localAxisStabilizer generatedFeasibleContainingIncidentPair) ⧸
        generatedFeasibleContainingSectionPreimage :=
  Subgroup.quotientMapOfLE generatedFeasibleContaining_axis_le_section

/-- Each genuine rooted-section coset has exactly 128 actual whole-axis phase lifts. -/
theorem generatedFeasibleContainingAxisSectionCosetMap_fiber_card
    (y : (localAxisStabilizer generatedFeasibleContainingIncidentPair) ⧸
      generatedFeasibleContainingSectionPreimage) :
    Nat.card (generatedFeasibleContainingAxisSectionCosetMap ⁻¹' {y}) = 128 := by
  unfold generatedFeasibleContainingAxisSectionCosetMap
  rw [Nat.card_congr (generatedFeasibleContainingTowerFiberEquiv _ _
    generatedFeasibleContaining_axis_le_section y),
    generatedFeasibleContainingSection_phase_cosets_card]

/-- Equivalences of the domain and target preserve the exact fibers of an actual map. -/
def generatedFeasibleContainingMapFiberEquiv {X X' Y Y' : Type*}
    (e : X ≃ X') (E : Y' ≃ Y) (f : X' → Y') (y : Y) :
    ((fun x => E (f (e x))) ⁻¹' {y}) ≃ (f ⁻¹' {E.symm y}) where
  toFun x := ⟨e x.val, by
    change f (e x.val) = E.symm y
    have h := congrArg E.symm x.property
    simpa only [Equiv.symm_apply_apply] using h⟩
  invFun x := ⟨e.symm x.val, by
    change E (f (e (e.symm x.val))) = y
    rw [Equiv.apply_symm_apply, x.property, Equiv.apply_symm_apply]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)

/-- The actual containing-axis orbit maps to its complete original rooted E8 geometry. -/
def generatedFeasibleContainingAxisRootedSectionMap :
    MulAction.orbit (localAxisStabilizer generatedFeasibleContainingIncidentPair)
        (generatedOctadLocalAxis 0 0) → generatedFeasibleContainingRootedSections :=
  fun x => generatedFeasibleContainingSectionCosetEquiv
    (generatedFeasibleContainingAxisSectionCosetMap
      (MulAction.orbitEquivQuotientStabilizer
        (localAxisStabilizer generatedFeasibleContainingIncidentPair)
        (generatedOctadLocalAxis 0 0) x))

/-- The vector-to-section map returns precisely the original fiber lift's section image. -/
theorem generatedFeasibleContainingAxisRootedSectionMap_image
    (a : localAxisStabilizer generatedFeasibleContainingIncidentPair)
    (f : localFiberSubgroup) (hf : localFiberIntoH f = a.val) :
    (generatedFeasibleContainingAxisRootedSectionMap
      ⟨rhoLocal a.val (generatedOctadLocalAxis 0 0), ⟨a, rfl⟩⟩).val =
        generatedAxisE8ImageSection f.val.2 (golayOctadWord generatedOctadBasisOctad) := by
  have hp : f.val.2 ∈ generatedFeasibleContainingRootGroup := by
    have hh := a.property
    rw [← hf] at hh
    exact ((localAxis_fiber_fixed_iff f generatedFeasibleContainingIncidentPair).mp hh).1
  let g : generatedFeasibleContainingRootGroup := ⟨f.val.2, hp⟩
  have hg : generatedFeasibleContainingRootProjection g =
      localAxisStabilizerProjection generatedFeasibleContainingIncidentPair a := by
    apply Subtype.ext
    change QuotientGroup.mk' signsSubgroup f.val.2 = projH a.val
    rw [← hf]
    rfl
  have hcoset : MulAction.orbitEquivQuotientStabilizer
      (localAxisStabilizer generatedFeasibleContainingIncidentPair)
      (generatedOctadLocalAxis 0 0)
      ⟨rhoLocal a.val (generatedOctadLocalAxis 0 0), ⟨a, rfl⟩⟩ = QuotientGroup.mk a := by
    apply (MulAction.orbitEquivQuotientStabilizer
      (localAxisStabilizer generatedFeasibleContainingIncidentPair)
      (generatedOctadLocalAxis 0 0)).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    rfl
  unfold generatedFeasibleContainingAxisRootedSectionMap
  rw [hcoset]
  change (generatedFeasibleContainingSectionCosetEquiv (QuotientGroup.mk a)).val = _
  exact generatedFeasibleContainingSectionCosetEquiv_apply a g hg

/-- Every one of the 56,925 actual rooted sections has 128 original whole-axis vectors above it. -/
theorem generatedFeasibleContainingAxisRootedSectionMap_fiber_card
    (S : generatedFeasibleContainingRootedSections) :
    Nat.card (generatedFeasibleContainingAxisRootedSectionMap ⁻¹' {S}) = 128 := by
  unfold generatedFeasibleContainingAxisRootedSectionMap
  rw [Nat.card_congr (generatedFeasibleContainingMapFiberEquiv
    (MulAction.orbitEquivQuotientStabilizer
      (localAxisStabilizer generatedFeasibleContainingIncidentPair)
      (generatedOctadLocalAxis 0 0))
    generatedFeasibleContainingSectionCosetEquiv
    generatedFeasibleContainingAxisSectionCosetMap S),
    generatedFeasibleContainingAxisSectionCosetMap_fiber_card]

/-- The genuine orbit-to-section map attains every original rooted section. -/
theorem generatedFeasibleContainingAxisRootedSectionMap_surjective :
    Function.Surjective generatedFeasibleContainingAxisRootedSectionMap := by
  intro S
  have h := generatedFeasibleContainingAxisRootedSectionMap_fiber_card S
  have hp : 0 < Nat.card (generatedFeasibleContainingAxisRootedSectionMap ⁻¹' {S}) := by
    rw [h]
    decide
  obtain ⟨x⟩ := Nat.card_pos_iff.mp hp |>.1
  exact ⟨x.val, x.property⟩


/-- Genuine source transport sends every original orbit vector to the old-axis orbit. -/
def generatedFeasibleContainingSourceOrbitEquiv (h : H)
    (hfirst : rhoLocal h
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0)
    (hdest : rhoLocal h generatedFeasibleContainingOctadDestination =
      generatedOctadLocalAxis 0 0) :
    MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination ≃
      MulAction.orbit (localAxisStabilizer generatedFeasibleContainingIncidentPair)
        (generatedOctadLocalAxis 0 0) where
  toFun x := ⟨rhoLocal h x.val, by
    obtain ⟨a, ha⟩ := x.property
    have hfix : rhoLocal a.val
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact a.property
    have hk : h * a.val * h⁻¹ ∈ localAxisStabilizer generatedFeasibleContainingIncidentPair := by
      change rhoLocal (h * a.val * h⁻¹)
        (conwayAxis generatedFeasibleContainingIncidentPair) =
          conwayAxis generatedFeasibleContainingIncidentPair
      simpa only [conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h a.val _ _ hfirst hfix
    refine ⟨⟨h * a.val * h⁻¹, hk⟩, ?_⟩
    change rhoLocal (h * a.val * h⁻¹) (generatedOctadLocalAxis 0 0) = rhoLocal h x.val
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      generatedFeasibleContaining_inverse_transports h _ _ hdest]
    change rhoLocal h (rhoLocal a.val generatedFeasibleContainingOctadDestination) = _
    change rhoLocal a.val generatedFeasibleContainingOctadDestination = x.val at ha
    rw [ha]⟩
  invFun x := ⟨rhoLocal h⁻¹ x.val, by
    obtain ⟨a, ha⟩ := x.property
    have hfix : rhoLocal a.val
        (conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact a.property
    have hk : h⁻¹ * a.val * h ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
      change rhoLocal (h⁻¹ * a.val * h) (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair
      have hi := generatedFeasibleContaining_inverse_transports h _ _ hfirst
      simpa only [inv_inv, conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h⁻¹ a.val _ _ hi hfix
    refine ⟨⟨h⁻¹ * a.val * h, hk⟩, ?_⟩
    change rhoLocal (h⁻¹ * a.val * h) generatedFeasibleContainingOctadDestination =
      rhoLocal h⁻¹ x.val
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdest]
    change rhoLocal a.val (generatedOctadLocalAxis 0 0) = x.val at ha
    rw [ha]⟩
  left_inv x := by
    apply Subtype.ext
    change rhoLocal h⁻¹ (rhoLocal h x.val) = x.val
    rw [map_inv]
    exact (rhoLocal h).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    change rhoLocal h (rhoLocal h⁻¹ x.val) = x.val
    rw [map_inv]
    exact (rhoLocal h).apply_symm_apply x.val

/-- The original source containing orbit has a genuine rooted-section map with 128-vector fibers. -/
theorem generatedFeasibleContainingSourceRootedSectionMap_exists :
    ∃ f : MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination → generatedFeasibleContainingRootedSections,
      Function.Surjective f ∧ ∀ S, Nat.card (f ⁻¹' {S}) = 128 := by
  obtain ⟨h, hfirst, hdest⟩ := generatedFeasibleContaining_source_transport
  let e := generatedFeasibleContainingSourceOrbitEquiv h hfirst hdest
  let f := fun x => generatedFeasibleContainingAxisRootedSectionMap (e x)
  have hf (S : generatedFeasibleContainingRootedSections) : Nat.card (f ⁻¹' {S}) = 128 := by
    change Nat.card ((fun x => (Equiv.refl generatedFeasibleContainingRootedSections)
      (generatedFeasibleContainingAxisRootedSectionMap (e x))) ⁻¹' {S}) = 128
    rw [Nat.card_congr (generatedFeasibleContainingMapFiberEquiv e
      (Equiv.refl generatedFeasibleContainingRootedSections)
      generatedFeasibleContainingAxisRootedSectionMap S)]
    exact generatedFeasibleContainingAxisRootedSectionMap_fiber_card S
  refine ⟨f, ?_, hf⟩
  intro S
  obtain ⟨x, hx⟩ := generatedFeasibleContainingAxisRootedSectionMap_surjective S
  refine ⟨e.symm x, ?_⟩
  change generatedFeasibleContainingAxisRootedSectionMap (e (e.symm x)) = S
  rw [Equiv.apply_symm_apply]
  exact hx


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
