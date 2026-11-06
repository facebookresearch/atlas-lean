/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadOrbitCount

/-! The complete genuine rooted E8 geometry underlying the containing feasible orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual full Co0 stabilizer of the original incident preferred root. -/
def generatedFeasibleContainingRootGroup : Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup
    (Sum.inl (0, generatedFeasibleContainingIncidentPair) : GriessShortIndex)

/-- Genuine E8 sections containing the fixed original incident root. -/
def generatedFeasibleContainingRootedSections : Set (Submodule ℤ leechIntegral) :=
  {S | S ∈ generatedAxisE8SectionOrbit (golayOctadWord generatedOctadBasisOctad) ∧
    Sum.inl (0, generatedFeasibleContainingIncidentPair) ∈ generatedAxisE8ShortLines S}

/-- The actual incident preferred root is contained in the original old E8 section. -/
theorem generatedFeasibleContainingRootedSections_initial :
    generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad) ∈
      generatedFeasibleContainingRootedSections :=
  ⟨⟨1, generatedAxisE8SectionEquiv_one _⟩,
    generatedFeasibleContainingIncident_short_mem⟩

/-- Every actual rooted section is reached by an original root-fixing lattice isometry. -/
theorem generatedFeasibleContainingRootedSections_orbit :
    MulAction.orbit generatedFeasibleContainingRootGroup
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) =
        generatedFeasibleContainingRootedSections := by
  ext S
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨⟨g.val, rfl⟩, ?_⟩
    have hm := (generatedAxisE8ShortLines_image_mem g.val
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))
      (Sum.inl (0, generatedFeasibleContainingIncidentPair))).mpr
        generatedFeasibleContainingIncident_short_mem
    change griessShortPermutation g.val _ ∈ _ at hm
    rw [show griessShortPermutation g.val
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
        Sum.inl (0, generatedFeasibleContainingIncidentPair) from g.property] at hm
    exact hm
  · rintro ⟨hS, hr⟩
    obtain ⟨g, hgS, hgr⟩ := generatedAxisE8Short_flags_transitive
      generatedOctadBasisOctad (Sum.inl (0, generatedFeasibleContainingIncidentPair))
      generatedFeasibleContainingIncident_short_mem S
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) hS hr
    exact ⟨⟨g, hgr⟩, hgS⟩

/-- The original preferred-root group has its actual Co0 order, including both signs. -/
theorem generatedFeasibleContainingRootGroup_card :
    Nat.card generatedFeasibleContainingRootGroup = 84610842624000 := by
  have horbit : MulAction.orbit leechIsomSubgroup
      (Sum.inl (0, generatedFeasibleContainingIncidentPair) : GriessShortIndex) =
        Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro r
    obtain ⟨g, _, hg⟩ := leechShort_concrete_label_transitive
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) r
    exact ⟨g, hg⟩
  have h := generatedFeasibleContainingRootGroup.card_mul_index
  have hi : generatedFeasibleContainingRootGroup.index = 98280 := by
    rw [generatedFeasibleContainingRootGroup, MulAction.index_stabilizer,
      ← Nat.card_coe_set_eq, horbit, Nat.card_univ, Nat.card_eq_fintype_card,
      griessShortIndex_card]
  rw [hi, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 98280)
    (h.trans (by decide : 8315553613086720000 = 84610842624000 * 98280))

/-- The rooted section point group is precisely the entire original incident flag group. -/
def generatedFeasibleContainingRootedSectionStabilizerEquiv :
    MulAction.stabilizer generatedFeasibleContainingRootGroup
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) ≃
        generatedAxisE8ShortFlagStabilizer generatedOctadBasisOctad
          (Sum.inl (0, generatedFeasibleContainingIncidentPair)) where
  toFun g := ⟨g.val.val,
    (generatedAxisE8ShortFlagStabilizer_mem _ _ _).mpr ⟨g.property, g.val.property⟩⟩
  invFun g := ⟨⟨g.val,
    ((generatedAxisE8ShortFlagStabilizer_mem _ _ _).mp g.property).2⟩,
    ((generatedAxisE8ShortFlagStabilizer_mem _ _ _).mp g.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly 56,925 genuine rooted E8 sections form the entire actual root-group orbit. -/
theorem generatedFeasibleContainingRootedSections_card :
    Nat.card generatedFeasibleContainingRootedSections = 56925 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite generatedFeasibleContainingRootGroup
  let _ := Fintype.ofFinite (MulAction.stabilizer generatedFeasibleContainingRootGroup
    (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)))
  let orbitMap : generatedFeasibleContainingRootGroup →
      MulAction.orbit generatedFeasibleContainingRootGroup
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) :=
    fun g => ⟨g • _, ⟨g, rfl⟩⟩
  have hm : Function.Surjective orbitMap := by
    rintro ⟨S, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit generatedFeasibleContainingRootGroup
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) :=
    Finite.of_surjective orbitMap hm
  let _ := Fintype.ofFinite (MulAction.orbit generatedFeasibleContainingRootGroup
    (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)))
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedFeasibleContainingRootGroup
    (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedFeasibleContainingRootedSections_orbit,
    Nat.card_congr generatedFeasibleContainingRootedSectionStabilizerEquiv,
    generatedAxisE8ShortFlagStabilizer_card _ _
      generatedFeasibleContainingIncident_short_mem,
    generatedFeasibleContainingRootGroup_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1486356480)
    (h.trans (by decide : 84610842624000 = 56925 * 1486356480))

/-- The actual incident Co1 flag, viewed inside the actual preferred-root stabilizer. -/
def generatedFeasibleContainingRootedCo1Flag :
    Subgroup (co2ShortStabilizer (Sum.inl (0, generatedFeasibleContainingIncidentPair))) :=
  generatedFeasibleContainingIncidentFlag.subgroupOf _

/-- Original root-fixing isometries project to genuine preferred-root-fixing Co1 elements. -/
theorem generatedFeasibleContainingRootProjection_mem (g : generatedFeasibleContainingRootGroup) :
    QuotientGroup.mk' signsSubgroup g.val ∈
      co2ShortStabilizer (Sum.inl (0, generatedFeasibleContainingIncidentPair)) := by
  change co1ShortPermutation (QuotientGroup.mk g.val) _ = _
  rw [co1ShortPermutation_mk]
  exact g.property

/-- The genuine central-sign quotient of the entire original incident root group. -/
def generatedFeasibleContainingRootProjection : generatedFeasibleContainingRootGroup →*
    co2ShortStabilizer (Sum.inl (0, generatedFeasibleContainingIncidentPair)) :=
  ((QuotientGroup.mk' signsSubgroup).comp
    generatedFeasibleContainingRootGroup.subtype).codRestrict _
      generatedFeasibleContainingRootProjection_mem

/-- Every actual root-fixing Co1 element lifts to an actual root-fixing Co0 isometry. -/
theorem generatedFeasibleContainingRootProjection_surjective :
    Function.Surjective generatedFeasibleContainingRootProjection := by
  intro c
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective signsSubgroup c.val
  have hp : g ∈ generatedFeasibleContainingRootGroup := by
    have h := c.property
    change co1ShortPermutation c.val _ = _ at h
    rw [← hg] at h
    change co1ShortPermutation (QuotientGroup.mk g) _ = _ at h
    rw [co1ShortPermutation_mk] at h
    exact h
  exact ⟨⟨g, hp⟩, Subtype.ext hg⟩

/-- Pulling the genuine Co1 flag back gives the entire actual rooted-section point group. -/
theorem generatedFeasibleContainingRootedFlag_preimage :
    generatedFeasibleContainingRootedCo1Flag.comap generatedFeasibleContainingRootProjection =
      MulAction.stabilizer generatedFeasibleContainingRootGroup
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
  have he : generatedFeasibleContainingIncidentFlag.comap (QuotientGroup.mk' signsSubgroup) =
      generatedAxisE8ShortFlagStabilizer generatedOctadBasisOctad
        (Sum.inl (0, generatedFeasibleContainingIncidentPair)) := by
    change (Subgroup.map (QuotientGroup.mk' signsSubgroup) _).comap _ = _
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (generatedAxisE8Short_signs_le_flagStabilizer _ _)]
  ext g
  change QuotientGroup.mk' signsSubgroup g.val ∈ generatedFeasibleContainingIncidentFlag ↔ _
  change g.val ∈ generatedFeasibleContainingIncidentFlag.comap
    (QuotientGroup.mk' signsSubgroup) ↔ _
  rw [he, generatedAxisE8ShortFlagStabilizer_mem]
  exact and_iff_left g.property


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
