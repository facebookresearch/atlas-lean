/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameFlagsOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Co1StabilizerCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Exact Co0 and Co1 stabilizers of genuine E8-section/frame-class flags. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full actual stabilizer of a coordinate E8 section and an incident frame class. -/
def generatedAxisE8FrameFlagsStabilizer (o : Fin 759) (b : LeechModTwo) :
    Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o), b)

/-- Membership fixes both original geometric components. -/
theorem generatedAxisE8FrameFlagsStabilizer_mem (o : Fin 759) (b : LeechModTwo)
    (g : leechIsomSubgroup) :
    g ∈ generatedAxisE8FrameFlagsStabilizer o b ↔
      generatedAxisE8ImageSection g (golayOctadWord o) =
        generatedAxisE8CoordinateSection (golayOctadWord o) ∧
      leechModTwoAction g b = b := Prod.ext_iff

/-- The actual group-action orbit equals the proved pair-image range. -/
theorem generatedAxisE8FrameFlags_action_orbit (o : Fin 759) (b : LeechModTwo) :
    MulAction.orbit leechIsomSubgroup
      (generatedAxisE8CoordinateSection (golayOctadWord o), b) =
        generatedAxisE8FrameFlagsOrbit o b := rfl

/-- Every genuine incident section-frame flag has Co0 stabilizer order 1321205760. -/
theorem generatedAxisE8FrameFlagsStabilizer_card (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (generatedAxisE8FrameFlagsStabilizer o b) = 1321205760 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let x := (generatedAxisE8CoordinateSection (golayOctadWord o), b)
  let f : leechIsomSubgroup → MulAction.orbit leechIsomSubgroup x :=
    fun g => ⟨g • x, ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨S, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit leechIsomSubgroup x) := Finite.of_surjective f hf
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup x)
  let _ := Fintype.ofFinite (MulAction.stabilizer leechIsomSubgroup x)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group leechIsomSubgroup x
  simp only [← Nat.card_eq_fintype_card] at h
  change Nat.card (MulAction.orbit leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o), b)) *
      Nat.card (generatedAxisE8FrameFlagsStabilizer o b) = Nat.card leechIsomSubgroup at h
  rw [generatedAxisE8FrameFlags_action_orbit, generatedAxisE8FrameFlagsOrbit_card o b hb,
    co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 6293912625)
    (h.trans (by decide : 8315553613086720000 = 6293912625 * 1321205760))

set_option maxHeartbeats 2000000 in
-- Transport through the concrete lattice coordinates requires additional elaboration.
/-- Both central lattice signs fix both components of every actual section-frame flag. -/
theorem generatedAxisE8FrameFlags_signs_le (o : Fin 759) (b : LeechModTwo) :
    signsSubgroup ≤ generatedAxisE8FrameFlagsStabilizer o b := by
  intro g hg
  rw [generatedAxisE8FrameFlagsStabilizer_mem]
  refine ⟨(generatedAxisE8SectionStabilizer_mem _ g).mp
    (generatedAxisE8_signs_le_section_stabilizer _ hg), ?_⟩
  have h := congrArg (fun f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) =>
    f (leechHyperbolicCoordinates b)) (leechBinaryAction_sign g hg)
  simp only [leechBinaryAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.coe_one, id_eq] at h
  exact leechHyperbolicCoordinates.injective h

/-- The genuine section-frame flag stabilizer in the actual central-sign quotient. -/
def generatedAxisE8FrameFlagsCo1Stabilizer (o : Fin 759) (b : LeechModTwo) : Subgroup Co1 :=
  (generatedAxisE8FrameFlagsStabilizer o b).map (QuotientGroup.mk' signsSubgroup)

/-- The genuine Co0 section-frame flag stabilizer has index 6293912625. -/
theorem generatedAxisE8FrameFlagsStabilizer_index (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    (generatedAxisE8FrameFlagsStabilizer o b).index = 6293912625 := by
  have h := (generatedAxisE8FrameFlagsStabilizer o b).card_mul_index
  rw [generatedAxisE8FrameFlagsStabilizer_card o b hb, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1321205760)
    (h.trans (by decide : 8315553613086720000 = 1321205760 * 6293912625))

/-- The central-sign quotient preserves the exact genuine flag index. -/
theorem generatedAxisE8FrameFlagsCo1Stabilizer_index (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    (generatedAxisE8FrameFlagsCo1Stabilizer o b).index = 6293912625 := by
  change ((generatedAxisE8FrameFlagsStabilizer o b).map
    (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedAxisE8FrameFlagsStabilizer_index o b hb
  · rw [QuotientGroup.ker_mk']
    exact generatedAxisE8FrameFlags_signs_le o b

/-- The actual Co1 flag stabilizer has order 660602880. -/
theorem generatedAxisE8FrameFlagsCo1Stabilizer_card (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (generatedAxisE8FrameFlagsCo1Stabilizer o b) = 660602880 := by
  have h := (generatedAxisE8FrameFlagsCo1Stabilizer o b).card_mul_index
  rw [generatedAxisE8FrameFlagsCo1Stabilizer_index o b hb, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 6293912625)
    (h.trans (by decide : 4157776806543360000 = 660602880 * 6293912625))

/-- Through the original frame class, the full flag stabilizer is the monomial section fixer. -/
theorem generatedAxisE8FrameFlags_frame_zero_mem_iff (o : Fin 759) (g : leechIsomSubgroup) :
    g ∈ generatedAxisE8FrameFlagsStabilizer o
      (leechReduction (leechCoordinateFrameLattice 0)) ↔
    g ∈ generatedAxisE8SectionStabilizer (golayOctadWord o) ∧ g ∈ golayMonomialSubgroup := by
  rw [generatedAxisE8FrameFlagsStabilizer_mem, ← generatedAxisE8SectionStabilizer_mem,
    ← leechFrameClass_stabilizer_eq_monomial]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
