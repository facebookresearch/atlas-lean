/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2RootStabilizer

/-! Exact actual Conway stabilizers of a rooted A2 plane and its distinguished root line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine root-line subgroup acts on the actual rooted planes by real submodule images. -/
instance : MulAction leechRootedA2RootLineSubgroup leechRootedA2Plane where
  smul g p := ⟨p.val.map g.val.val.toLinearMap, leechRootedA2Plane_map_mem g.val
    ((leechRootedA2RootLineSubgroup_mem g.val).mp g.property) p⟩
  one_smul p := by
    apply Subtype.ext
    change p.val.map LinearMap.id = p.val
    exact Submodule.map_id _
  mul_smul g h p := by
    apply Subtype.ext
    change p.val.map (g * h).val.val.toLinearMap =
      (p.val.map h.val.val.toLinearMap).map g.val.val.toLinearMap
    rw [← Submodule.map_comp]
    rfl

/-- Actual rooted-plane transitivity makes each plane orbit the entire counted plane set. -/
theorem leechRootedA2Plane_action_orbit (p : leechRootedA2Plane) :
    MulAction.orbit leechRootedA2RootLineSubgroup p = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro q
  obtain ⟨e, he, heq⟩ := leechRootedA2Plane_transitive p q
  exact ⟨⟨e, (leechRootedA2RootLineSubgroup_mem e).mpr he⟩, Subtype.ext heq⟩

/-- Every actual plane orbit in the genuine root-line subgroup has2300 elements. -/
theorem leechRootedA2Plane_action_orbit_card (p : leechRootedA2Plane) :
    Nat.card (MulAction.orbit leechRootedA2RootLineSubgroup p) = 2300 := by
  rw [leechRootedA2Plane_action_orbit, Nat.card_univ, Nat.card_eq_fintype_card,
    leechRootedA2Plane_card]

/-- The genuine plane stabilizer inside the actual root-line subgroup. -/
def leechRootedA2PlaneRootStabilizer (p : leechRootedA2Plane) :
    Subgroup leechRootedA2RootLineSubgroup := MulAction.stabilizer leechRootedA2RootLineSubgroup p

/-- The full actual rooted-plane stabilizer has36787322880 elements. -/
theorem leechRootedA2PlaneRootStabilizer_card (p : leechRootedA2Plane) :
    Nat.card (leechRootedA2PlaneRootStabilizer p) = 36787322880 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite leechRootedA2RootLineSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechRootedA2RootLineSubgroup p)
  let _ := Fintype.ofFinite (leechRootedA2PlaneRootStabilizer p)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    leechRootedA2RootLineSubgroup p
  simp only [← Nat.card_eq_fintype_card] at h
  change Nat.card (MulAction.orbit leechRootedA2RootLineSubgroup p) *
    Nat.card (leechRootedA2PlaneRootStabilizer p) = Nat.card leechRootedA2RootLineSubgroup at h
  rw [leechRootedA2Plane_action_orbit_card, leechRootedA2RootLineSubgroup_card] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2300)
    (h.trans (by decide : 84610842624000 = 2300 * 36787322880))

/-- The same actual plane and root-line stabilizer viewed as a subgroup of the full Conway group. -/
def leechRootedA2FlagStabilizer (p : leechRootedA2Plane) : Subgroup leechIsomSubgroup :=
  (leechRootedA2PlaneRootStabilizer p).map leechRootedA2RootLineSubgroup.subtype

/-- Actual global flag membership fixes the root line and real rooted plane. -/
theorem leechRootedA2FlagStabilizer_mem (p : leechRootedA2Plane) (e : leechIsomSubgroup) :
    e ∈ leechRootedA2FlagStabilizer p ↔ leechRootedA2PreservesRootLine e ∧
      p.val.map e.val.toLinearMap = p.val := by
  constructor
  · rintro ⟨g, hg, hge⟩
    change g.val = e at hge
    subst e
    refine ⟨(leechRootedA2RootLineSubgroup_mem g.val).mp g.property, ?_⟩
    change g • p = p at hg
    exact congrArg Subtype.val hg
  · rintro ⟨he, hp⟩
    let g : leechRootedA2RootLineSubgroup := ⟨e,
      (leechRootedA2RootLineSubgroup_mem e).mpr he⟩
    exact ⟨g, Subtype.ext hp, rfl⟩

/-- Viewing the actual rooted stabilizer inside full Co0 preserves its exact order. -/
theorem leechRootedA2FlagStabilizer_card (p : leechRootedA2Plane) :
    Nat.card (leechRootedA2FlagStabilizer p) = 36787322880 := by
  rw [leechRootedA2FlagStabilizer, Subgroup.card_subtype, leechRootedA2PlaneRootStabilizer_card]

/-- The genuine rooted-plane/root-line flag stabilizer has index226044000 in Co0. -/
theorem leechRootedA2FlagStabilizer_index (p : leechRootedA2Plane) :
    (leechRootedA2FlagStabilizer p).index = 226044000 := by
  have h := (leechRootedA2FlagStabilizer p).card_mul_index
  rw [leechRootedA2FlagStabilizer_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 36787322880)
    (h.trans (by decide : 8315553613086720000 = 36787322880 * 226044000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
