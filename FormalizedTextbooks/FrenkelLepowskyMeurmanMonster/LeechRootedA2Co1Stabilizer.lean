/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PlaneStabilizer

/-! Exact rooted-plane/root-line stabilizer order in the genuine central-sign Conway quotient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both genuine central lattice signs preserve every actual rooted-plane/root-line flag. -/
theorem leechRootedA2_signs_le_flagStabilizer (p : leechRootedA2Plane) :
    signsSubgroup ≤ leechRootedA2FlagStabilizer p := by
  intro e he
  apply (leechRootedA2FlagStabilizer_mem p e).mpr
  have hb : leechBinaryAction e = 1 := by
    change e ∈ leechBinaryAction.ker
    rwa [leechBinaryAction_ker]
  refine ⟨(leechRootedA2RootLineSubgroup_mem e).mp
    (griessShortPermutation_binary_trivial e hb leechRootedA2RootAddress), ?_⟩
  rcases he with he | he
  · have hi : e = 1 := Subtype.ext he
    subst e
    change p.val.map LinearMap.id = p.val
    exact Submodule.map_id _
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hx
      rw [← hvx]
      change e.val v ∈ p.val
      rw [he v]
      exact p.val.neg_mem hv
    · intro x hx
      apply Submodule.mem_map.mpr
      refine ⟨-x, p.val.neg_mem hx, ?_⟩
      change e.val (-x) = x
      rw [he, neg_neg]

/-- The actual rooted-plane/root-line stabilizer in the central-sign quotient Co1. -/
def leechRootedA2Co1FlagStabilizer (p : leechRootedA2Plane) : Subgroup Co1 :=
  (leechRootedA2FlagStabilizer p).map (QuotientGroup.mk' signsSubgroup)

/-- The genuine central-sign quotient preserves the actual rooted-flag stabilizer index. -/
theorem leechRootedA2Co1FlagStabilizer_index (p : leechRootedA2Plane) :
    (leechRootedA2Co1FlagStabilizer p).index = 226044000 := by
  change ((leechRootedA2FlagStabilizer p).map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact leechRootedA2FlagStabilizer_index p
  · rw [QuotientGroup.ker_mk']
    exact leechRootedA2_signs_le_flagStabilizer p

/-- The full actual Co1 rooted-plane/root-line stabilizer has18393661440 elements. -/
theorem leechRootedA2Co1FlagStabilizer_card (p : leechRootedA2Plane) :
    Nat.card (leechRootedA2Co1FlagStabilizer p) = 18393661440 := by
  have h := (leechRootedA2Co1FlagStabilizer p).card_mul_index
  rw [leechRootedA2Co1FlagStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 226044000)
    (h.trans (by decide : 4157776806543360000 = 18393661440 * 226044000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
