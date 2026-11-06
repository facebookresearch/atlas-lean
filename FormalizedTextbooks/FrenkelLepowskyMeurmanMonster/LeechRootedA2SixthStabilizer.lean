/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2TwoRootFlags
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpatialStabilizer

/-! Exact orders of the genuine sixth-axis spatial rooted-plane/root-line stabilizers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Equality of a real plane image is precisely setwise preservation by the actual isometry. -/
theorem leechRootedA2_map_preserves_iff (S : Submodule ℝ (Fin 24 → ℝ))
    (e : leechIsomSubgroup) :
    S.map e.val.toLinearMap = S ↔ ∀ x, x ∈ S ↔ e.val x ∈ S := by
  constructor
  · intro h x
    constructor
    · intro hx
      have hy : e.val x ∈ S.map e.val.toLinearMap := Submodule.mem_map_of_mem hx
      rwa [h] at hy
    · intro hx
      rw [← h] at hx
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hx
      have he : v = x := e.val.injective hvx
      rwa [he] at hv
  · intro h
    apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hx
      rw [← hvx]
      exact (h v).mp hv
    · intro x hx
      apply Submodule.mem_map.mpr
      refine ⟨e.val.symm x, ?_, e.val.apply_symm_apply x⟩
      apply (h (e.val.symm x)).mpr
      simpa only [e.val.apply_symm_apply] using hx

/-- The actual sixth spatial subgroup is exactly the stabilizer of its original two-root flag. -/
theorem leechRootedA2SixthSpatialStabilizer_eq :
    generatedSixthSpatialStabilizer =
      MulAction.stabilizer leechIsomSubgroup (generatedSixthRootedPlane,
        generatedSixthPlaneShort) := by
  ext g
  rw [generatedSixthSpatialStabilizer_mem]
  change _ ↔ g • (generatedSixthRootedPlane, generatedSixthPlaneShort) =
    (generatedSixthRootedPlane, generatedSixthPlaneShort)
  rw [Prod.ext_iff]
  change _ ↔ generatedSixthRootedPlane.map g.val.toLinearMap = generatedSixthRootedPlane ∧
    griessShortPermutation g generatedSixthPlaneShort = generatedSixthPlaneShort
  rw [leechRootedA2_map_preserves_iff]

/-- The full actual sixth-axis spatial stabilizer has36787322880 elements in Co0. -/
theorem generatedSixthSpatialStabilizer_card : Nat.card generatedSixthSpatialStabilizer =
    36787322880 := by
  rw [leechRootedA2SixthSpatialStabilizer_eq, generatedSixthRootedPlane]
  exact leechRootedA2TwoRootFlag_stabilizer_card generatedSixthPlaneShort
    generatedSixthPlaneSecondShort generatedSixth_plane_lattice_roots.2.2

/-- Both genuine lattice signs preserve the actual sixth spatial flag. -/
theorem generatedSixthSpatialStabilizer_signs :
    signsSubgroup ≤ generatedSixthSpatialStabilizer := by
  intro g hg
  rw [generatedSixthSpatialStabilizer_mem]
  have hb : leechBinaryAction g = 1 := by
    change g ∈ leechBinaryAction.ker
    rwa [leechBinaryAction_ker]
  refine ⟨?_, griessShortPermutation_binary_trivial g hb generatedSixthPlaneShort⟩
  intro x
  rcases hg with hg | hg
  · rw [hg]
    rfl
  · rw [hg x]
    exact (Submodule.neg_mem_iff _).symm

/-- The full actual sixth spatial stabilizer has index226044000 in Co0. -/
theorem generatedSixthSpatialStabilizer_index : generatedSixthSpatialStabilizer.index =
    226044000 := by
  have h := generatedSixthSpatialStabilizer.card_mul_index
  rw [generatedSixthSpatialStabilizer_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 36787322880)
    (h.trans (by decide : 8315553613086720000 = 36787322880 * 226044000))

/-- The central-sign quotient retains the actual sixth spatial flag stabilizer index. -/
theorem generatedSixthCo1SpatialStabilizer_index : generatedSixthCo1SpatialStabilizer.index =
    226044000 := by
  change (generatedSixthSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedSixthSpatialStabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedSixthSpatialStabilizer_signs

/-- The full actual sixth-axis spatial rooted-flag stabilizer has18393661440 elements in Co1. -/
theorem generatedSixthCo1SpatialStabilizer_card : Nat.card generatedSixthCo1SpatialStabilizer =
    18393661440 := by
  have h := generatedSixthCo1SpatialStabilizer.card_mul_index
  rw [generatedSixthCo1SpatialStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 226044000)
    (h.trans (by decide : 4157776806543360000 = 18393661440 * 226044000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
