/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! The exact genuine feasible-axis transition coset count. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The nested local Ω-axis stabilizer is the genuine intersection subgroup in H. -/
noncomputable def localOmegaAxisIntersectionEquiv (p : Fin 276) :
    MulAction.stabilizer localOmegaStabilizer (conwayAxis p) ≃*
      ↥((localAxisStabilizer p ⊓ localOmegaStabilizer) : Subgroup H) where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun y := ⟨⟨y.val, y.property.2⟩, y.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual common local Ω-axis stabilizer has its exact numerical order. -/
theorem localOmegaAxisIntersection_card (p : Fin 276) :
    Nat.card ↥((localAxisStabilizer p ⊓ localOmegaStabilizer) : Subgroup H) =
      7619615580487680 := by
  have h := (MulAction.stabilizer localOmegaStabilizer (conwayAxis p)).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq,
    generatedAxis_localOmega_pair_orbit_card,
    Nat.card_congr (localOmegaAxisIntersectionEquiv p).toEquiv] at h
  have hN : Nat.card localOmegaStabilizer = 8412055600858398720 := by
    rw [localOmegaStabilizer_card, co1OmegaFrameStabilizer_card]
    norm_num
  rw [hN] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1104) h

/-- The genuine transition subgroup inside the actual first-axis stabilizer. -/
noncomputable def localFeasibleTransitionSubgroup (p : Fin 276) :
    Subgroup (localAxisStabilizer p) := localOmegaStabilizer.subgroupOf (localAxisStabilizer p)

/-- The feasible transition subgroup and the genuine intersection count the same elements. -/
noncomputable def localFeasibleTransitionEquiv (p : Fin 276) :
    localFeasibleTransitionSubgroup p ≃*
      ↥((localAxisStabilizer p ⊓ localOmegaStabilizer) : Subgroup H) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun y := ⟨⟨y.val, y.property.1⟩, y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual feasible-axis transition coset domain has exactly 93,150 elements. -/
theorem localFeasibleTransitionSubgroup_index (p : Fin 276) :
    (localFeasibleTransitionSubgroup p).index = 93150 := by
  have h := (localFeasibleTransitionSubgroup p).card_mul_index
  rw [Nat.card_congr (localFeasibleTransitionEquiv p).toEquiv,
    localOmegaAxisIntersection_card] at h
  have hA : Nat.card (localAxisStabilizer p) = 709767191322427392000 := by
    rw [localAxisStabilizer_card, co2Short_card_exact]
    norm_num
  rw [hA] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7619615580487680) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
