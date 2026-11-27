/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27

namespace MathlibExtTest.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27

open MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27Wanted

-- Some finite group has a strictly smaller subgroup whose automorphism group has the same order.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G),
    Nat.card H < Nat.card G ∧ Nat.card (MulAut H) = Nat.card (MulAut G) := by
  obtain ⟨-, -, G, _, _, -, -, H, hH, ⟨e⟩⟩ := autIsoAutOfProperSubgroup_holds
  exact ⟨G, inferInstance, inferInstance, H,
    H.card_le_card_group.lt_of_ne (mt H.card_eq_iff_eq_top.mp hH),
    (Nat.card_congr e.toEquiv).symm⟩

-- The condition `H ≠ ⊤` is needed: the cyclic group of order three, with `H` the whole group,
-- satisfies the other conditions.
example : IsPGroup 3 (Multiplicative (ZMod 3)) ∧ 2 < Nat.card (Multiplicative (ZMod 3)) ∧
    Nonempty (MulAut (Multiplicative (ZMod 3)) ≃*
      MulAut (⊤ : Subgroup (Multiplicative (ZMod 3)))) := by
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
  exact ⟨IsPGroup.of_card (n := 1) hcard, by omega, ⟨MulAut.congr Subgroup.topEquiv.symm⟩⟩

-- The bound `2 < Nat.card G` is needed: the group of order two and its trivial subgroup satisfy
-- the other conditions, since both automorphism groups are trivial.
example : IsPGroup 2 (Multiplicative (ZMod 2)) ∧ Nat.card (Multiplicative (ZMod 2)) = 2 ∧
    (⊥ : Subgroup (Multiplicative (ZMod 2))) ≠ ⊤ ∧
    Nonempty (MulAut (Multiplicative (ZMod 2)) ≃*
      MulAut (⊥ : Subgroup (Multiplicative (ZMod 2)))) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
  have hfix : ∀ y z : Multiplicative (ZMod 2), (y = 1 ↔ z = 1) → y = z := by decide
  let _ : Unique (MulAut (Multiplicative (ZMod 2))) :=
    { default := 1
      uniq := fun f ↦ MulEquiv.ext fun x ↦ hfix _ _ f.map_eq_one_iff }
  exact ⟨IsPGroup.of_card (n := 1) hcard, hcard, bot_ne_top, ⟨MulEquiv.ofUnique⟩⟩

end MathlibExtTest.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27
