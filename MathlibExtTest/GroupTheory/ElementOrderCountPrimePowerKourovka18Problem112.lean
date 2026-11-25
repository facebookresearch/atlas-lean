/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

open MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112Wanted

-- In a group of prime order, each allowed subgroup has order one.
example (G : Type) [Group G] [Finite G] (hp : (Nat.card G).Prime) (g : G) (hg : g ≠ 1) :
    IsPrimePow (orderOf g) := by
  apply elementOrderCountPrimePowerOrders_holds G _ g hg
  intro d hd hdvd H hcop
  obtain rfl | rfl := (Nat.dvd_prime hp).mp hdvd
  · exact (lt_irrefl _ hd).elim
  · rw [hcop.eq_one_of_dvd H.card_subgroup_dvd_card]
    exact one_dvd _

-- The generator of the cyclic group of order six rules out the divisibility condition.
example :
    ¬ (∀ d : ℕ, 1 < d → d ∣ Nat.card (Multiplicative (ZMod 6)) →
      ∀ H : Subgroup (Multiplicative (ZMod 6)), (Nat.card H).Coprime d →
        Nat.card H ∣ Nat.card {g : Multiplicative (ZMod 6) // orderOf g = d}) := by
  intro h
  let g := Multiplicative.ofAdd (1 : ZMod 6)
  have hg : g ≠ 1 := by decide
  have horder : orderOf g = 6 := ZMod.addOrderOf_one 6
  have hpow := elementOrderCountPrimePowerOrders_holds _ h g hg
  rw [horder] at hpow
  exact (by decide : ¬ IsPrimePow 6) hpow
