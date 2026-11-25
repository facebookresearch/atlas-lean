/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.CentreDerivedRankExtensionKourovka21Problem150
import Mathlib.Data.ZMod.Basic

/-! # Tests for Zenkov's rank bound and its refutation -/

namespace MathlibExtTest.GroupTheory.CentreDerivedRankExtensionKourovka21Problem150

open MathlibExt.GroupTheory.CentreDerivedRankExtensionKourovka21Problem150Wanted

-- A group of exponent three supplies the intended prime.
example : IsElementaryAbelian (⊤ : Subgroup (Multiplicative (ZMod 3))) := by
  refine ⟨fun x _ y _ => mul_comm x y, 3, by decide, fun x _ => ?_⟩
  change 3 • x.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

-- A cyclic group of order four is abelian, but no prime annihilates its generator.
example : ¬ IsElementaryAbelian (⊤ : Subgroup (Multiplicative (ZMod 4))) := by
  rintro ⟨_, p, hp, hpow⟩
  have hz : (p : ZMod 4) = 0 := by
    have h := congrArg Multiplicative.toAdd
      (hpow (Multiplicative.ofAdd (1 : ZMod 4)) (Subgroup.mem_top _))
    change p • (1 : ZMod 4) = 0 at h
    simpa only [nsmul_eq_mul, mul_one] using h
  have hp2 : p = 2 := ((Nat.dvd_prime_two_le hp (by decide : 2 ≤ 2)).mp
    (dvd_trans (by decide : 2 ∣ 4) ((ZMod.natCast_eq_zero_iff p 4).mp hz))).symm
  subst p
  exact (by decide : (2 : ZMod 4) ≠ 0) hz

-- Check the refutation against the original formulation in terms of generating sets.
example :
    ¬ (∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G) (a : G), A.Normal →
      IsElementaryAbelian A → IsElementaryAbelian B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → a ∈ A →
      (∀ b ∈ B, b * a = a * b → b = 1) →
      ∀ s : Finset G, Subgroup.closure (s : Set G) = B →
        ∃ t : Finset G, t.card ≤ s.card ∧ Subgroup.closure (t : Set G) =
          (Subgroup.center (Subgroup.closure {a} ⊔ B : Subgroup G)).map
              (Subgroup.closure {a} ⊔ B : Subgroup G).subtype ⊓
            ⁅Subgroup.closure {a} ⊔ B, Subgroup.closure {a} ⊔ B⁆) :=
  centreDerivedRankLeComplementRank_refuted

end MathlibExtTest.GroupTheory.CentreDerivedRankExtensionKourovka21Problem150
