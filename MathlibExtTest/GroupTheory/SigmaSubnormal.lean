/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.Subgroup.Simple
import MathlibExt.GroupTheory.SigmaSubnormal

open MathlibExt.GroupTheory.KourovkaNotebookShared

namespace MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84Wanted

private abbrev singletons (p : Nat.Primes) : Set ℕ := {p.val}

example : IsPrimePartition singletons := by
  refine ⟨fun i => ⟨⟨i, rfl⟩, ?_⟩, ?_, fun p hp => ⟨⟨p, hp⟩, rfl⟩⟩
  · rintro p (rfl : p = i.val)
    exact i.property
  · intro i j hij
    exact Set.disjoint_singleton.mpr (fun h => hij (Subtype.ext h))

-- One has no prime divisors, whereas every prime divides zero.
example : IsSigmaPrimary singletons 1 := by
  refine ⟨⟨2, Nat.prime_two⟩, fun p hp hd => ?_⟩
  exact (hp.ne_one (Nat.dvd_one.mp hd)).elim

example : ¬ IsSigmaPrimary singletons 0 := by
  rintro ⟨i, hi⟩
  have h₂ : 2 = i.val := hi 2 Nat.prime_two (dvd_zero _)
  have h₃ : 3 = i.val := hi 3 Nat.prime_three (dvd_zero _)
  omega

-- A normal subgroup admits a one-step chain even when there are no primary blocks.
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] :
    IsSigmaSubnormal (fun i : Empty => i.elim) H := by
  refine ⟨1, fun i => if i = 0 then H else ⊤, rfl, rfl, ?_⟩
  intro i hi
  obtain rfl : i = 0 := by omega
  exact ⟨le_top, Or.inl (inferInstanceAs (H.subgroupOf ⊤).Normal)⟩

-- In a simple group, `⊤ / ⊥` is a chief factor.
example {G : Type*} [Group G] [IsSimpleGroup G] : IsChiefFactor (⊤ : Subgroup G) ⊥ :=
  ⟨inferInstance, inferInstance, bot_lt_top,
    fun N _ _ _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N⟩

-- A chief factor is a proper step: `A / A` never is one.
example {G : Type*} [Group G] (A : Subgroup G) : ¬ IsChiefFactor A A :=
  fun h => h.2.2.1.ne rfl

-- With one block containing every prime, every group is σ-soluble.
example {G : Type*} [Group G] : IsSigmaSoluble (fun _ : Unit => {p : ℕ | p.Prime}) G :=
  fun _ _ _ => ⟨(), fun _ hp _ => hp⟩

-- For the singleton partition, the chief factor `⊤ / ⊥` of a simple group whose order has two
-- prime divisors is not σ-primary, so such a group is not σ-soluble.
example {G : Type*} [Group G] [IsSimpleGroup G] (h2 : 2 ∣ Nat.card G) (h3 : 3 ∣ Nat.card G) :
    ¬ IsSigmaSoluble singletons G := by
  intro h
  obtain ⟨i, hi⟩ := h ⊤ ⊥ ⟨inferInstance, inferInstance, bot_lt_top,
    fun N _ _ _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N⟩
  rw [Subgroup.relIndex_bot_left, Subgroup.card_top] at hi
  have e₂ : 2 = i.val := hi 2 Nat.prime_two h2
  have e₃ : 3 = i.val := hi 3 Nat.prime_three h3
  omega

end MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84Wanted
