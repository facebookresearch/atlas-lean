/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

end MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84Wanted
