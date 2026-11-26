/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.IsolatedSubgroupPSeparable

open MathlibExt.GroupTheory.IsolatedSubgroupPSeparableKourovka15Problem60Wanted

-- In a p-group, the order of any nonidentity element is divisible by p.
example {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (hG : IsPGroup p G) :
    IsPPrimeIsolated p (⊥ : Subgroup G) := by
  intro x n _ hn hx
  by_contra h
  exact hn ((hG.dvd_orderOf (by simpa using h)).trans (orderOf_dvd_of_pow_eq_one hx))

-- The identity map of a finite p-group separates every outside element.
example {p : ℕ} {G : Type} [Group G] [Finite G] (hG : IsPGroup p G) (H : Subgroup G) :
    IsPSeparable p H := by
  intro x hx
  exact ⟨G, inferInstance, inferInstance, hG, MonoidHom.id G, by simpa using hx⟩
