/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PGroupConjugacyClassSizes

/-! # Tests for prescribed conjugacy class sizes -/

open MathlibExt.GroupTheory.PGroupConjugacyClassSizesKourovka14Problem77Wanted

-- With only the zeroth power prescribed, every class has size one.
example (p : ℕ) (hp : p.Prime) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧
      ∀ c : ConjClasses G, Nat.card c.carrier = 1 := by
  obtain ⟨G, _, _, hG, h⟩ := everyPowerSetIsClassSizeSet_holds p hp {1} (by simp)
    (fun x hx ↦ ⟨0, by simpa using hx⟩)
  refine ⟨G, inferInstance, inferInstance, hG, fun c ↦ ?_⟩
  have hc : Nat.card c.carrier ∈ (({1} : Finset ℕ) : Set ℕ) := h ▸ ⟨c, rfl⟩
  simpa using hc

-- The exponents can have gaps, even in characteristic two.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup 2 G ∧
    Set.range (fun c : ConjClasses G ↦ Nat.card c.carrier) = {1, 4, 32} := by
  have hpow (x : ℕ) (hx : x ∈ ({1, 4, 32} : Finset ℕ)) : ∃ k : ℕ, x = 2 ^ k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨5, rfl⟩
  simpa only [Finset.coe_insert, Finset.coe_singleton] using
    everyPowerSetIsClassSizeSet_holds 2 (by decide) {1, 4, 32} (by decide) hpow
