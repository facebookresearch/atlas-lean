/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import MathlibExt.Combinatorics.DisjointMonochromaticSumset

/-! # Parity coloring of disjoint infinite sets and their sumset -/

open scoped Pointwise

namespace MetaMathlibExt.exists_disjoint_infinite_union_add_monochromatic

-- A sum of two odd numbers is even, so the common color must be even.
example : ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ Disjoint A B ∧
    A ∪ B ∪ (A + B) ⊆ {n | n % 2 = 0} := by
  let c (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨A, B, hA, hB, hd, k, hcA, hcB, hsum⟩ :=
    exists_disjoint_infinite_union_add_monochromatic c
  have hk : k.val = 0 := by
    obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨b, hb⟩ := hB.nonempty
    have ha' : a % 2 = k.val := congrArg Fin.val (hcA a ha)
    have hb' : b % 2 = k.val := congrArg Fin.val (hcB b hb)
    have hab : (a + b) % 2 = k.val := congrArg Fin.val (hsum a ha b hb)
    rw [Nat.add_mod, ha', hb'] at hab
    omega
  refine ⟨A, B, hA, hB, hd, ?_⟩
  rintro n ((ha | hb) | ⟨a, ha, b, hb, rfl⟩)
  · exact (congrArg Fin.val (hcA n ha)).trans hk
  · exact (congrArg Fin.val (hcB n hb)).trans hk
  · exact (congrArg Fin.val (hsum a ha b hb)).trans hk

end MetaMathlibExt.exists_disjoint_infinite_union_add_monochromatic
