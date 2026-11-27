/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SmallSubsetsSeparatedKourovka17Problem102
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Tests for separation of subsets of a group -/

open MathlibExt.GroupTheory.SmallSubsetsSeparatedKourovka17Problem102Wanted

-- An infinite subgroup itself witnesses separation from any singleton outside it.
example {G : Type*} [Group G] (H : Subgroup G) (hH : (H : Set G).Infinite)
    {b : G} (hb : b ∉ H) : AreSeparated (H : Set G) {b} := by
  refine ⟨H, hH, H.one_mem, inv_coe_set, Set.disjoint_singleton_right.mpr ?_⟩
  rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩
  exact hb (H.mul_mem (H.mul_mem hx hy) hz)

-- Since a separating set contains the identity, it cannot separate overlapping subsets.
example {G : Type*} [Group G] {A B : Set G} {a : G} (ha : a ∈ A) (hb : a ∈ B) :
    ¬ AreSeparated A B := by
  rintro ⟨X, _, h₁, _, hdisj⟩
  apply Set.disjoint_left.mp hdisj _ hb
  simpa using Set.mul_mem_mul (Set.mul_mem_mul h₁ ha) h₁
