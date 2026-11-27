/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.HallPronormalNormalClosureKourovka18Problem32
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientGroup

/-! # Tests for `MathlibExt.GroupTheory.HallPronormalNormalClosureKourovka18Problem32` -/

open MathlibExt.GroupTheory.HallPronormalNormalClosureKourovka18Problem32Wanted

-- The refutation provides a finite group with a Hall subgroup that is not pronormal in its normal
-- closure.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G), IsHallSubgroup H ∧
    ¬ IsPronormalIn H (Subgroup.normalClosure (H : Set G)) :=
  Classical.byContradiction fun h => hallSubgroupPronormalInNormalClosure_refuted
    fun G _ _ H hH => Classical.byContradiction fun hn => h ⟨G, ‹_›, ‹_›, H, hH, hn⟩

-- Consequently some finite group has a non-pronormal Hall subgroup: pronormality in the whole
-- group gives pronormality in every subgroup, the normal closure included.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G), IsHallSubgroup H ∧
    ¬ IsPronormalIn H ⊤ := by
  by_contra h
  refine hallSubgroupPronormalInNormalClosure_refuted fun G _ _ H hH g _ => ?_
  have hp : IsPronormalIn H ⊤ :=
    Classical.byContradiction fun hn => h ⟨G, ‹_›, ‹_›, H, hH, hn⟩
  exact hp g (Subgroup.mem_top g)

-- The trivial subgroup and the whole group are Hall subgroups.
example {G : Type} [Group G] : IsHallSubgroup (⊥ : Subgroup G) := by
  simp [IsHallSubgroup]

example {G : Type} [Group G] : IsHallSubgroup (⊤ : Subgroup G) := by
  simp [IsHallSubgroup]

-- The subgroup of order `2` in the cyclic group of order `4` has index `2`, so it is not Hall.
example : ¬ IsHallSubgroup (Subgroup.zpowers (Multiplicative.ofAdd (2 : ZMod 4))) := by
  have hcard : Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (2 : ZMod 4))) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  have hindex : (Subgroup.zpowers (Multiplicative.ofAdd (2 : ZMod 4))).index = 2 := by
    have h := (Subgroup.zpowers (Multiplicative.ofAdd (2 : ZMod 4))).card_mul_index
    rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
    omega
  rw [IsHallSubgroup, hcard, hindex]
  decide

-- A normal subgroup is pronormal in every subgroup, with conjugating element `1`.
example {G : Type} [Group G] (H K : Subgroup G) [H.Normal] : IsPronormalIn H K := by
  intro g _
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  have h1 : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
    ext x
    simp
  rw [h1]
  exact (H.normal_iff_map_conj_eq.mp ‹_› g).symm

-- Every subgroup is pronormal in itself, with conjugating element `g`.
example {G : Type} [Group G] (H : Subgroup G) : IsPronormalIn H H :=
  fun g hg => ⟨g, Subgroup.mem_sup_left hg, rfl⟩
