/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36
import MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25
import Mathlib.Data.ZMod.Basic

open MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36Wanted

-- Extract the counterexample with conjugacy interpreted in the Sylow subgroup.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G), IsRationalGroup G ∧
    ∃ P : Sylow 2 G, ∃ (g : (P : Subgroup G)) (k : ℕ),
      k.Coprime (orderOf g) ∧ ¬ IsConj g (g ^ k) := by
  classical
  by_contra! h
  apply sylowTwoOfRationalIsRational_refuted
  intro G grp fin hG P g k hk
  exact h G grp fin hG P g k hk

-- In a group of exponent two, every coprime power fixes the element.
example : IsRationalGroup (Multiplicative (ZMod 2)) := by
  intro g k hk
  have h₂ : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide
  have hd := orderOf_dvd_of_pow_eq_one (h₂ g)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with ho | ho
  · rw [orderOf_eq_one_iff.mp ho, one_pow]
    exact IsConj.refl _
  · rw [ho] at hk
    rw [← pow_mod_orderOf, ho, Nat.odd_iff.mp hk.odd_of_right, pow_one]
    exact IsConj.refl _

-- This module's rationality predicate is, by definition, the one of Kourovka 15.25.
example (G : Type*) [Group G] :
    IsRationalGroup G ↔
      MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25Wanted.IsRationalGroup G :=
  Iff.rfl
