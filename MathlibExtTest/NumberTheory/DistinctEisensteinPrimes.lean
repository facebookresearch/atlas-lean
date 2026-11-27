/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MathlibExt.NumberTheory.DistinctEisensteinPrimes

open MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted

-- At the lower endpoint the number of summands must be a positive multiple of six.
example : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 6 = 5) ∧
    (∑ p ∈ S, p) = 162 ∧ 6 ≤ S.card := by
  obtain ⟨S, hp, hs⟩ := eq_sum_distinct_primes_modEq_five 162 (by decide)
  refine ⟨S, hp, hs, ?_⟩
  have hmod := Finset.sum_nat_mod S 6 (fun p => p)
  have hres : (∑ p ∈ S, p % 6) = ∑ _ ∈ S, 5 := Finset.sum_congr rfl fun p h => (hp p h).2
  rw [hs, hres, Finset.sum_const, Nat.nsmul_eq_mul] at hmod
  have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by rintro rfl; simp at hs)
  have := Finset.card_pos.mpr hne
  omega

-- One below the threshold, the residue forces one summand or at least seven.
-- Seven eligible primes already sum to at least 173.
example : ¬ ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 6 = 5) ∧ (∑ p ∈ S, p) = 161 := by
  rintro ⟨S, hp, hs⟩
  let small := (Finset.range 47).filter (fun p => p.Prime ∧ p % 6 = 5)
  have hsmall : ∑ p ∈ small, (47 - p) = 156 := by decide
  have hsub : S.filter (· < 47) ⊆ small := by
    intro p h
    obtain ⟨hpS, hlt⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hp p hpS⟩
  have hdeficit : ∑ p ∈ S, (47 - p) ≤ 156 := by
    rw [← hsmall, ← Finset.sum_filter_of_ne (p := (· < 47)) (by intros; omega)]
    exact Finset.sum_le_sum_of_subset hsub
  have hcount : ∑ _ ∈ S, 47 ≤ ∑ p ∈ S, (p + (47 - p)) :=
    Finset.sum_le_sum fun p _ => by omega
  rw [Finset.sum_add_distrib, hs] at hcount
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hcount
  have hmod := Finset.sum_nat_mod S 6 (fun p => p)
  have hres : (∑ p ∈ S, p % 6) = ∑ _ ∈ S, 5 := Finset.sum_congr rfl fun p h => (hp p h).2
  rw [hs, hres, Finset.sum_const, Nat.nsmul_eq_mul] at hmod
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
  simp only [Finset.sum_singleton] at hs
  subst p
  exact (by decide : ¬ Nat.Prime 161) (hp 161 (by simp)).1
