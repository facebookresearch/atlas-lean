/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LcmDenseSets
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Positivity

open MetaMathlibExt

-- The empty product contributes even when the prime harmonic sum vanishes.
example : recipSumUpTo (primeProductsAtMost ∅ 0) 1 = 1 := by
  rw [primeProductsAtMost_zero]
  have h : naturalsInSetUpTo (primeProductLayer ∅ 0) 1 = {1} := by
    ext n
    simp only [naturalsInSetUpTo, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    norm_num
    constructor
    · rintro ⟨⟨ha, hb⟩, _⟩
      omega
    · rintro rfl
      simp [primeProductLayer, Nat.dvd_one]
      exact fun p hp h => hp.ne_one h
  simp [recipSumUpTo, h]

-- At a fractional cutoff the layer contains 2·3, while 2² is never squarefree.
example : 6 ∈ naturalsInSetUpTo (primeProductLayer {2, 3} 2) (13 / 2) := by
  simp only [naturalsInSetUpTo, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨by norm_num, ?_⟩
  obtain ⟨hs, hc⟩ := (Nat.squarefree_and_primeFactors_card_eq_two_iff 6).mpr
    ⟨2, 3, by decide, Nat.prime_two, Nat.prime_three, rfl⟩
  refine ⟨hs, ?_, hc⟩
  intro p hp hd
  rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hd) with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)

example : 4 ∉ primeProductLayer {2, 3} 1 := by
  intro h
  exact (by decide : ¬ Squarefree 4) h.1

example : 6 ∉ naturalsInSetUpTo (primeProductLayer {2, 3} 2) (11 / 2) := by
  norm_num [naturalsInSetUpTo]

-- The lower bound produces a squarefree product below the cutoff for positive harmonic mass.
example : ∃ c : ℝ, 0 < c ∧ ∀ (P : Set ℕ) (k : ℕ) (x : ℝ),
    (∀ p ∈ P, Nat.Prime p) → 1 ≤ x → 0 < recipSumUpTo P x →
    (k : ℝ) ≤ c * recipSumUpTo P x →
    (naturalsInSetUpTo (primeProductLayer P k) x).Nonempty := by
  obtain ⟨c, hc, C, hC, h⟩ := recipSum_primeProductLayer_asymp
  refine ⟨c, hc, ?_⟩
  intro P k x hP hx hS hk
  have hpos : 0 < recipSumUpTo (primeProductLayer P k) x :=
    lt_of_lt_of_le (by positivity) (h P k x hP hx hk).1
  by_contra! he
  simp [recipSumUpTo, he] at hpos
