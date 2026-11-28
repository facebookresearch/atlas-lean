/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.NumberTheory.Digits.BasePhiRepresentations

/-!
# Bergman expansions of the Fibonacci numbers

The Bergman expansion of $F_{2n}$ is the word $(1000)^{n-1}1$ and the Bergman
expansion of $F_{2n+1}$ is the word $(1000)^{n-1}1001$, up to translation of the
set of positions. The proof exhibits the two words, computes their base phi
values by the Fibonacci recurrence, and uses uniqueness of Bergman expansions.
-/

open scoped goldenRatio

namespace MetaMathlibExt

namespace bergmanWord_fib

private theorem fib_step (m : ℕ) :
    (Nat.fib (m + 2) : ℝ) = φ ^ m + φ ^ (-2 : ℤ) * (Nat.fib m : ℝ) := by
  have h : φ ^ (-2 : ℤ) = ψ + 1 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow, Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]
  rw [h, Nat.fib_add_two, Nat.cast_add]
  have hfib := Real.fib_succ_sub_goldenConj_mul_fib m
  linear_combination hfib

private theorem even_fib_step (n : ℕ) :
    (Nat.fib (2 * n + 2) : ℝ) =
      φ ^ (2 * (n : ℤ)) + φ ^ (-2 : ℤ) * (Nat.fib (2 * n) : ℝ) := by
  exact fib_step (2 * n)

private theorem odd_fib_step (n : ℕ) :
    (Nat.fib (2 * n + 1 + 2) : ℝ) =
      φ ^ (2 * (n : ℤ) + 1) + φ ^ (-2 : ℤ) * (Nat.fib (2 * n + 1) : ℝ) := by
  exact fib_step (2 * n + 1)

private theorem even_value_sum (n : ℕ) :
    basePhiValue ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) =
      ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
  rw [basePhiValue_eq_sum, Finset.sum_image]
  intro a _ b _ h
  dsimp only at h
  have h' : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast h'

private theorem even_value (n : ℕ) :
    basePhiValue ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) =
      Nat.fib (2 * n) := by
  induction n with
  | zero => simp [basePhiValue_eq_sum]
  | succ n ih =>
    rw [even_value_sum, Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hlast : (4 : ℤ) * ((n : ℤ)) + (2 - 2 * ((n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) := by
      rw [hcast]; ring
    rw [hlast]
    have hfactor : ∑ j ∈ Finset.range n,
        φ ^ (4 * (j : ℤ) + (2 - 2 * ((n + 1 : ℕ) : ℤ))) =
        φ ^ (-2 : ℤ) * ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show 4 * (j : ℤ) + (2 - 2 * ((n + 1 : ℕ) : ℤ)) =
        (-2 : ℤ) + (4 * (j : ℤ) + (2 - 2 * (n : ℤ))) by rw [hcast]; ring,
        zpow_add₀ Real.goldenRatio_ne_zero]
    rw [hfactor, ← even_value_sum, ih]
    have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [h2]
    rw [even_fib_step]
    ring

private theorem odd_value_sum (n : ℕ) :
    basePhiValue (insert (-(2 * (n : ℤ)))
        ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) =
      φ ^ (-(2 * (n : ℤ))) +
        ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + 3 + (-(2 * (n : ℤ)))) := by
  have hnot : -(2 * (n : ℤ)) ∉
      (Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))) := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    omega
  rw [basePhiValue_eq_sum, Finset.sum_insert hnot, Finset.sum_image]
  intro a _ b _ h
  dsimp only at h
  have h' : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast h'

private theorem odd_value (n : ℕ) :
    basePhiValue (insert (-(2 * (n : ℤ)))
        ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) =
      Nat.fib (2 * n + 1) := by
  induction n with
  | zero => simp [basePhiValue_eq_sum]
  | succ n ih =>
    rw [odd_value_sum, Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hlast : (4 : ℤ) * (n : ℤ) + 3 + (-(2 * ((n + 1 : ℕ) : ℤ))) = 2 * (n : ℤ) + 1 := by
      rw [hcast]; ring
    rw [hlast]
    have hfactor : φ ^ (-(2 * ((n + 1 : ℕ) : ℤ))) +
        ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + 3 + (-(2 * ((n + 1 : ℕ) : ℤ)))) =
        φ ^ (-2 : ℤ) * (φ ^ (-(2 * (n : ℤ))) +
          ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) := by
      have hpow : φ ^ (-(2 * ((n + 1 : ℕ) : ℤ))) =
          φ ^ (-2 : ℤ) * φ ^ (-(2 * (n : ℤ))) := by
        rw [← zpow_add₀ Real.goldenRatio_ne_zero]
        congr 1
        rw [hcast]; ring
      rw [hpow, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [show 4 * (j : ℤ) + 3 + (-(2 * ((n + 1 : ℕ) : ℤ))) =
        (-2 : ℤ) + (4 * (j : ℤ) + 3 + (-(2 * (n : ℤ)))) by rw [hcast]; ring,
        zpow_add₀ Real.goldenRatio_ne_zero]
    rw [← add_assoc, hfactor, ← odd_value_sum, ih]
    have h2 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
    rw [h2]
    rw [odd_fib_step]
    ring

private theorem bergman_even (n : ℕ) :
    IsBergmanExpansion
      ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
  intro i hi h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  omega

private theorem bergman_odd (n : ℕ) :
    IsBergmanExpansion (insert (-(2 * (n : ℤ)))
      ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) := by
  intro i hi h
  rcases Finset.mem_insert.mp hi with rfl | hi
  · rcases Finset.mem_insert.mp h with h | h
    · omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      omega
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      omega

end bergmanWord_fib

set_option linter.unusedVariables false in
/-- **Bergman expansions of the Fibonacci numbers.** Let $n \ge 1$ and write $F_m$ for the $m$-th
Fibonacci number, with $F_1 = F_2 = 1$. Let $S$ be a finite set of integers with no two
consecutive elements (a Bergman expansion). If the base phi value of $S$ is $F_{2n}$, then
$S = \{t + 4j : 0 \le j < n\}$ for some integer $t$. If the base phi value of $S$ is
$F_{2n+1}$, then $S = \{t\} \cup \{t + 3 + 4j : 0 \le j < n\}$ for some integer $t$.

Read from the highest to the lowest position, these are the digit words $(1000)^{n-1}1$ and
$(1000)^{n-1}1001$; the position of the radix point is not determined.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 3.1
(`fq-2024-dekking11102023-prop-3.1`). -/
public theorem bergmanWord_fib (n : ℕ) (hn : 1 ≤ n) :
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n) →
      ∃ t : ℤ, S = (Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + t) ∧
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n + 1) →
      ∃ t : ℤ, S = insert t ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + t)) := by
  constructor
  · intro S hS hval
    refine ⟨2 - 2 * (n : ℤ), ?_⟩
    have hval' : basePhiValue S =
        basePhiValue ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
      rw [hval, bergmanWord_fib.even_value]
    exact BasePhiRepresentations.bergman_eq_of_value_eq hS (bergmanWord_fib.bergman_even n) hval'
  · intro S hS hval
    refine ⟨-(2 * (n : ℤ)), ?_⟩
    have hval' : basePhiValue S =
        basePhiValue (insert (-(2 * (n : ℤ)))
          ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) := by
      rw [hval, bergmanWord_fib.odd_value]
    exact BasePhiRepresentations.bergman_eq_of_value_eq hS (bergmanWord_fib.bergman_odd n) hval'

end MetaMathlibExt
