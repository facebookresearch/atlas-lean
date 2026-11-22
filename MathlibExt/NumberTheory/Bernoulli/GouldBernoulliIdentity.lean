/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star

@[expose] public section

namespace MetaMathlibExt

/-! # Gould-Bernoulli identity
-/

open scoped BigOperators

/-- Alternating binomial sums telescope across Pascal's rule. -/
private theorem aux_pascal_sum (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * f k =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f k) -
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f (k + 1) := by
  have hfirst : ∀ m : ℕ, (-1 : ℚ) ^ (0 : ℕ) * (Nat.choose m 0 : ℚ) * f 0 = f 0 := by
    intro m
    simp
  have hlast : (-1 : ℚ) ^ (n + 1) * (Nat.choose n (n + 1) : ℚ) * f (n + 1) = 0 := by
    have hc : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hc, Nat.cast_zero, mul_zero, zero_mul]
  have hpas : ∀ k : ℕ, (-1 : ℚ) ^ (k + 1) * (Nat.choose (n + 1) (k + 1) : ℚ) * f (k + 1) +
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f (k + 1) =
      (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) * f (k + 1) := by
    intro k
    have hcc : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) := by
      rw [Nat.choose_succ_succ]
    have hccQ : ((Nat.choose (n + 1) (k + 1) : ℕ) : ℚ) =
        ((Nat.choose n k : ℕ) : ℚ) + ((Nat.choose n (k + 1) : ℕ) : ℚ) := by
      exact_mod_cast hcc
    have hsign : (-1 : ℚ) ^ (k + 1) = -(-1 : ℚ) ^ k := by
      rw [pow_succ]
      ring
    rw [hccQ, hsign]
    ring
  have eL : (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * f k) =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k + 1) * (Nat.choose (n + 1) (k + 1) : ℚ) * f (k + 1)) + f 0 := by
    conv_lhs => rw [Finset.sum_range_succ']
    simp only [hfirst]
  have eC : (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k + 1) * (Nat.choose (n + 1) (k + 1) : ℚ) * f (k + 1)) +
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) * f (k + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hpas k)
  have eM : (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) * f (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f k) - f 0 := by
    have e1 : (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f k) =
        (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) * f (k + 1)) + f 0 := by
      conv_lhs => rw [Finset.sum_range_succ']
      simp only [hfirst]
    have e2 : (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f k) =
        ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f k := by
      rw [Finset.sum_range_succ, hlast, add_zero]
    linarith
  linarith

/-- Vanishing and evaluation of alternating binomial power sums. -/
private theorem aux_pow_triple : ∀ n : ℕ,
    (∀ j : ℕ, j < n → ∀ y : ℚ,
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (y - (k : ℚ)) ^ j = 0) ∧
    (∀ y : ℚ, ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (y - (k : ℚ)) ^ n =
      (Nat.factorial n : ℚ)) ∧
    (∀ y : ℚ, ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (y - (k : ℚ)) ^ (n + 1) =
      (Nat.factorial (n + 1) : ℚ) * (y - (n : ℚ) / 2)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun j hj => (Nat.not_lt_zero j hj).elim, ?_, ?_⟩
    · intro y
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · intro y
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
  | succ n ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have expand : ∀ (j : ℕ) (y : ℚ),
        (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
          ((y - (k : ℚ)) ^ j - (y - (((k + 1 : ℕ)) : ℚ)) ^ j)) =
        ∑ i ∈ Finset.range j, (Nat.choose j i : ℚ) *
          ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((y - 1 - (k : ℚ)) ^ i) := by
      intro j y
      have inner : ∀ k : ℕ, (y - (k : ℚ)) ^ j - (y - (((k + 1 : ℕ)) : ℚ)) ^ j =
          ∑ i ∈ Finset.range j, (Nat.choose j i : ℚ) * ((y - 1 - (k : ℚ)) ^ i) := by
        intro k
        have h1 : y - (k : ℚ) = (y - 1 - (k : ℚ)) + 1 := by ring
        have h2 : y - (((k + 1 : ℕ)) : ℚ) = y - 1 - (k : ℚ) := by push_cast; ring
        rw [h1, h2]
        have hap := add_pow (y - 1 - (k : ℚ)) (1 : ℚ) j
        rw [Finset.sum_range_succ] at hap
        have hjj : (y - 1 - (k : ℚ)) ^ j * (1 : ℚ) ^ (j - j) * (Nat.choose j j : ℚ) =
            (y - 1 - (k : ℚ)) ^ j := by simp
        rw [hjj] at hap
        rw [hap]
        have hsub : ∀ (S a : ℚ), (S + a) - a = S := fun S a => by ring
        rw [hsub]
        apply Finset.sum_congr rfl
        intro i _
        ring
      calc (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
            ((y - (k : ℚ)) ^ j - (y - (((k + 1 : ℕ)) : ℚ)) ^ j))
          = ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
              (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((Nat.choose j i : ℚ) * ((y - 1 - (k : ℚ)) ^ i)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [inner k, Finset.mul_sum]
        _ = ∑ i ∈ Finset.range j, ∑ k ∈ Finset.range (n + 1),
              (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((Nat.choose j i : ℚ) * ((y - 1 - (k : ℚ)) ^ i)) :=
          Finset.sum_comm
        _ = ∑ i ∈ Finset.range j, (Nat.choose j i : ℚ) *
            ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((y - 1 - (k : ℚ)) ^ i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    have E' : ∀ (j : ℕ) (y : ℚ),
        (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * (y - (k : ℚ)) ^ j) =
        ∑ i ∈ Finset.range j, (Nat.choose j i : ℚ) *
          ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((y - 1 - (k : ℚ)) ^ i) := by
      intro j y
      calc (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * (y - (k : ℚ)) ^ j)
          = ((∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (y - (k : ℚ)) ^ j) -
            ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (y - (((k + 1 : ℕ)) : ℚ)) ^ j) :=
            aux_pascal_sum n (fun k => (y - (k : ℚ)) ^ j)
        _ = (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
            ((y - (k : ℚ)) ^ j - (y - (((k + 1 : ℕ)) : ℚ)) ^ j)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ = ∑ i ∈ Finset.range j, (Nat.choose j i : ℚ) *
            ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((y - 1 - (k : ℚ)) ^ i) :=
            expand j y
    have hA' : ∀ j : ℕ, j < n + 1 → ∀ y : ℚ,
        ∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * (y - (k : ℚ)) ^ j = 0 := by
      intro j hj y
      have hE := E' j y
      rw [hE]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      have hi2 : i < n := by omega
      rw [hA i hi2 (y - 1), mul_zero]
    have hB' : ∀ y : ℚ, ∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) *
        (y - (k : ℚ)) ^ (n + 1) = (Nat.factorial (n + 1) : ℚ) := by
      intro y
      have hE := E' (n + 1) y
      rw [hE, Finset.sum_range_succ]
      have h0 : (∑ i ∈ Finset.range n, (Nat.choose (n + 1) i : ℚ) *
          ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((y - 1 - (k : ℚ)) ^ i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        have hi2 : i < n := by omega
        rw [hA i hi2 (y - 1), mul_zero]
      rw [h0, zero_add, hB (y - 1)]
      have hcm := Nat.choose_mul_factorial_mul_factorial (show n ≤ n + 1 by omega)
      have hsub : n + 1 - n = 1 := by omega
      rw [hsub, Nat.factorial_one, mul_one] at hcm
      exact_mod_cast hcm
    have hC' : ∀ y : ℚ, ∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) *
        (y - (k : ℚ)) ^ (n + 2) = (Nat.factorial (n + 2) : ℚ) * (y - ((n + 1 : ℕ) : ℚ) / 2) := by
      intro y
      have hE := E' (n + 2) y
      rw [hE, Finset.sum_range_succ, Finset.sum_range_succ]
      have h0 : (∑ i ∈ Finset.range n, (Nat.choose (n + 2) i : ℚ) *
          ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * ((y - 1 - (k : ℚ)) ^ i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        have hi2 : i < n := by omega
        rw [hA i hi2 (y - 1), mul_zero]
      rw [h0, zero_add, hB (y - 1), hC (y - 1)]
      have hI1 : ((Nat.choose (n + 2) n : ℕ) : ℚ) * (Nat.factorial n : ℚ) =
          (Nat.factorial (n + 2) : ℚ) / 2 := by
        have hcm := Nat.choose_mul_factorial_mul_factorial (show n ≤ n + 2 by omega)
        have hsub : n + 2 - n = 2 := by omega
        rw [hsub] at hcm
        have h2 : Nat.factorial 2 = 2 := by decide
        rw [h2] at hcm
        have hcmQ : ((Nat.choose (n + 2) n : ℕ) : ℚ) * (Nat.factorial n : ℚ) * 2 =
            (Nat.factorial (n + 2) : ℚ) := by
          exact_mod_cast hcm
        linarith
      have hI2 : ((Nat.choose (n + 2) (n + 1) : ℕ) : ℚ) * (Nat.factorial (n + 1) : ℚ) =
          (Nat.factorial (n + 2) : ℚ) := by
        have hcm := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ n + 2 by omega)
        have hsub : n + 2 - (n + 1) = 1 := by omega
        rw [hsub, Nat.factorial_one, mul_one] at hcm
        exact_mod_cast hcm
      push_cast
      linear_combination hI1 + hI2 * ((y - 1) - (n : ℚ) / 2)
    exact ⟨hA', hB', hC'⟩

/-- Bernoulli differences reduce the level-`n + 1` sum to a power sum. -/
private theorem aux_bernoulli_step (n : ℕ) (x : ℚ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
      ((Polynomial.bernoulli (n + 2)).eval (x - (k : ℚ)) -
        (Polynomial.bernoulli (n + 2)).eval (x - 1 - (k : ℚ)))) =
    ((n + 2 : ℕ) : ℚ) * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
      ((x - 1 - (k : ℚ)) ^ (n + 1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h := Polynomial.bernoulli_eval_one_add (n + 2) (x - 1 - (k : ℚ))
  have e1 : (1 : ℚ) + (x - 1 - (k : ℚ)) = x - (k : ℚ) := by ring
  have e2 : n + 2 - 1 = n + 1 := by omega
  rw [e1, e2] at h
  rw [h]
  ring

/-- The Gould-Bernoulli sum at level `n + 1`, reduced to power sums. -/
private theorem aux_main_succ (n : ℕ) (x : ℚ) :
    (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) *
      (Polynomial.bernoulli (n + 2)).eval (x - (k : ℚ))) =
    (Nat.factorial (n + 2) : ℚ) / 2 * (2 * x - ((n + 1 : ℕ) : ℚ) - 1) := by
  have hpow := (aux_pow_triple n).2.2 (x - 1)
  have hstep := aux_bernoulli_step n x
  calc (∑ k ∈ Finset.range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) *
        (Polynomial.bernoulli (n + 2)).eval (x - (k : ℚ)))
      = ((∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
          (Polynomial.bernoulli (n + 2)).eval (x - (k : ℚ))) -
        ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
          (Polynomial.bernoulli (n + 2)).eval (x - (((k + 1 : ℕ)) : ℚ))) :=
        aux_pascal_sum n (fun k => (Polynomial.bernoulli (n + 2)).eval (x - (k : ℚ)))
    _ = (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
        ((Polynomial.bernoulli (n + 2)).eval (x - (k : ℚ)) -
          (Polynomial.bernoulli (n + 2)).eval (x - 1 - (k : ℚ)))) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        have hk : x - (((k + 1 : ℕ)) : ℚ) = x - 1 - (k : ℚ) := by push_cast; ring
        rw [hk, mul_sub]
    _ = ((n + 2 : ℕ) : ℚ) * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
        ((x - 1 - (k : ℚ)) ^ (n + 1)) := hstep
    _ = ((n + 2 : ℕ) : ℚ) * ((Nat.factorial (n + 1) : ℚ) * ((x - 1) - (n : ℚ) / 2)) := by
        rw [hpow]
    _ = (Nat.factorial (n + 2) : ℚ) / 2 * (2 * x - ((n + 1 : ℕ) : ℚ) - 1) := by
        have hfact : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := Nat.factorial_succ (n + 1)
        have hfactQ : (Nat.factorial (n + 2) : ℚ) = ((n + 2 : ℕ) : ℚ) * (Nat.factorial (n + 1) : ℚ) := by
          exact_mod_cast hfact
        rw [hfactQ]
        push_cast
        ring

/--
**Gould's alternating identity for Bernoulli polynomials.** Let $B_i$ denote the $i$-th
Bernoulli number, with $B_1 = -1/2$, and let $B_j(x) = \sum_{i=0}^{j} \binom{j}{i} B_i x^{j-i}$
be the $j$-th Bernoulli polynomial. For every natural number $n$ and every rational number $x$,
$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} B_{n+1}(x - k) = \frac{(n+1)!}{2} (2x - n - 1).$$

Source: Claudio de J. Pita Ruiz V., "Carlitz-Type and Other Bernoulli Identities", Journal of Integer Sequences 19 (2016), Article 16.1.8, Proposition (Gould-Bernoulli identities), equation (5.3), lines 727-732, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex>.
Proves `Wanted` entry `gould_bernoulli_identity`.
-/
theorem gould_bernoulli_identity (n : ℕ) (x : ℚ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
          (Polynomial.bernoulli (n + 1)).eval (x - k) =
      (Nat.factorial (n + 1) : ℚ) / 2 * (2 * x - n - 1) := by
  have hzero : (∑ k ∈ Finset.range (0 + 1), (-1 : ℚ) ^ k * (Nat.choose 0 k : ℚ) *
      (Polynomial.bernoulli (0 + 1)).eval (x - (k : ℚ))) =
      (Nat.factorial (0 + 1) : ℚ) / 2 * (2 * x - ((0 : ℕ) : ℚ) - 1) := by
    have e01 : (0 : ℕ) + 1 = 1 := by decide
    rw [e01, Finset.sum_range_one, Polynomial.bernoulli_one]
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, sub_zero,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.factorial_one]
    ring
  rcases n with _ | n
  · exact hzero
  · exact aux_main_succ n x

end MetaMathlibExt
