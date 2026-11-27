/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Chebyshev

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private lemma choose_mul_choose_eq (s m k i : ℕ) (h : s = m + k) (hi : i ≤ k) :
    s.choose i * (s - i).choose m = s.choose m * k.choose i := by
  have his : i ≤ s := by omega
  have hmi : m ≤ s - i := by omega
  have h1 := Nat.choose_mul (n := s) hmi
  have h2 : s.choose (s - i) = s.choose i := Nat.choose_symm his
  have h3 : s - m = k := by omega
  have h4 : s - i - m = k - i := by omega
  have h5 : k.choose (k - i) = k.choose i := Nat.choose_symm hi
  rw [h3, h4] at h1
  rw [← h2, ← h5]
  exact h1

private lemma sum_choose_mul_eq (s m k : ℕ) (h : s = m + k) :
    ∑ i ∈ Finset.range (k + 1), s.choose i * (s - i).choose m
      = s.choose m * 2 ^ k := by
  have hsum := Nat.sum_range_choose k
  conv_rhs => rw [← hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hii : i ≤ k := by
    have hmem := Finset.mem_range.mp hi
    omega
  exact choose_mul_choose_eq s m k i h hii

private lemma sum_choose_mul_eq_int (s m k : ℕ) (h : s = m + k) :
    (∑ i ∈ Finset.range (k + 1), ((s.choose i : ℕ) : ℤ) * (((s - i).choose m : ℕ) : ℤ))
      = ((s.choose m : ℕ) : ℤ) * (2 : ℤ) ^ k := by
  have hN := sum_choose_mul_eq s m k h
  exact_mod_cast hN

private lemma chebyshevU_coeff_aux_base0 (k : ℕ) (hk : k ≤ 0) :
    (Polynomial.Chebyshev.U ℤ (((0 : ℕ)) : ℤ)).coeff k =
      if (0 : ℕ) % 2 = k % 2 then (-1 : ℤ) ^ (((0 : ℕ) - k) / 2) *
        ((Nat.choose (((0 : ℕ) + k) / 2) (((0 : ℕ) - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
      else 0 := by
  have hk0 : k = 0 := by omega
  subst hk0
  rw [Nat.cast_zero, Polynomial.Chebyshev.U_zero]
  norm_num

private lemma chebyshevU_coeff_aux_base1 (k : ℕ) (hk : k ≤ 1) :
    (Polynomial.Chebyshev.U ℤ (((1 : ℕ)) : ℤ)).coeff k =
      if (1 : ℕ) % 2 = k % 2 then (-1 : ℤ) ^ (((1 : ℕ) - k) / 2) *
        ((Nat.choose (((1 : ℕ) + k) / 2) (((1 : ℕ) - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
      else 0 := by
  have hkk : k = 0 ∨ k = 1 := by omega
  have hC : (2 : Polynomial ℤ) = Polynomial.C 2 := (Polynomial.C_ofNat 2).symm
  rcases hkk with rfl | rfl
  · rw [Nat.cast_one, Polynomial.Chebyshev.U_one]
    norm_num [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero]
  · rw [Nat.cast_one, Polynomial.Chebyshev.U_one]
    have h2X : (2 : Polynomial ℤ) * Polynomial.X
        = Polynomial.C 2 * Polynomial.X := by rw [hC]
    rw [h2X, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one]
    norm_num [Nat.choose_zero_right]

private lemma chebyshevU_coeff_aux_step (n : ℕ)
    (ih0 : ∀ k : ℕ, k ≤ n →
      (Polynomial.Chebyshev.U ℤ ((n : ℕ) : ℤ)).coeff k =
        if n % 2 = k % 2 then (-1 : ℤ) ^ ((n - k) / 2) *
          ((Nat.choose ((n + k) / 2) ((n - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
        else 0)
    (ih1 : ∀ k : ℕ, k ≤ n + 1 →
      (Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)).coeff k =
        if (n + 1) % 2 = k % 2 then (-1 : ℤ) ^ (((n + 1) - k) / 2) *
          ((Nat.choose (((n + 1) + k) / 2) (((n + 1) - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
        else 0)
    (k : ℕ) (hk : k ≤ n + 2) :
    (Polynomial.Chebyshev.U ℤ (((n + 2 : ℕ)) : ℤ)).coeff k =
      if (n + 2) % 2 = k % 2 then (-1 : ℤ) ^ (((n + 2) - k) / 2) *
        ((Nat.choose (((n + 2) + k) / 2) (((n + 2) - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
      else 0 := by
  have hU : Polynomial.Chebyshev.U ℤ (((n + 2 : ℕ)) : ℤ)
      = 2 * Polynomial.X * Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)
        - Polynomial.Chebyshev.U ℤ (((n : ℕ)) : ℤ) := by
    have h := Polynomial.Chebyshev.U_add_two ℤ (((n : ℕ)))
    have e1 : (((n : ℕ)) : ℤ) + 2 = (((n + 2 : ℕ)) : ℤ) := by omega
    have e2 : (((n : ℕ)) : ℤ) + 1 = (((n + 1 : ℕ)) : ℤ) := by omega
    rw [e1, e2] at h
    exact h
  have hC : (2 : Polynomial ℤ) = Polynomial.C 2 := (Polynomial.C_ofNat 2).symm
  have hdeg : ∀ t : ℕ, (Polynomial.Chebyshev.U ℤ (((t : ℕ)) : ℤ)).natDegree = t :=
    fun t => Polynomial.Chebyshev.natDegree_U_natCast ℤ t
  rw [hU, Polynomial.coeff_sub]
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [show (2 : Polynomial ℤ) * Polynomial.X *
          Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)
        = Polynomial.C 2 * (Polynomial.X *
          Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)) by rw [hC, mul_assoc]]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero, mul_zero, zero_sub,
      ih0 0 (by omega)]
    by_cases hpar0 : n % 2 = (0 : ℕ) % 2
    · have p02 : (n + 2) % 2 = (0 : ℕ) % 2 := by omega
      rw [ite_eq_left hpar0, ite_eq_left p02]
      have e1 : (n + 2 - 0) / 2 = (n - 0) / 2 + 1 := by omega
      have e2 : (n + 2 + 0) / 2 = (n + 0) / 2 + 1 := by omega
      have es : (n + 0) / 2 = (n - 0) / 2 := by omega
      rw [e1, e2, es]
      simp only [Nat.choose_self, Nat.cast_one, mul_one, pow_zero]
      rw [pow_succ]
      ring
    · have n02 : ¬ ((n + 2) % 2 = (0 : ℕ) % 2) := by omega
      rw [ite_eq_right hpar0, ite_eq_right n02, neg_zero]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Nat.succ_eq_add_one] at hk ⊢
    rw [show (2 : Polynomial ℤ) * Polynomial.X *
          Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)
        = Polynomial.C 2 * (Polynomial.X *
          Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)) by rw [hC, mul_assoc]]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    by_cases hjn : j + 1 ≤ n
    · rw [ih1 j (by omega), ih0 (j + 1) hjn]
      by_cases hpar : n % 2 = (j + 1) % 2
      · have p01 : (n + 1) % 2 = j % 2 := by omega
        have p12 : (n + 2) % 2 = (j + 1) % 2 := by omega
        rw [ite_eq_left p01, ite_eq_left hpar, ite_eq_left p12]
        set s := (n + (j + 1)) / 2 with hs
        set m := (n - (j + 1)) / 2 with hm
        have e1 : (n + 2 - (j + 1)) / 2 = m + 1 := by omega
        have e2 : (n + 2 + (j + 1)) / 2 = s + 1 := by omega
        have e3 : (n + 1 - j) / 2 = m + 1 := by omega
        have e4 : (n + 1 + j) / 2 = s := by omega
        rw [e1, e2, e3, e4]
        have hps := Nat.choose_succ_succ s m
        rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at hps
        have pascal : ((((s + 1).choose (m + 1) : ℕ)) : ℤ)
            = ((((s.choose m : ℕ))) : ℤ) + ((((s.choose (m + 1) : ℕ))) : ℤ) := by
          exact_mod_cast hps
        have ePow : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := pow_succ' _ _
        have eNeg : (-1 : ℤ) ^ (m + 1) = -(-1 : ℤ) ^ m := by rw [pow_succ]; ring
        rw [pascal, ePow, eNeg]
        ring
      · have n01 : ¬ ((n + 1) % 2 = j % 2) := by omega
        have n12 : ¬ ((n + 2) % 2 = (j + 1) % 2) := by omega
        rw [ite_eq_right n01, ite_eq_right hpar, ite_eq_right n12]
        ring
    · have hkk : j + 1 = n + 1 ∨ j + 1 = n + 2 := by omega
      rcases hkk with hkk | hkk
      · have hjn : j = n := by omega
        rw [hjn]
        rw [ih1 n (by omega)]
        have hvan : (Polynomial.Chebyshev.U ℤ (((n : ℕ)) : ℤ)).coeff (n + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hdeg n]
          omega
        rw [hvan]
        have n01 : ¬ ((n + 1) % 2 = n % 2) := by omega
        have n12 : ¬ ((n + 2) % 2 = (n + 1) % 2) := by omega
        rw [ite_eq_right n01, ite_eq_right n12]
        ring
      · have hjn : j = n + 1 := by omega
        rw [hjn]
        rw [ih1 (n + 1) (by omega)]
        have hvan : (Polynomial.Chebyshev.U ℤ (((n : ℕ)) : ℤ)).coeff (n + 1 + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hdeg n]
          omega
        rw [hvan]
        have e : n + 1 + 1 = n + 2 := by omega
        rw [e]
        have p12 : (n + 2) % 2 = (n + 2) % 2 := rfl
        have p01 : (n + 1) % 2 = (n + 1) % 2 := rfl
        rw [ite_eq_left p12, ite_eq_left p01]
        have f1 : (n + 2 - (n + 2)) / 2 = 0 := by omega
        have f2 : (n + 1 - (n + 1)) / 2 = 0 := by omega
        rw [f1, f2, Nat.choose_zero_right, Nat.choose_zero_right]
        have ePow : (2 : ℤ) ^ (n + 2) = 2 * (2 : ℤ) ^ (n + 1) := by
          rw [show n + 2 = (n + 1) + 1 from by omega, pow_succ']
        rw [ePow]
        simp

private lemma chebyshevU_coeff_aux (n k : ℕ) (hk : k ≤ n) :
    (Polynomial.Chebyshev.U ℤ ((n : ℕ) : ℤ)).coeff k =
      if n % 2 = k % 2 then (-1 : ℤ) ^ ((n - k) / 2) *
        ((Nat.choose ((n + k) / 2) ((n - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
      else 0 := by
  suffices H : ∀ n : ℕ, (∀ k : ℕ, k ≤ n →
      (Polynomial.Chebyshev.U ℤ ((n : ℕ) : ℤ)).coeff k =
        if n % 2 = k % 2 then (-1 : ℤ) ^ ((n - k) / 2) *
          ((Nat.choose ((n + k) / 2) ((n - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
        else 0)
      ∧ (∀ k : ℕ, k ≤ n + 1 →
      (Polynomial.Chebyshev.U ℤ (((n + 1 : ℕ)) : ℤ)).coeff k =
        if (n + 1) % 2 = k % 2 then (-1 : ℤ) ^ (((n + 1) - k) / 2) *
          ((Nat.choose (((n + 1) + k) / 2) (((n + 1) - k) / 2) : ℕ) : ℤ) * (2 : ℤ) ^ k
        else 0) from (H n).1 k hk
  intro n
  induction n with
  | zero =>
    refine ⟨chebyshevU_coeff_aux_base0, ?_⟩
    intro k hk
    simp only [Nat.zero_add] at hk ⊢
    exact chebyshevU_coeff_aux_base1 k hk
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    intro k hk
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e] at hk ⊢
    exact chebyshevU_coeff_aux_step n ih.1 ih.2 k hk

/--
**Coefficients of the Chebyshev polynomials of the second kind.** Let $U_n \in \mathbb{Z}[x]$
denote the $n$-th Chebyshev polynomial of the second kind, and let $k \le n$ be natural numbers.
If $n$ and $k$ have the same parity, the coefficient of $x^k$ in $U_n$ is
$(-1)^{(n-k)/2} \sum_{i=0}^{k} \binom{(n+k)/2}{i} \binom{(n+k)/2 - i}{(n-k)/2}$;
otherwise it is $0$.

Source: Milan Janjić, "On a Class of Polynomials with Integer Coefficients", Journal of Integer Sequences 11 (2008), Article 08.5.2, Corollary lines 441-446, <https://cs.uwaterloo.ca/journals/JIS/VOL11/Janjic/janjic19.tex>.
Proves `Wanted` entry `chebyshevU_coeff_eq_binomial_sum`.
-/
theorem chebyshevU_coeff_eq_binomial_sum
    (n k : ℕ) (hk : k ≤ n) :
    (Polynomial.Chebyshev.U ℤ (n : ℤ)).coeff k =
      if n % 2 = k % 2 then
        (-1 : ℤ) ^ ((n - k) / 2) *
          ∑ i ∈ Finset.range (k + 1),
            ((Nat.choose ((n + k) / 2) i : ℕ) : ℤ) *
              ((Nat.choose ((n + k) / 2 - i) ((n - k) / 2) : ℕ) : ℤ)
      else 0 := by
  have haux := chebyshevU_coeff_aux n k hk
  by_cases hpar : n % 2 = k % 2
  · rw [ite_eq_left hpar, haux, ite_eq_left hpar]
    have hsk : (n + k) / 2 = (n - k) / 2 + k := by omega
    have hsum := sum_choose_mul_eq_int ((n + k) / 2) ((n - k) / 2) k hsk
    rw [hsum]
    ring
  · rw [ite_eq_right hpar, haux, ite_eq_right hpar]

end MetaMathlibExt
