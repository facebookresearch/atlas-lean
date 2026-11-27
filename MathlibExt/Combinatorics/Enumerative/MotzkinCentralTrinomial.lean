/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.TrinomialCoefficient
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Coeff

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-! # Recurrence linking Motzkin numbers and central trinomial coefficients

This file gives a binomial-sum formula for central trinomial coefficients and uses it to prove
their recurrence with the Catalan-weighted sums defining the Motzkin numbers.
-/

private theorem motzkinTri_trinomialCoefficient_self_eq_sum_range (n : ℕ) :
    trinomialCoefficient n n =
      ∑ k ∈ Finset.range (n + 1), n.choose k * (n - k).choose k := by
  rw [trinomialCoefficient]
  have hbase : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) =
      1 + (Polynomial.X + Polynomial.X ^ 2) := by
    exact add_assoc _ _ _
  rw [hbase, add_pow, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  have hpoly : (Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) =
      Polynomial.X * (1 + Polynomial.X) := by
    ring
  rw [hpoly, mul_pow]
  simp only [one_pow, one_mul]
  rw [Polynomial.coeff_mul_natCast]
  rw [Polynomial.coeff_X_pow_mul']
  simp only [Nat.sub_le, ite_true, Polynomial.coeff_one_add_X_pow, Nat.cast_id]
  rw [Nat.sub_sub_self hkn]
  exact Nat.mul_comm _ _

/-- **Central trinomial coefficients as a binomial sum.** For every natural number $n$, the
coefficient of $X^n$ in $(1 + X + X^2)^n$ equals
$\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \binom{2k}{k}$. -/
public theorem trinomialCoefficient_self_eq_sum (n : ℕ) :
    trinomialCoefficient n n =
      ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * (2 * k).choose k := by
  rw [motzkinTri_trinomialCoefficient_self_eq_sum_range]
  calc
    (∑ k ∈ Finset.range (n + 1), n.choose k * (n - k).choose k) =
        ∑ k ∈ Finset.range (n / 2 + 1), n.choose k * (n - k).choose k := by
      apply (Finset.sum_subset ?_ ?_).symm
      · intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro k hk hnot
        simp only [Finset.mem_range] at hk hnot
        rw [Nat.choose_eq_zero_of_lt (by omega : n - k < k), Nat.mul_zero]
    _ = ∑ k ∈ Finset.range (n / 2 + 1),
        n.choose (2 * k) * (2 * k).choose k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hchoose := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
      have hsub : 2 * k - k = k := by omega
      rw [hsub] at hchoose
      exact hchoose.symm

private theorem motzkinTri_trinomialCoefficient_self_eq_sum_range_of_le
    (n r : ℕ) (h : n / 2 + 1 ≤ r) :
    trinomialCoefficient n n =
      ∑ k ∈ Finset.range r, n.choose (2 * k) * (2 * k).choose k := by
  rw [trinomialCoefficient_self_eq_sum]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    simp only [Finset.mem_range] at hk hnot
    rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * k), Nat.zero_mul]

private theorem motzkinTri_pascal_term (n i : ℕ) :
    (n + 1).choose (2 * (i + 1)) * (2 * (i + 1)).choose (i + 1) =
      n.choose (2 * (i + 1)) * (2 * (i + 1)).choose (i + 1) +
        n.choose (2 * i + 1) * (2 * (i + 1)).choose (i + 1) := by
  have hidx : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
  rw [hidx, Nat.choose_succ_succ', Nat.add_mul]
  exact Nat.add_comm _ _

private theorem motzkinTri_pascal (n : ℕ) :
    trinomialCoefficient (n + 1) (n + 1) =
      trinomialCoefficient n n +
        ∑ i ∈ Finset.range (n + 1),
          n.choose (2 * i + 1) * (2 * i + 2).choose (i + 1) := by
  have hn1 := motzkinTri_trinomialCoefficient_self_eq_sum_range_of_le
    (n + 1) (n + 2) (by omega)
  have hn := motzkinTri_trinomialCoefficient_self_eq_sum_range_of_le
    n (n + 2) (by omega)
  rw [Finset.sum_range_succ'] at hn1 hn
  simp only [Nat.choose_zero_right, Nat.mul_zero, Nat.choose_self, Nat.one_mul] at hn1 hn
  have hodd :
      (∑ i ∈ Finset.range (n + 1),
          n.choose (2 * i + 1) * (2 * (i + 1)).choose (i + 1)) =
        ∑ i ∈ Finset.range (n + 1),
          n.choose (2 * i + 1) * (2 * i + 2).choose (i + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 2 * (i + 1) = 2 * i + 2 by omega]
  rw [hn1, hn]
  simp_rw [motzkinTri_pascal_term]
  rw [Finset.sum_add_distrib, hodd]
  omega

private theorem motzkinTri_central_choose_eq_catalan (i : ℕ) :
    (2 * i + 2).choose (i + 1) = 2 * (2 * i + 1) * catalan i := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < i + 1)
  have hbinom : (2 * i + 2).choose (i + 1) = Nat.centralBinom (i + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    congr 1
  rw [hbinom, Nat.succ_mul_centralBinom_succ,
    ← succ_mul_catalan_eq_centralBinom]
  ring

private theorem motzkinTri_term (n i : ℕ) (hn : 1 ≤ n) :
    n.choose (2 * i + 1) * (2 * i + 2).choose (i + 1) =
      2 * n * ((n - 1).choose (2 * i) * catalan i) := by
  have hnchoose := Nat.add_one_mul_choose_eq (n - 1) (2 * i)
  have hnsucc : n - 1 + 1 = n := by omega
  rw [hnsucc] at hnchoose
  rw [motzkinTri_central_choose_eq_catalan]
  calc
    n.choose (2 * i + 1) * (2 * (2 * i + 1) * catalan i) =
        2 * (n.choose (2 * i + 1) * (2 * i + 1)) * catalan i := by ring
    _ = 2 * (n * (n - 1).choose (2 * i)) * catalan i := by rw [← hnchoose]
    _ = 2 * n * ((n - 1).choose (2 * i) * catalan i) := by ring

private theorem motzkinTri_motzkin_eq_sum_range_of_le
    (M : ℕ → ℕ)
    (hM : ∀ n, M n =
      ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k)
    (n r : ℕ) (h : n / 2 + 1 ≤ r) :
    M n = ∑ k ∈ Finset.range r, n.choose (2 * k) * catalan k := by
  rw [hM]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    simp only [Finset.mem_range] at hk hnot
    rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * k), Nat.zero_mul]

/--
**Recurrence linking central trinomial coefficients and Motzkin numbers.** For $n \in \mathbb{N}$
let $T_n$ be the central trinomial coefficient, the coefficient of $X^n$ in $(1 + X + X^2)^n$.
Let $M : \mathbb{N} \to \mathbb{N}$ be any function with
$M_n = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} C_k$ for every $n$, where $C_k$ is the
$k$-th Catalan number (these sums are the Motzkin numbers). Then for every $n \ge 1$,
$T_{n+1} = T_n + 2n \, M_{n-1}$.

The source attributes the recurrence to Barcucci, Pinzani, and Sprugnoli, "The Motzkin family",
and proves it with hybrid-polynomial operator calculus; the proof here instead uses the binomial
sum for $T_n$ and an elementary termwise binomial identity.

Proves `Wanted` entry `motzkin_central_trinomial_recurrence`.

Source: P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky,
"Motzkin Numbers, Central Trinomial Coefficients and Hybrid Polynomials,"
Journal of Integer Sequences 11 (2008), Article 08.1.1, Theorem (equation
eq34), lines 459–464,
https://cs.uwaterloo.ca/journals/JIS/VOL11/Penson/penson131.tex
-/
public theorem motzkin_central_trinomial_recurrence
    (M : ℕ → ℕ)
    (hM : ∀ n, M n =
      ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalan k) :
    ∀ n, 1 ≤ n →
      trinomialCoefficient (n + 1) (n + 1) =
        trinomialCoefficient n n + 2 * n * M (n - 1) := by
  intro n hn
  rw [motzkinTri_pascal]
  have hMpadded := motzkinTri_motzkin_eq_sum_range_of_le
    M hM (n - 1) (n + 1) (by omega)
  have hcorrection :
      (∑ i ∈ Finset.range (n + 1),
          n.choose (2 * i + 1) * (2 * i + 2).choose (i + 1)) =
        2 * n * M (n - 1) := by
    calc
      (∑ i ∈ Finset.range (n + 1),
          n.choose (2 * i + 1) * (2 * i + 2).choose (i + 1)) =
          ∑ i ∈ Finset.range (n + 1),
            2 * n * ((n - 1).choose (2 * i) * catalan i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact motzkinTri_term n i hn
      _ = 2 * n *
          (∑ i ∈ Finset.range (n + 1), (n - 1).choose (2 * i) * catalan i) := by
        rw [Finset.mul_sum]
      _ = 2 * n * M (n - 1) := by rw [hMpadded]
  rw [hcorrection]

end

end MetaMathlibExt
