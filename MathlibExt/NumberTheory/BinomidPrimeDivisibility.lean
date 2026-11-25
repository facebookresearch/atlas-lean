/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.Combinatorics.Enumerative.TotienomialCoefficient
public import MathlibExt.NumberTheory.BinomidPartialSum
import Mathlib.Order.Preorder.Finite

/-!
# Prime divisibility of nomid coefficients

A binomid index that is not a lex-minimal extension gives infinitely many rows whose inner
nomid coefficients are all divisible by the prime used to form the sequence of prime powers.
-/

namespace MetaMathlibExt

namespace infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension

private theorem exists_strict_split_row {μ : ℕ → ℕ} (hμ : IsBinomidIndex μ)
    (hlex : ¬ IsLexMinimalExtension μ) (m : ℕ) :
    ∃ n, m < n ∧ ∀ k, 1 ≤ k → k < n →
      (∑ i ∈ Finset.range (n - k), μ i) + (∑ i ∈ Finset.range k, μ i) <
        ∑ i ∈ Finset.range n, μ i := by
  classical
  by_contra! h
  apply hlex
  refine ⟨m, hμ, fun γ hγ hagree => ?_⟩
  by_cases heq : μ = γ
  · exact Or.inl heq
  have hdiff := Function.ne_iff.mp heq
  let j := Nat.find hdiff
  have hj : μ j ≠ γ j := Nat.find_spec hdiff
  have hbefore (i : ℕ) (hi : i < j) : μ i = γ i := by
    by_contra hne
    exact Nat.find_min hdiff hi hne
  have hmj : m < j + 1 := by
    by_contra! hle
    exact hj (hagree j (by omega)).symm
  -- Both parts of the split use only entries before the first difference.
  obtain ⟨k, hk, hkn, hle⟩ := h (j + 1) hmj
  have hsum (l : ℕ) (hl : l ≤ j) :
      (∑ i ∈ Finset.range l, μ i) = ∑ i ∈ Finset.range l, γ i :=
    Finset.sum_congr rfl fun i hi => hbefore i ((Finset.mem_range.mp hi).trans_le hl)
  have hbound := (isBinomidIndex_iff_partialSum γ).1.mp hγ k (j + 1) hk hkn
  rw [← hsum _ (by omega), ← hsum k (by omega), Finset.sum_range_succ, ← hsum j le_rfl] at hbound
  rw [Finset.sum_range_succ] at hle
  exact Or.inr ⟨j, hbefore, by omega⟩

private theorem factorial_pow (μ : ℕ → ℕ) (p n : ℕ) :
    generalizedFactorial (fun i => p ^ μ (i - 1)) n = p ^ (∑ i ∈ Finset.range n, μ i) := by
  rw [generalizedFactorial, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [Nat.add_comm 1, Finset.prod_pow_eq_pow_sum]

end infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension

open infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension

/-- **Nomid coefficients of binomid indices that are not lex-minimal extensions.** Let
$\mu = (e_1, e_2, \dots)$ be a binomid index such that for no $m$ is $\mu$ the lex-minimal
extension of its first $m$ entries, and let $p$ be a prime. Write $f_i = p^{e_i}$ for $i \ge 1$
and let $[n, k]_f = \frac{f_n f_{n-1} \cdots f_{n-k+1}}{f_k f_{k-1} \cdots f_1}$ be the
$f$-nomid coefficient. Then there are infinitely many natural numbers $n$ such that for every $k$
with $1 \le k < n$ the coefficient $[n, k]_f$ is an integer multiple of $p$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 2
(`integers-2024-A53-cor-2`). -/
public theorem infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension
    {μ : ℕ → ℕ} (hμ : IsBinomidIndex μ) (hlex : ¬ IsLexMinimalExtension μ) {p : ℕ}
    (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
      generalizedBinomialCoefficient (fun i => p ^ μ (i - 1)) k (n - k) =
        (p : ℚ) * z}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  obtain ⟨n, hmn, hstrict⟩ :=
    exists_strict_split_row hμ hlex m
  refine ⟨n, ?_, hmn⟩
  intro k hk hkn
  let a := (∑ i ∈ Finset.range k, μ i) + (∑ i ∈ Finset.range (n - k), μ i)
  let b := ∑ i ∈ Finset.range n, μ i
  have hab : a < b := by simpa only [a, b, add_comm] using hstrict k hk hkn
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨(p : ℤ) ^ (b - a - 1), ?_⟩
  rw [generalizedBinomialCoefficient, Nat.add_sub_of_le hkn.le]
  simp only [factorial_pow, Nat.cast_pow, Int.cast_pow, Int.cast_natCast, ← pow_add]
  change (p : ℚ) ^ b / (p : ℚ) ^ a = (p : ℚ) * (p : ℚ) ^ (b - a - 1)
  rw [← pow_succ']
  apply (div_eq_iff (pow_ne_zero _ hpq)).2
  rw [← pow_add, show b - a - 1 + 1 + a = b by omega]

end MetaMathlibExt
