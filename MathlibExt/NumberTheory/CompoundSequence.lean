/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Deleting a term of a compound sequence

A compound sequence combines prefix products of one sequence with suffix products of another.
We characterize when the terms remaining after one deletion generate a numerical semigroup.
-/

namespace MetaMathlibExt

/-- **Compound sequence.** Let $n$ be a natural number and let $a = (a_i)$ and $b = (b_i)$ be
sequences of natural numbers. For a natural number $j$, the $j$-th term of the compound sequence
of $a$ and $b$ is
$$c_j = \Big(\prod_{i=1}^{j} b_i\Big) \Big(\prod_{i=j+1}^{n} a_i\Big),$$
so that $c_j = b_1 b_2 \cdots b_j \, a_{j+1} \cdots a_n$ for $0 \le j \le n$, the range of
interest; for $j > n$ the second product is empty and $c_j = b_1 \cdots b_j$.

Source: Edgar Federico Elizeche and Amitabha Tripathi, *A Note on Deletions from Compound
Sequences That Leave the Frobenius Number Invariant*, INTEGERS 25 (2025), Article A6,
Section 2, eq. (1) (after Kiers, O'Neill, and Ponomarenko). -/
@[expose] public def compoundSequence (n : ℕ) (a b : ℕ → ℕ) (j : ℕ) : ℕ :=
  (∏ i ∈ Finset.Icc 1 j, b i) * ∏ i ∈ Finset.Ioc j n, a i

/-- **First term of a compound sequence.** For every natural number $n$ and all sequences $a$, $b$
of natural numbers, the compound sequence $c$ of $a$ and $b$ satisfies $c_0 = a_1 a_2 \cdots a_n$.

Source: Edgar Federico Elizeche and Amitabha Tripathi, *A Note on Deletions from Compound
Sequences That Leave the Frobenius Number Invariant*, INTEGERS 25 (2025), Article A6,
Section 2, eq. (1). -/
public theorem compoundSequence_zero (n : ℕ) (a b : ℕ → ℕ) :
    compoundSequence n a b 0 = ∏ i ∈ Finset.Ioc 0 n, a i := by
  simp [compoundSequence]

/-- **Last term of a compound sequence.** For every natural number $n$ and all sequences $a$, $b$
of natural numbers, the compound sequence $c$ of $a$ and $b$ satisfies $c_n = b_1 b_2 \cdots b_n$.

Source: Edgar Federico Elizeche and Amitabha Tripathi, *A Note on Deletions from Compound
Sequences That Leave the Frobenius Number Invariant*, INTEGERS 25 (2025), Article A6,
Section 2, eq. (1). -/
public theorem compoundSequence_self (n : ℕ) (a b : ℕ → ℕ) :
    compoundSequence n a b n = ∏ i ∈ Finset.Icc 1 n, b i := by
  simp [compoundSequence]

namespace compoundSequence_erase_cofinite_iff

private theorem finite_compl_closure_iff {G : Set ℕ} :
    (AddSubmonoid.closure G : Set ℕ)ᶜ.Finite ↔ Nat.setGcd G = 1 := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := h.bddAbove
    have hmem {m : ℕ} (hm : N < m) : m ∈ AddSubmonoid.closure G := by
      by_contra hgap
      exact hm.not_ge (hN hgap)
    have hd := Nat.setGcd_dvd_of_mem_closure (hmem (Nat.lt_succ_self N))
    exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd).mpr
      (Nat.setGcd_dvd_of_mem_closure (hmem (show N < N + 1 + 1 by omega))))
  · intro hg
    obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge G
    apply (Finset.range N).finite_toSet.subset
    intro m hm
    exact Finset.mem_range.mpr (lt_of_not_ge fun hge ↦ hm (hN m hge (hg ▸ one_dvd _)))

private theorem prime_dvd_term_iff {n k p : ℕ} {a b : ℕ → ℕ} (hp : p.Prime) :
    p ∣ compoundSequence n a b k ↔
      (∃ i, (1 ≤ i ∧ i ≤ k) ∧ p ∣ b i) ∨ (∃ i, (k < i ∧ i ≤ n) ∧ p ∣ a i) := by
  simp only [compoundSequence, hp.dvd_mul, hp.prime.dvd_finsetProd_iff, Finset.mem_Icc,
    Finset.mem_Ioc]

private theorem prime_dvd_remaining_iff {n j p : ℕ} {a b : ℕ → ℕ} (hp : p.Prime)
    (hcop : ∀ i ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Icc 1 n, l ≤ i → Nat.Coprime (a i) (b l))
    (hj : j ≤ n) :
    (∀ k, k ≠ j → k ≤ n → p ∣ compoundSequence n a b k) ↔
      (0 < j → p ∣ a j) ∧ (j < n → p ∣ b (j + 1)) := by
  constructor
  · intro h
    -- At the last index with p ∣ a i (or zero), neither product has a factor divisible by p.
    let k := Nat.findGreatest (fun i ↦ p ∣ a i) n
    obtain ⟨hkn, hka, hafter⟩ := Nat.findGreatest_eq_iff.mp (show
      Nat.findGreatest (fun i ↦ p ∣ a i) n = k from rfl)
    have hbefore {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k) : ¬p ∣ b i := by
      have hki := hcop k (Finset.mem_Icc.mpr ⟨by omega, hkn⟩) i
        (Finset.mem_Icc.mpr ⟨hi.1, hi.2.trans hkn⟩) hi.2
      exact hp.coprime_iff_not_dvd.mp (hki.coprime_dvd_left (hka (by omega)))
    have hkj : k = j := by
      by_contra hne
      obtain ⟨i, hi, hd⟩ | ⟨i, hi, hd⟩ := (prime_dvd_term_iff hp).mp (h k hne hkn)
      · exact hbefore hi hd
      · exact hafter hi.1 hi.2 hd
    subst j
    refine ⟨fun hk ↦ hka hk.ne', fun hk ↦ ?_⟩
    obtain ⟨i, hi, hd⟩ | ⟨i, hi, hd⟩ := (prime_dvd_term_iff hp).mp
      (h (k + 1) (by omega) hk)
    · by_cases hik : i ≤ k
      · exact (hbefore ⟨hi.1, hik⟩ hd).elim
      · rwa [show k + 1 = i by omega]
    · exact (hafter (by omega) hi.2 hd).elim
  · rintro ⟨ha, hb⟩ k hne hk
    apply (prime_dvd_term_iff hp).mpr
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr ⟨j, ⟨hlt, hj⟩, ha (by omega)⟩
    · exact Or.inl ⟨j + 1, ⟨by omega, hgt⟩, hb (by omega)⟩

end compoundSequence_erase_cofinite_iff

open compoundSequence_erase_cofinite_iff in
/-- **When deleting a term of a compound sequence leaves a numerical semigroup.** Let $n \ge 1$
and let $a_1, \dots, a_n$ and $b_1, \dots, b_n$ be natural numbers with $0 < a_i < b_i$ for
$1 \le i \le n$ and $\gcd(a_i, b_j) = 1$ whenever $1 \le j \le i \le n$; let $c_0, \dots, c_n$
be their compound sequence. For $0 \le j \le n$, the additive submonoid of $\mathbb{N}$
generated by the terms $c_i$ with $0 \le i \le n$ and $i \ne j$ has finite complement in
$\mathbb{N}$ (so it is a numerical semigroup) if and only if either $0 < j < n$ and
$\gcd(a_j, b_{j+1}) = 1$, or $j = n$ and $a_n = 1$.

Source: Edgar Federico Elizeche and Amitabha Tripathi, *A Note on Deletions from Compound
Sequences That Leave the Frobenius Number Invariant*, INTEGERS 25 (2025), Article A6,
Proposition 3 (`integers-2025-A6-prop-3`). -/
public theorem compoundSequence_erase_cofinite_iff (n : ℕ) (hn : 1 ≤ n) (a b : ℕ → ℕ)
    (hab : ∀ i ∈ Finset.Icc 1 n, 0 < a i ∧ a i < b i)
    (hcop : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, j ≤ i → Nat.Coprime (a i) (b j))
    (j : ℕ) (hj : j ≤ n) :
    (AddSubmonoid.closure ((((Finset.range (n + 1)).erase j).image (compoundSequence n a b) :
        Finset ℕ) : Set ℕ) : Set ℕ)ᶜ.Finite ↔
      (0 < j ∧ j < n ∧ Nat.Coprime (a j) (b (j + 1))) ∨ (j = n ∧ a j = 1) := by
  rw [finite_compl_closure_iff, Nat.eq_one_iff_not_exists_prime_dvd]
  simp only [Nat.dvd_setGcd_iff, Finset.mem_coe, Finset.forall_mem_image,
    Finset.mem_erase, Finset.mem_range, Nat.lt_succ_iff, and_imp]
  conv_lhs =>
    intro p hp
    rw [prime_dvd_remaining_iff hp hcop hj]
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · have h₁ := hab 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
    have hn' : 0 < n := hn
    simp [hn', hn'.ne, ← Nat.eq_one_iff_not_exists_prime_dvd, show b 1 ≠ 1 by omega]
  · rcases lt_or_eq_of_le hj with hlt | rfl
    · simp [hpos, hlt, hlt.ne, Nat.eq_one_iff_not_exists_prime_dvd, Nat.dvd_gcd_iff]
    · simp [hpos, ← Nat.eq_one_iff_not_exists_prime_dvd]

end MetaMathlibExt
