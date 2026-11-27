/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Finset.Basic

/-!
# Criterion for a uniform bound on the least non-vanishing Bernoulli index

This module proves `exists_bound_bernoulli_iff_finite_iInter`: there is a bound `M` such that
every prime `p ≥ 5` has an odd `k` with `3 ≤ k ≤ M`, `k < p` and `p ∤ num(B_{p-k})` if and
only if, for some `M ≥ 5`, only finitely many primes `p` satisfy `k < p` and
`p ∣ num(B_{p-k})` for every odd `k` with `3 ≤ k ≤ M`.

Statements from Shin-ichiro Seki, *Regular Primes, Non-Wieferich Primes, and Finite
Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22 (arXiv:2310.06809).
-/

namespace MetaMathlibExt

/-- **Criterion for a uniform bound on the least non-vanishing Bernoulli index.** The following
are equivalent:
(a) there is a natural number $M$ such that for every prime $p \ge 5$ there is an odd integer
$k$ with $3 \le k \le M$, $k < p$ and $p \nmid \operatorname{num}(B_{p-k})$;
(b) there is a natural number $M \ge 5$ such that only finitely many primes $p$ satisfy $k < p$
and $p \mid \operatorname{num}(B_{p-k})$ for every odd integer $k$ with $3 \le k \le M$.

Here $B_n$ is the $n$-th Bernoulli number, with $B_1 = +1/2$ (only even indices $n \ge 2$ occur),
and $\operatorname{num}(B_n)$ is its numerator in lowest terms.

Condition (a) says that the least such $k$, the source's $g_p$, is bounded uniformly in $p$;
condition (b) says that $\bigcap_{3 \le k \le M,\ k \text{ odd}} I(k)$ is finite, where $I(k)$ is
the set of primes $p > k$ with $p \mid \operatorname{num}(B_{p-k})$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 4 (`integers-2024-A22-lem-4`). -/
public theorem exists_bound_bernoulli_iff_finite_iInter :
    (∃ M : ℕ, ∀ p : ℕ, p.Prime → 5 ≤ p →
        ∃ k, Odd k ∧ 3 ≤ k ∧ k ≤ M ∧ k < p ∧ ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num) ↔
      ∃ M : ℕ, 5 ≤ M ∧
        {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 M, Odd k →
          k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num}.Finite := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max M 5, le_max_right _ _, ?_⟩
    have hsub : {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 (max M 5), Odd k →
        k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num} ⊆ {i | i < 5} := by
      intro p hp
      change p < 5
      by_contra hcon
      push Not at hcon
      obtain ⟨k, hkodd, hk3, hkM, hkp, hkndvd⟩ := hM p hp.1 hcon
      have hmem : k ∈ Finset.Icc 3 (max M 5) :=
        Finset.mem_Icc.mpr ⟨hk3, le_trans hkM (le_max_left _ _)⟩
      have hdiv := (hp.2 k hmem hkodd).2
      exact hkndvd hdiv
    exact (Set.finite_lt_nat 5).subset hsub
  · rintro ⟨M, hM5, hFin⟩
    obtain ⟨B, hB⟩ := hFin.bddAbove
    rw [mem_upperBounds] at hB
    refine ⟨max M B, fun p hpPrime hp5 => ?_⟩
    by_cases hle : p ≤ max M B
    · have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
      have h2le : 2 ≤ p := by omega
      have hkOdd : Odd (p - 2) := Nat.Odd.sub_even h2le hpOdd even_two
      have hsub : p - (p - 2) = 2 := by omega
      have hnum : (bernoulli' 2).num = 1 := by
        have h2 : bernoulli' 2 = bernoulli 2 :=
          (bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1)).symm
        rw [h2, bernoulli_two, Rat.inv_ofNat_num]
      refine ⟨p - 2, hkOdd, by omega, le_trans (Nat.sub_le _ _) hle, by omega, ?_⟩
      rw [hsub, hnum]
      intro hdvd
      rw [Int.natCast_dvd] at hdvd
      simp at hdvd
      omega
    · push Not at hle
      have hMB : M ≤ max M B := le_max_left _ _
      have hBB : B ≤ max M B := le_max_right _ _
      have hMp : M < p := lt_of_le_of_lt hMB hle
      have hBp : B < p := lt_of_le_of_lt hBB hle
      have hpNotMem : p ∉ {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 M, Odd k →
          k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num} := by
        intro hmem
        have hleB := hB p hmem
        omega
      have hNotForall : ¬ ∀ k ∈ Finset.Icc 3 M, Odd k →
          k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num := by
        intro hall
        exact hpNotMem ⟨hpPrime, hall⟩
      push Not at hNotForall
      obtain ⟨k, hkmem, hkodd, hknot⟩ := hNotForall
      have hkM : k ≤ M := (Finset.mem_Icc.mp hkmem).2
      have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hkmem).1
      have hkp : k < p := lt_of_le_of_lt hkM hMp
      have hndvd : ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num :=
        fun hdvd => hknot hkp hdvd
      exact ⟨k, hkodd, hk3, le_trans hkM hMB, hkp, hndvd⟩

end MetaMathlibExt
