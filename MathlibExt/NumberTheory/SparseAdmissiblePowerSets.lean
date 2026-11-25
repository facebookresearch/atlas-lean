/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Int.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Preorder.Finite

/-!
# Sparse subsets of powers with no prime translate

Powers of an integer that is a primitive root modulo infinitely many primes contain
arbitrarily sparse infinite subsets with no prime translate.

Theorem 1 of Desmond Weisenberg, *Sparse Admissible Sets and a Problem of Erdős and Graham*,
INTEGERS 24 (2024), Article A89 (the set `S` read from arXiv:2405.12310v2). Its closing
consequence, the refutation of Erdős Problem 429, is `erdos429_refuted` in
`WantedExt/NumberTheory/ErdosProblem429Wanted.lean`.
-/

namespace MetaMathlibExt

namespace exists_sparse_subset_pow_no_prime_translate

/-- For each shift there is a prime that divides arbitrarily late shifted powers. -/
private theorem exists_prime_dvd_powers {a : ℕ} (ha : 1 < a)
    (hprim : {p : ℕ | p.Prime ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}.Infinite) (n : ℤ) :
    ∃ p : ℕ, p.Prime ∧ ∀ B : ℕ, ∃ k : ℕ, B < k ∧ (a : ZMod p) ^ k + (n : ZMod p) = 0 := by
  by_cases hn : n = 0
  · subst n
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (ne_of_gt ha)
    have haz : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).mpr hpa
    exact ⟨p, hp, fun B => ⟨B + 1, Nat.lt_succ_self B, by simp [haz]⟩⟩
  · obtain ⟨p, ⟨hp, hroot⟩, hnp⟩ := hprim.exists_gt n.natAbs
    have hp₂ := hp.two_le
    have horder : 1 ≤ p - 1 := by omega
    let _ : Fact p.Prime := ⟨hp⟩
    let _ : NeZero (p - 1) := ⟨Nat.ne_of_gt horder⟩
    have hnz : (n : ZMod p) ≠ 0 := by
      intro hzero
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hzero
      exact (not_le_of_gt hnp) (by simpa using Int.natAbs_le_of_dvd_ne_zero hd hn)
    obtain ⟨i, -, hi⟩ := hroot.eq_pow_of_pow_eq_one
      (ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr hnz))
    refine ⟨p, hp, fun B => ⟨i + (p - 1) * (B + 1), ?_, ?_⟩⟩
    · have hmultiple : B + 1 ≤ (p - 1) * (B + 1) := by
        simpa using Nat.mul_le_mul_right (B + 1) horder
      omega
    · rw [pow_add, pow_mul, hroot.pow_eq_one, one_pow, mul_one, hi, neg_add_cancel]

/-- A power can be made large enough that its shift is strictly larger than a prime divisor. -/
private theorem exists_large_power {a : ℕ} (ha : 1 < a)
    (hprim : {p : ℕ | p.Prime ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}.Infinite)
    (n : ℤ) (B : ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ B < a ^ k ∧ ¬ ∃ q : ℕ, q.Prime ∧ (q : ℤ) = (a ^ k : ℕ) + n := by
  obtain ⟨p, hp, hdiv⟩ := exists_prime_dvd_powers ha hprim n
  obtain ⟨k, hk, hz⟩ := hdiv (max B (p + n.natAbs))
  have hpow : max B (p + n.natAbs) < a ^ k := hk.trans (Nat.lt_pow_self ha)
  refine ⟨k, by omega, (le_max_left _ _).trans_lt hpow, ?_⟩
  rintro ⟨q, hq, heq⟩
  have hqz : (q : ZMod p) = 0 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod p)) heq
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_natCast, Nat.cast_pow, hz] using hcast
  have hpq := (Nat.prime_dvd_prime_iff_eq hp hq).mp ((ZMod.natCast_eq_zero_iff q p).mp hqz)
  have hbig := (le_max_right B (p + n.natAbs)).trans_lt hpow
  have hnabs : -n ≤ (n.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
  omega

end exists_sparse_subset_pow_no_prime_translate

@[expose] public section

/-- **Sparse subsets of powers with no prime translate.** Let $a$ be a natural number that is a
primitive root modulo infinitely many primes, and let $S = \{a^k : k \ge 1\}$. For every
non-decreasing unbounded function $f : \mathbb{N} \to \mathbb{N}$ there is an infinite set
$A \subseteq S$ such that $|A \cap \{1, \dots, N\}| \le f(N)$ for every natural number $N$, and
such that no translate $A + n$ with $n \in \mathbb{Z}$ consists entirely of (positive) primes.

The hypothesis forces $a \ge 2$. The exponent range $k \ge 1$ is the reading in which the
paper's remark "$S$ is admissible" holds: with $k = 0$ and $a$ even, $S$ contains $1$ and $a$,
which meet both residue classes modulo $2$.

Source: Desmond Weisenberg, *Sparse Admissible Sets and a Problem of Erdős and Graham*,
INTEGERS 24 (2024), Article A89, Theorem 1 (`integers-2024-A89-thm-1`). -/
public theorem exists_sparse_subset_pow_no_prime_translate {a : ℕ}
    (hprim : {p : ℕ | p.Prime ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}.Infinite)
    {f : ℕ → ℕ} (hmono : Monotone f) (hunb : ∀ M : ℕ, ∃ N : ℕ, M ≤ f N) :
    ∃ A : Set ℕ, A.Infinite ∧ A ⊆ {m | ∃ k : ℕ, 1 ≤ k ∧ m = a ^ k} ∧
      (∀ N : ℕ, (A ∩ Set.Icc 1 N).ncard ≤ f N) ∧
      ¬ ∃ n : ℤ, ∀ m ∈ A, ∃ p : ℕ, p.Prime ∧ (p : ℤ) = m + n := by
  have ha : 1 < a := by
    obtain ⟨p, ⟨hp, hroot⟩, hpgt⟩ := hprim.exists_gt 2
    let _ : Fact p.Prime := ⟨hp⟩
    have ha₀ : a ≠ 0 := fun h => hroot.ne_zero (by omega) (by simp [h])
    have ha₁ : a ≠ 1 := fun h => hroot.ne_one (by omega) (by simp [h])
    omega
  -- Index the shifts by naturals, taking each power above its index and the sparsity threshold.
  let shift : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  have hstep (j : ℕ) : ∃ m : ℕ, j < m ∧ (∃ k : ℕ, 1 ≤ k ∧ m = a ^ k) ∧
      j + 1 ≤ f m ∧ ¬ ∃ p : ℕ, p.Prime ∧ (p : ℤ) = m + shift j := by
    obtain ⟨N, hN⟩ := hunb (j + 1)
    obtain ⟨k, hk, hlarge, hshift⟩ :=
      exists_sparse_subset_pow_no_prime_translate.exists_large_power ha hprim (shift j) (max j N)
    exact ⟨a ^ k, (le_max_left _ _).trans_lt hlarge, ⟨k, hk, rfl⟩,
      hN.trans (hmono ((le_max_right _ _).trans hlarge.le)), hshift⟩
  choose s hs_large hs_pow hs_count hs_shift using hstep
  refine ⟨Set.range s, Set.infinite_of_forall_exists_gt
    (fun j => ⟨s j, Set.mem_range_self j, hs_large j⟩), ?_, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact hs_pow j
  · intro N
    have hsub : Set.range s ∩ Set.Icc 1 N ⊆ s '' Set.Iio (f N) := by
      rintro _ ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, (hs_count j).trans (hmono hj.2), rfl⟩
    have hfin := Set.finite_Iio (f N)
    calc
      (Set.range s ∩ Set.Icc 1 N).ncard ≤ (s '' Set.Iio (f N)).ncard :=
        Set.ncard_le_ncard hsub (hfin.image s)
      _ ≤ (Set.Iio (f N)).ncard := Set.ncard_image_le hfin
      _ = f N := Set.ncard_Iio_nat _
  · rintro ⟨n, hn⟩
    obtain ⟨j, rfl⟩ := shift.surjective n
    exact hs_shift j (hn (s j) (Set.mem_range_self j))

end

end MetaMathlibExt
