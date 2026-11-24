/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.Finite.Basic

/-!
# Square-weighted zero-sum free unit pairs modulo the prime divisors of an odd number

For a natural number $n$, write $S(n)$ for the set of nonzero squares in $\mathbb{Z}/n\mathbb{Z}$.
A sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}/n\mathbb{Z}$ has an $A$-weighted zero-sum
subsequence when there are a nonempty set $J$ of indices and weights $a_i \in A$ for $i \in J$
with $\sum_{i \in J} a_i x_i = 0$.

This file proves Proposition 17 of Paul and Paul: for odd $n \ge 2$ there are units $u, v$ of
$\mathbb{Z}/n\mathbb{Z}$ such that, for every prime $p$ dividing $n$, the reduction
$(u \bmod p, v \bmod p)$ has no $S(p)$-weighted zero-sum subsequence.

## Main definitions

* `MetaMathlibExt.squareSet`: the set $S(n)$ of nonzero squares of $\mathbb{Z}/n\mathbb{Z}$.
* `MetaMathlibExt.HasWeightedZeroSumSubseq`: a finite sequence in $\mathbb{Z}/n\mathbb{Z}$ has an
  $A$-weighted zero-sum subsequence.

## Main results

* `MetaMathlibExt.exists_pair_units_avoiding_prime_squareWeights`: Proposition 17.

## Implementation notes

As in the paper, the pair is assembled from one pair modulo each prime divisor by the Chinese
remainder theorem. Modulo an odd prime $p$ we take the pair $(1, c_p)$, where $-c_p$ is not a
square: a single nonzero term has no weighted zero sum, and $a \cdot 1 + b c_p = 0$ with nonzero
squares $a, b$ would make $-c_p = a / b$ a square. So $u = 1$, and $v$ is congruent to $c_p$
modulo every prime $p \mid n$.

## References

* Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
  Sequences 27 (2024), Article 24.6.6; arXiv:2202.13143.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nonzero squares modulo $n$.** For a natural number $n$, $S(n)$ is the set of elements $x$
of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ with $x \neq 0$ and $x = y^2$ for some
$y \in \mathbb{Z}_n$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def squareSet (n : ℕ) : Set (ZMod n) := {x | x ≠ 0 ∧ ∃ y, x = y ^ 2}

/-- **Weighted zero-sum subsequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ has an $A$-weighted
zero-sum subsequence if there are a nonempty set $J \subseteq \{1, \dots, k\}$ of indices and
weights $a_i \in A$ for $i \in J$ with $\sum_{i \in J} a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

end

/-- Modulo an odd prime $p$, some natural number $c$ has $-c$ not a square. -/
private lemma exists_natCast_neg_not_isSquare {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ c : ℕ, ¬IsSquare (-(c : ZMod p)) := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare ((ZMod.ringChar_zmod_n p).trans_ne hp2)
  refine ⟨(-a).val, ?_⟩
  rwa [ZMod.natCast_zmod_val, neg_neg]

/-- Modulo a prime $p$, if $-c$ is not a square, then the pair $(1, c)$ has no $S(p)$-weighted
zero-sum subsequence. -/
private lemma not_hasWeightedZeroSumSubseq_one_pair {p : ℕ} [Fact p.Prime] {c : ZMod p}
    (hc : ¬IsSquare (-c)) : ¬HasWeightedZeroSumSubseq (squareSet p) ![1, c] := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by simp⟩
  rintro ⟨J, ⟨j, hj⟩, a, ha, hsum⟩
  rw [← Finset.univ_inter J, ← Finset.sum_ite_mem, Fin.sum_univ_two] at hsum
  by_cases h0 : (0 : Fin 2) ∈ J <;> by_cases h1 : (1 : Fin 2) ∈ J
  · -- Both terms: `y ^ 2 + z ^ 2 * c = 0` with `z ≠ 0` makes `-c = (y / z) ^ 2` a square.
    obtain ⟨-, y, hy⟩ := ha 0 h0
    obtain ⟨ha1, z, hz⟩ := ha 1 h1
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [hz] at ha1
    simp only [h0, h1, ite_true, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, hy, hz]
      at hsum
    refine hc ⟨y / z, ?_⟩
    field_simp
    linear_combination -hsum
  · -- Only the first term: its weight would vanish.
    obtain ⟨ha0, -⟩ := ha 0 h0
    simp only [h0, h1, ite_true, ite_false, Matrix.cons_val_zero, mul_one, add_zero] at hsum
    exact ha0 hsum
  · -- Only the second term: a product of two nonzero elements of a field would vanish.
    obtain ⟨ha1, -⟩ := ha 1 h1
    simp only [h0, h1, ite_true, ite_false, Matrix.cons_val_one, zero_add] at hsum
    exact mul_ne_zero ha1 hc0 hsum
  · -- No term: the index set would be empty.
    fin_cases j <;> simp_all

/-- **Two units without square-weighted zero sums modulo any prime divisor.** Let $n \ge 2$ be
odd, and write $S(m)$ for the set of nonzero squares in $\mathbb{Z}/m\mathbb{Z}$. Then there are
units $u, v$ of $\mathbb{Z}/n\mathbb{Z}$ such that for every prime $p$ dividing $n$, the sequence
$(u \bmod p, v \bmod p)$ in $\mathbb{Z}/p\mathbb{Z}$ has no $S(p)$-weighted zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Proposition 17. -/
public theorem exists_pair_units_avoiding_prime_squareWeights (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) :
    ∃ u v : ZMod n, IsUnit u ∧ IsUnit v ∧
      ∀ p : ℕ, p.Prime → p ∣ n →
        ¬HasWeightedZeroSumSubseq (squareSet p)
          (fun i : Fin 2 => (ZMod.cast (![u, v] i) : ZMod p)) := by
  have hn0 : n ≠ 0 := by omega
  -- Every prime factor `p` of `n` is odd, so some `c p` has `-c p` not a square modulo `p`.
  have hodd : ∀ p ∈ n.primeFactors, p ≠ 2 := by
    rintro p hp rfl
    exact Nat.not_even_iff_odd.mpr hnOdd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  choose! c hc using fun p (hp : p ∈ n.primeFactors) =>
    exists_natCast_neg_not_isSquare (Nat.prime_of_mem_primeFactors hp) (hodd p hp)
  -- The Chinese remainder theorem gives `k` with `k ≡ c p [MOD p]` for every prime factor `p`.
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset c id n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  have hkp : ∀ p ∈ n.primeFactors, (k : ZMod p) = c p := fun p hp =>
    (ZMod.natCast_eq_natCast_iff k (c p) p).mpr (hk p hp)
  refine ⟨1, k, isUnit_one, (ZMod.isUnit_iff_coprime k n).mpr ?_, fun p hp hpn => ?_⟩
  · -- A common prime factor `q` of `k` and `n` would make `-c q ≡ -k ≡ 0` a square modulo `q`.
    refine Nat.coprime_of_dvd fun q hq hqk hqn => ?_
    have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩
    apply hc q hqmem
    rw [← hkp q hqmem, (ZMod.natCast_eq_zero_iff k q).mpr hqk, neg_zero]
    exact ⟨0, by simp⟩
  · -- Modulo `p` the pair is `(1, c p)`.
    have := Fact.mk hp
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
    have hS : (fun i : Fin 2 => (ZMod.cast (![(1 : ZMod n), (k : ZMod n)] i) : ZMod p)) =
        ![1, (c p : ZMod p)] := by
      funext i
      fin_cases i
      · simp [ZMod.cast_one hpn]
      · simp [ZMod.cast_natCast hpn, hkp p hpmem]
    rw [hS]
    exact not_hasWeightedZeroSumSubseq_one_pair (hc p hpmem)

end MetaMathlibExt
