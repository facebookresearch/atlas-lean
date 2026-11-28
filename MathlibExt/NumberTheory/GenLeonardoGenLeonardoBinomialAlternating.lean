/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import MathlibExt.NumberTheory.GenLeonardo
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

/-!
# Alternating binomial identities for generalized Leonardo numbers

For an integer `k`, let `L_{k,n} = genLeonardo k n` and `M_{k,n} = genLeonardoCompanion k n`.
For all natural numbers `n ≥ 1` and `r`,
`∑ i ∈ Finset.range (n + 1), C(n,i) (-1)^(n-i) L_{k,2i+r} = L_{k,n+r} + k` and
`∑ i ∈ Finset.range (n + 1), C(n,i) (-1)^(n-i) M_{k,2i+r} = M_{k,n+r} + 2k`
(`genLeonardo_binomial_alternating`).

The shifted sequences `L_{k,n} + k` and `M_{k,n} + 2 * k` both satisfy the Fibonacci
recurrence, for which the step-two alternating binomial transform is the shift by the order;
the constant shifts contribute nothing since alternating Pascal row sums vanish for `n ≥ 1`.

## References

* Kantaphon Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, The Fibonacci Quarterly 62
  (2024), no. 3, 201–207, Theorem 3.3, the source of the statement.
-/

namespace MetaMathlibExt

/-- If `A (n + 2) = A (n + 1) + A n` for all `n`, then the alternating binomial sum of `A`
with step two equals the shift of `A` by the order. -/
private theorem alt_sum_fib_rec {R : Type*} [CommRing R] (A : ℕ → R)
    (hA : ∀ n, A (n + 2) = A (n + 1) + A n) :
    ∀ n r : ℕ, ∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + r) = A (n + r) := by
  intro n
  induction n with
  | zero =>
    intro r
    simp
  | succ n IH =>
    intro r
    have pascal : ∀ i : ℕ, (Nat.choose (n + 1) (i + 1) : R)
        * (-1 : R) ^ (n + 1 - (i + 1)) * A (2 * (i + 1) + r)
        = (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + (r + 2))
          + (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - i) * A (2 * (i + 1) + r) := by
      intro i
      have hP : Nat.choose (n + 1) (i + 1) = Nat.choose n i + Nat.choose n (i + 1) :=
        Nat.choose_succ_succ n i
      have he : n + 1 - (i + 1) = n - i := by omega
      have hAidx : 2 * i + (r + 2) = 2 * (i + 1) + r := by ring
      rw [hP, he, hAidx, Nat.cast_add]
      ring
    have hLHS : (∑ i ∈ Finset.range (n + 1 + 1),
          (Nat.choose (n + 1) i : R) * (-1 : R) ^ (n + 1 - i) * A (2 * i + r))
        = (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + (r + 2)))
          + (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - i) * A (2 * (i + 1) + r))
          + (Nat.choose (n + 1) 0 : R) * (-1 : R) ^ (n + 1 - 0) * A (2 * 0 + r) := by
      have h : (∑ i ∈ Finset.range (n + 1),
            (Nat.choose (n + 1) (i + 1) : R) * (-1 : R) ^ (n + 1 - (i + 1)) *
              A (2 * (i + 1) + r))
          = (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + (r + 2)))
            + (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - i) * A (2 * (i + 1) + r)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => pascal i)
      rw [Finset.sum_range_succ', h]
    have hS2top : (Nat.choose n (n + 1) : R) * (-1 : R) ^ (n - n) * A (2 * (n + 1) + r)
        = 0 := by
      have hz : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      simp
    have hneg : ∀ i ∈ Finset.range n,
        (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - i) * A (2 * (i + 1) + r)
        = -((Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - (i + 1))
          * A (2 * (i + 1) + r)) := by
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have he : n - i = (n - (i + 1)) + 1 := by omega
      rw [he, pow_succ']
      ring
    have hS2 : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - i) * A (2 * (i + 1) + r))
        = -(∑ i ∈ Finset.range n,
          (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - (i + 1))
            * A (2 * (i + 1) + r)) := by
      rw [Finset.sum_range_succ, hS2top, add_zero, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i hi => hneg i hi)
    have hSn : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + r))
        = (∑ i ∈ Finset.range n,
            (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - (i + 1))
              * A (2 * (i + 1) + r))
          + (Nat.choose n 0 : R) * (-1 : R) ^ (n - 0) * A (2 * 0 + r) := by
      rw [Finset.sum_range_succ']
    have hpow : (Nat.choose (n + 1) 0 : R) * (-1 : R) ^ (n + 1 - 0) * A (2 * 0 + r)
        + (Nat.choose n 0 : R) * (-1 : R) ^ (n - 0) * A (2 * 0 + r) = 0 := by
      rw [Nat.choose_zero_right, Nat.choose_zero_right, Nat.sub_zero, Nat.sub_zero, pow_succ']
      ring
    have e1 : n + (r + 2) = (n + r) + 2 := by omega
    have e2 : n + 1 + r = (n + r) + 1 := by omega
    have hAelem : A (n + (r + 2)) = A (n + 1 + r) + A (n + r) := by
      rw [e1, e2]
      exact hA (n + r)
    have hS1 : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + (r + 2)))
        = A (n + (r + 2)) := IH (r + 2)
    have hSnv : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + r))
        = A (n + r) := IH r
    have hT : (∑ i ∈ Finset.range n,
          (Nat.choose n (i + 1) : R) * (-1 : R) ^ (n - (i + 1)) * A (2 * (i + 1) + r))
        = (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : R) * (-1 : R) ^ (n - i) * A (2 * i + r))
          - (Nat.choose n 0 : R) * (-1 : R) ^ (n - 0) * A (2 * 0 + r) := by
      rw [hSn]
      ring
    have hfinal : (∑ i ∈ Finset.range (n + 1 + 1),
          (Nat.choose (n + 1) i : R) * (-1 : R) ^ (n + 1 - i) * A (2 * i + r))
        = A (n + 1 + r) := by
      linear_combination hLHS + hS1 + hS2 - hT - hSnv + hpow + hAelem
    exact hfinal

/-- For `1 ≤ n`, the alternating row sum of Pascal's triangle vanishes. -/
private theorem alt_choose_sum_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i) = 0 := by
  have h := add_pow (1 : ℤ) (-1 : ℤ) n
  have h01 : (1 : ℤ) + -1 = 0 := by ring
  have hn0 : n ≠ 0 := by omega
  rw [h01, zero_pow hn0] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_pow]
  ring

/-- The shifted sequence `L_{k,n} + k` satisfies the Fibonacci recurrence. -/
private theorem genLeonardo_add_rec (k : ℤ) (n : ℕ) :
    genLeonardo k (n + 2) + k
      = (genLeonardo k (n + 1) + k) + (genLeonardo k n + k) := by
  have hL : genLeonardo k (n + 2) = genLeonardo k (n + 1) + genLeonardo k n + k := rfl
  rw [hL]
  ring

/-- The shifted dual sequence `M_{k,n} + 2 * k` satisfies the Fibonacci recurrence. -/
private theorem genLeonardoCompanion_add_rec (k : ℤ) :
    ∀ n, genLeonardoCompanion k (n + 2) + 2 * k
      = (genLeonardoCompanion k (n + 1) + 2 * k)
        + (genLeonardoCompanion k n + 2 * k) := by
  intro n
  cases n with
  | zero =>
    change genLeonardoCompanion k 2 + 2 * k
      = (genLeonardoCompanion k 1 + 2 * k) + (genLeonardoCompanion k 0 + 2 * k)
    have hM0 : genLeonardoCompanion k 0 = 1 - k := rfl
    have hM1 : genLeonardoCompanion k 1 = genLeonardo k 0 + genLeonardo k 2 := rfl
    have hM2 : genLeonardoCompanion k 2 = genLeonardo k 1 + genLeonardo k 3 := rfl
    have hL0 : genLeonardo k 0 = 1 := rfl
    have hL1 : genLeonardo k 1 = 1 := rfl
    have hL3 : genLeonardo k 3 = genLeonardo k 2 + genLeonardo k 1 + k := rfl
    linear_combination hM2 - hM1 - hM0 + hL3 + 2 * hL1 - hL0
  | succ n =>
    have h2 : genLeonardoCompanion k (n + 1 + 2)
      = genLeonardo k (n + 2) + genLeonardo k (n + 4) := rfl
    have h1 : genLeonardoCompanion k (n + 1 + 1)
      = genLeonardo k (n + 1) + genLeonardo k (n + 3) := rfl
    have h0 : genLeonardoCompanion k (n + 1)
      = genLeonardo k n + genLeonardo k (n + 2) := rfl
    have g2 : genLeonardo k (n + 4)
      = genLeonardo k (n + 3) + genLeonardo k (n + 2) + k := rfl
    have g1 : genLeonardo k (n + 2)
      = genLeonardo k (n + 1) + genLeonardo k n + k := rfl
    linear_combination h2 - h1 - h0 + g2 + g1

@[expose] public section

/-- **Alternating binomial identities for generalized Leonardo numbers.** Let $k$ be an integer,
and let $L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized
Leonardo numbers. For all natural numbers $n \ge 1$ and $r$,
$$\sum_{i=0}^{n} \binom{n}{i} (-1)^{n-i} L_{k,2i+r} = L_{k,n+r} + k$$
and
$$\sum_{i=0}^{n} \binom{n}{i} (-1)^{n-i} M_{k,2i+r} = M_{k,n+r} + 2k.$$

The hypothesis $n \ge 1$ is needed: for $n = 0$ the two sums equal $L_{k,r}$ and $M_{k,r}$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.3 (`fq-2024-kuhapatanakul05292024-thm-3.3`). -/
public theorem genLeonardo_binomial_alternating (k : ℤ) (n r : ℕ)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (-1) ^ (n - i) * genLeonardo k (2 * i + r)
      = genLeonardo k (n + r) + k) ∧
    (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (-1) ^ (n - i) * genLeonardoCompanion k (2 * i + r)
      = genLeonardoCompanion k (n + r) + 2 * k) := by
  have hzero := alt_choose_sum_zero n hn
  constructor
  · have hmain : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i) * (genLeonardo k (2 * i + r) + k))
        = genLeonardo k (n + r) + k :=
      alt_sum_fib_rec (fun m => genLeonardo k m + k) (genLeonardo_add_rec k) n r
    have hterm : ∀ i : ℕ, (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)
          * genLeonardo k (2 * i + r)
        = (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i) * (genLeonardo k (2 * i + r) + k)
          - k * ((Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)) := by
      intro i
      ring
    have hsplit : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i) * genLeonardo k (2 * i + r))
        = (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i) * (genLeonardo k (2 * i + r) + k))
          - k * (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hsplit, hmain, hzero, mul_zero, sub_zero]
  · have hmain : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)
            * (genLeonardoCompanion k (2 * i + r) + 2 * k))
        = genLeonardoCompanion k (n + r) + 2 * k :=
      alt_sum_fib_rec (fun m => genLeonardoCompanion k m + 2 * k)
        (genLeonardoCompanion_add_rec k) n r
    have hterm : ∀ i : ℕ, (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)
          * genLeonardoCompanion k (2 * i + r)
        = (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)
            * (genLeonardoCompanion k (2 * i + r) + 2 * k)
          - (2 * k) * ((Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)) := by
      intro i
      ring
    have hsplit : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i) * genLeonardoCompanion k (2 * i + r))
        = (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)
              * (genLeonardoCompanion k (2 * i + r) + 2 * k))
          - (2 * k) * (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : ℤ) * (-1 : ℤ) ^ (n - i)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hsplit, hmain, hzero, mul_zero, sub_zero]

end

end MetaMathlibExt
