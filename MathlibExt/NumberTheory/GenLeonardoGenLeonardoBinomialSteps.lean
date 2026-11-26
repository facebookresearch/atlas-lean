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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Binomial identities with steps three and four for generalized Leonardo numbers

For an integer `k`, with `L_{k,n} = genLeonardo k n` and `M_{k,n} = genLeonardoCompanion k n`,
for all natural numbers `n` and `r`, `∑_{i=0}^n C(n,i) L_{k,3i+r} = 2^n L_{k,2n+r}`,
`∑_{i=0}^n C(n,i) M_{k,3i+r} = 2^n M_{k,2n+r}`,
`∑_{i=0}^n C(n,i) L_{k,4i+r} = 3^n L_{k,2n+r} + k (3^n - 2^n)`, and
`∑_{i=0}^n C(n,i) M_{k,4i+r} = 3^n M_{k,2n+r} + 2k (3^n - 2^n)`.

This module proves `genLeonardo_binomial_steps`. The proof writes both sequences in terms of
Fibonacci numbers (`L_{k,n} + k = (1 + k) F_{n+1}`) and proves the resulting Fibonacci binomial
identities by induction on `n`.

## References

* Kantaphon Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, The Fibonacci Quarterly 62
  (2024), no. 3, 201–207, Theorem 3.4.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A binomial sum at `n + 1` splits into the sum at `n` and the shifted sum at `n`. -/
private lemma binomial_split (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), (Nat.choose (n + 1) i : ℤ) * f i
      = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * f i
        + ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * f (i + 1) := by
  have hLHS : ∑ i ∈ Finset.range (n + 2), (Nat.choose (n + 1) i : ℤ) * f i
      = ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℤ) * f (k + 1)
        + (Nat.choose (n + 1) 0 : ℤ) * f 0 := by
    have h := Finset.sum_range_succ' (fun k => (Nat.choose (n + 1) k : ℤ) * f k) (n + 1)
    simpa [show n + 1 + 1 = n + 2 by omega] using h
  rw [hLHS]
  have hsplit : ∀ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 1) (k + 1) : ℤ) * f (k + 1)
        = (Nat.choose n k : ℤ) * f (k + 1) + (Nat.choose n (k + 1) : ℤ) * f (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  rw [Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hRHS1 : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * f i
      = ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℤ) * f (k + 1) + f 0 := by
    have h := Finset.sum_range_succ' (fun k => (Nat.choose n k : ℤ) * f k) n
    rw [h, Nat.choose_zero_right, Nat.cast_one, one_mul]
  have htail : ∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * f (k + 1)
      = ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℤ) * f (k + 1) := by
    rw [Finset.sum_range_succ]
    have hz : (Nat.choose n (n + 1) : ℤ) * f (n + 1) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega : n < n + 1), Nat.cast_zero, zero_mul]
    rw [hz, add_zero]
  rw [htail, hRHS1]
  ring

/-- Fibonacci three-step relation `F_m + F_{m+3} = 2 F_{m+2}`, over `ℤ`. -/
private lemma fib_three_add (m : ℕ) :
    (Nat.fib m : ℤ) + Nat.fib (m + 3) = 2 * Nat.fib (m + 2) := by
  have h1 : (Nat.fib (m + 3) : ℤ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    have h : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      rw [show m + 3 = (m + 1) + 2 by omega, Nat.fib_add_two]
    exact_mod_cast h
  have h2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_add_two
  linear_combination h1 - h2

/-- Fibonacci four-step relation `F_m + F_{m+4} = 3 F_{m+2}`, over `ℤ`. -/
private lemma fib_four_add (m : ℕ) :
    (Nat.fib m : ℤ) + Nat.fib (m + 4) = 3 * Nat.fib (m + 2) := by
  have h1 : (Nat.fib (m + 4) : ℤ) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    have h : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
      rw [show m + 4 = (m + 2) + 2 by omega, Nat.fib_add_two]
    exact_mod_cast h
  have h2 : (Nat.fib (m + 3) : ℤ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    have h : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      rw [show m + 3 = (m + 1) + 2 by omega, Nat.fib_add_two]
    exact_mod_cast h
  have h3 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_add_two
  linear_combination h1 + h2 - h3

/-- Fibonacci binomial identity with step three: `∑_i C(n,i) F_{3i+r} = 2^n F_{2n+r}`. -/
private lemma fib_binom_three (n : ℕ) : ∀ r : ℕ,
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + r) : ℤ)
      = 2 ^ n * (Nat.fib (2 * n + r) : ℤ) := by
  induction n with
  | zero =>
    intro r
    simp
  | succ n ih =>
    intro r
    have hsplit := binomial_split (fun i => (Nat.fib (3 * i + r) : ℤ)) n
    rw [show n + 1 + 1 = n + 2 by omega] at *
    have hshift : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * (i + 1) + r) : ℤ)
        = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + (r + 3)) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      congr 1
      omega
    rw [hsplit, hshift]
    rw [ih r, ih (r + 3)]
    have hfib := fib_three_add (2 * n + r)
    have e1 : 2 * n + r + 3 = 2 * n + (r + 3) := by omega
    have e2 : 2 * (n + 1) + r = (2 * n + r) + 2 := by omega
    rw [e1] at hfib
    rw [e2]
    rw [pow_succ]
    linear_combination (2 ^ n) * hfib

/-- Fibonacci binomial identity with step four: `∑_i C(n,i) F_{4i+r} = 3^n F_{2n+r}`. -/
private lemma fib_binom_four (n : ℕ) : ∀ r : ℕ,
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + r) : ℤ)
      = 3 ^ n * (Nat.fib (2 * n + r) : ℤ) := by
  induction n with
  | zero =>
    intro r
    simp
  | succ n ih =>
    intro r
    have hsplit := binomial_split (fun i => (Nat.fib (4 * i + r) : ℤ)) n
    rw [show n + 1 + 1 = n + 2 by omega] at *
    have hshift : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * (i + 1) + r) : ℤ)
        = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + (r + 4)) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      congr 1
      omega
    rw [hsplit, hshift]
    rw [ih r, ih (r + 4)]
    have hfib := fib_four_add (2 * n + r)
    have e1 : 2 * n + r + 4 = 2 * n + (r + 4) := by omega
    have e2 : 2 * (n + 1) + r = (2 * n + r) + 2 := by omega
    rw [e1] at hfib
    rw [e2]
    rw [pow_succ]
    linear_combination (3 ^ n) * hfib

/-- The generalized Leonardo numbers shifted by `k` are `1 + k` times the Fibonacci numbers:
`L_{k,n} + k = (1 + k) F_{n+1}`. -/
private theorem genLeonardo_add_eq_mul_fib (k : ℤ) :
    ∀ n : ℕ, genLeonardo k n + k = (1 + k) * Nat.fib (n + 1)
  | 0 => by simp [genLeonardo]
  | 1 => by simp [genLeonardo, Nat.fib_two]
  | n + 2 => by
    have h0 := genLeonardo_add_eq_mul_fib k n
    have h1 := genLeonardo_add_eq_mul_fib k (n + 1)
    have hF : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      exact_mod_cast Nat.fib_add_two
    rw [genLeonardo, hF]
    linear_combination h0 + h1

/-- Each `L_{k,i}` is `(1 + k) F_{i+1} - k`. -/
private lemma genLeonardo_eq (k : ℤ) (i : ℕ) :
    genLeonardo k i = (1 + k) * Nat.fib (i + 1) - k :=
  eq_sub_of_add_eq (genLeonardo_add_eq_mul_fib k i)

/-- The sum of the binomial coefficients over `ℤ` is `2 ^ n`. -/
private lemma sum_choose_eq (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) = (2 ^ n : ℤ) := by
  have h : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ)
      = ((∑ i ∈ Finset.range (n + 1), Nat.choose n i : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
  rw [h, Nat.sum_range_choose]
  simp

/-- The dual numbers shifted by `2k` are `1 + k` times a Fibonacci sum:
`M_{k,n} + 2k = (1 + k) (F_n + F_{n+2})`. -/
private lemma companion_add (k : ℤ) : ∀ n : ℕ,
    genLeonardoCompanion k n + 2 * k
      = (1 + k) * ((Nat.fib n : ℤ) + Nat.fib (n + 2))
  | 0 => by
    have h0 : genLeonardoCompanion k 0 = 1 - k := rfl
    have e : (0 + 2 : ℕ) = 2 := by omega
    rw [h0, e, Nat.fib_zero, Nat.fib_two, Nat.cast_zero, Nat.cast_one, zero_add, mul_one]
    ring
  | n + 1 => by
    have h0 := genLeonardo_eq k n
    have h1 := genLeonardo_eq k (n + 2)
    have e : n + 2 + 1 = n + 1 + 2 := by omega
    change genLeonardo k n + genLeonardo k (n + 2) + 2 * k = _
    rw [h0, h1, e]
    ring

/-- Each `M_{k,j}` is `(1 + k) (F_j + F_{j+2}) - 2k`. -/
private lemma companion_eq (k : ℤ) (j : ℕ) :
    genLeonardoCompanion k j
      = (1 + k) * ((Nat.fib j : ℤ) + Nat.fib (j + 2)) - 2 * k :=
  eq_sub_of_add_eq (companion_add k j)

/-- Step-three binomial identity for `L`: `∑_i C(n,i) L_{k,3i+r} = 2^n L_{k,2n+r}`. -/
private lemma leo_three (k : ℤ) (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (3 * i + r)
      = 2 ^ n * genLeonardo k (2 * n + r) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℤ) * genLeonardo k (3 * i + r)
        = (1 + k) * ((Nat.choose n i : ℤ) * (Nat.fib (3 * i + r + 1) : ℤ))
          - k * (Nat.choose n i : ℤ) := by
    intro i _
    rw [genLeonardo_eq]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_choose_eq, genLeonardo_eq]
  have hF : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + r + 1) : ℤ)
      = 2 ^ n * (Nat.fib (2 * n + r + 1) : ℤ) := by
    have h0 := fib_binom_three n (r + 1)
    have eL : ∀ i ∈ Finset.range (n + 1),
        (Nat.fib (3 * i + r + 1) : ℤ) = (Nat.fib (3 * i + (r + 1)) : ℤ) := by
      intro i _
      rw [show 3 * i + r + 1 = 3 * i + (r + 1) by omega]
    have eR : (Nat.fib (2 * n + r + 1) : ℤ) = (Nat.fib (2 * n + (r + 1)) : ℤ) := by
      rw [show 2 * n + r + 1 = 2 * n + (r + 1) by omega]
    have hsum : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + r + 1) : ℤ)
        = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + (r + 1)) : ℤ) :=
      Finset.sum_congr rfl (fun i hi => by rw [eL i hi])
    rw [hsum, h0, eR]
  linear_combination (1 + k) * hF

/-- Step-four binomial identity for `L`:
`∑_i C(n,i) L_{k,4i+r} = 3^n L_{k,2n+r} + k (3^n - 2^n)`. -/
private lemma leo_four (k : ℤ) (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (4 * i + r)
      = 3 ^ n * genLeonardo k (2 * n + r) + k * (3 ^ n - 2 ^ n) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℤ) * genLeonardo k (4 * i + r)
        = (1 + k) * ((Nat.choose n i : ℤ) * (Nat.fib (4 * i + r + 1) : ℤ))
          - k * (Nat.choose n i : ℤ) := by
    intro i _
    rw [genLeonardo_eq]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_choose_eq, genLeonardo_eq]
  have hF : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + r + 1) : ℤ)
      = 3 ^ n * (Nat.fib (2 * n + r + 1) : ℤ) := by
    have h0 := fib_binom_four n (r + 1)
    have eL : ∀ i ∈ Finset.range (n + 1),
        (Nat.fib (4 * i + r + 1) : ℤ) = (Nat.fib (4 * i + (r + 1)) : ℤ) := by
      intro i _
      rw [show 4 * i + r + 1 = 4 * i + (r + 1) by omega]
    have eR : (Nat.fib (2 * n + r + 1) : ℤ) = (Nat.fib (2 * n + (r + 1)) : ℤ) := by
      rw [show 2 * n + r + 1 = 2 * n + (r + 1) by omega]
    have hsum : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + r + 1) : ℤ)
        = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + (r + 1)) : ℤ) :=
      Finset.sum_congr rfl (fun i hi => by rw [eL i hi])
    rw [hsum, h0, eR]
  linear_combination (1 + k) * hF

/-- Step-three binomial identity for `M`: `∑_i C(n,i) M_{k,3i+r} = 2^n M_{k,2n+r}`. -/
private lemma comp_three (k : ℤ) (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (3 * i + r)
      = 2 ^ n * genLeonardoCompanion k (2 * n + r) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℤ) * genLeonardoCompanion k (3 * i + r)
        = (1 + k) * ((Nat.choose n i : ℤ) * (Nat.fib (3 * i + r) : ℤ))
          + (1 + k) * ((Nat.choose n i : ℤ) * (Nat.fib (3 * i + r + 2) : ℤ))
          - 2 * k * (Nat.choose n i : ℤ) := by
    intro i _
    rw [companion_eq]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_choose_eq, companion_eq]
  have hF1 : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + r) : ℤ)
      = 2 ^ n * (Nat.fib (2 * n + r) : ℤ) :=
    fib_binom_three n r
  have hF2 : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + r + 2) : ℤ)
      = 2 ^ n * (Nat.fib (2 * n + r + 2) : ℤ) := by
    have h0 := fib_binom_three n (r + 2)
    have eL : ∀ i ∈ Finset.range (n + 1),
        (Nat.fib (3 * i + r + 2) : ℤ) = (Nat.fib (3 * i + (r + 2)) : ℤ) := by
      intro i _
      rw [show 3 * i + r + 2 = 3 * i + (r + 2) by omega]
    have eR : (Nat.fib (2 * n + r + 2) : ℤ) = (Nat.fib (2 * n + (r + 2)) : ℤ) := by
      rw [show 2 * n + r + 2 = 2 * n + (r + 2) by omega]
    have hsum : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + r + 2) : ℤ)
        = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (3 * i + (r + 2)) : ℤ) :=
      Finset.sum_congr rfl (fun i hi => by rw [eL i hi])
    rw [hsum, h0, eR]
  linear_combination (1 + k) * hF1 + (1 + k) * hF2

/-- Step-four binomial identity for `M`:
`∑_i C(n,i) M_{k,4i+r} = 3^n M_{k,2n+r} + 2k (3^n - 2^n)`. -/
private lemma comp_four (k : ℤ) (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (4 * i + r)
      = 3 ^ n * genLeonardoCompanion k (2 * n + r) + 2 * k * (3 ^ n - 2 ^ n) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℤ) * genLeonardoCompanion k (4 * i + r)
        = (1 + k) * ((Nat.choose n i : ℤ) * (Nat.fib (4 * i + r) : ℤ))
          + (1 + k) * ((Nat.choose n i : ℤ) * (Nat.fib (4 * i + r + 2) : ℤ))
          - 2 * k * (Nat.choose n i : ℤ) := by
    intro i _
    rw [companion_eq]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_choose_eq, companion_eq]
  have hF1 : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + r) : ℤ)
      = 3 ^ n * (Nat.fib (2 * n + r) : ℤ) :=
    fib_binom_four n r
  have hF2 : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + r + 2) : ℤ)
      = 3 ^ n * (Nat.fib (2 * n + r + 2) : ℤ) := by
    have h0 := fib_binom_four n (r + 2)
    have eL : ∀ i ∈ Finset.range (n + 1),
        (Nat.fib (4 * i + r + 2) : ℤ) = (Nat.fib (4 * i + (r + 2)) : ℤ) := by
      intro i _
      rw [show 4 * i + r + 2 = 4 * i + (r + 2) by omega]
    have eR : (Nat.fib (2 * n + r + 2) : ℤ) = (Nat.fib (2 * n + (r + 2)) : ℤ) := by
      rw [show 2 * n + r + 2 = 2 * n + (r + 2) by omega]
    have hsum : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + r + 2) : ℤ)
        = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * (Nat.fib (4 * i + (r + 2)) : ℤ) :=
      Finset.sum_congr rfl (fun i hi => by rw [eL i hi])
    rw [hsum, h0, eR]
  linear_combination (1 + k) * hF1 + (1 + k) * hF2

/-- **Binomial identities with steps three and four for generalized Leonardo numbers.** Let $k$ be
an integer, and let $L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual
generalized Leonardo numbers. For all natural numbers $n$ and $r$,
$$\sum_{i=0}^{n} \binom{n}{i} L_{k,3i+r} = 2^n L_{k,2n+r},$$
$$\sum_{i=0}^{n} \binom{n}{i} M_{k,3i+r} = 2^n M_{k,2n+r},$$
$$\sum_{i=0}^{n} \binom{n}{i} L_{k,4i+r} = 3^n L_{k,2n+r} + k\,(3^n - 2^n),$$
and
$$\sum_{i=0}^{n} \binom{n}{i} M_{k,4i+r} = 3^n M_{k,2n+r} + 2k\,(3^n - 2^n).$$

Part (iv) of the paper's Theorem 3.4 prints the last term of the fourth identity as
$k\,(3^n - 2^n)$, which is false at $k = n = 1$, $r = 0$; the coefficient $2k$ is the correct one,
as in parts (ii) of Theorems 3.1–3.3.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.4 (`fq-2024-kuhapatanakul05292024-thm-3.4`). -/
public theorem genLeonardo_binomial_steps (k : ℤ) (n r : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (3 * i + r)
      = 2 ^ n * genLeonardo k (2 * n + r)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (3 * i + r)
      = 2 ^ n * genLeonardoCompanion k (2 * n + r)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (4 * i + r)
      = 3 ^ n * genLeonardo k (2 * n + r) + k * (3 ^ n - 2 ^ n)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (4 * i + r)
      = 3 ^ n * genLeonardoCompanion k (2 * n + r) + 2 * k * (3 ^ n - 2 ^ n))
    := by
  exact ⟨leo_three k n r, comp_three k n r, leo_four k n r, comp_four k n r⟩

end

end MetaMathlibExt
