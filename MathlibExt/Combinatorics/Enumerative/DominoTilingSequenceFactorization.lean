/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Basic

@[expose] public section

namespace MetaMathlibExt

/-! # Domino tiling sequence factorization
-/

/-- Odd-index Fibonacci recurrence step: unfolding `Nat.fib_add_two` three times
leaves a goal linear in `Nat.fib (2 * k)` and `Nat.fib (2 * k + 1)`. -/
private theorem domino_fib_odd_step (k : ℕ) :
    Nat.fib (2 * k + 5) + Nat.fib (2 * k + 1) = 3 * Nat.fib (2 * k + 3) := by
  have e1 : Nat.fib (2 * k + 5) = Nat.fib (2 * k + 3) + Nat.fib (2 * k + 4) := by
    have h : 2 * k + 5 = (2 * k + 3) + 2 := by omega
    rw [h, Nat.fib_add_two]
  have e2 : Nat.fib (2 * k + 4) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := by
    have h : 2 * k + 4 = (2 * k + 2) + 2 := by omega
    rw [h, Nat.fib_add_two]
  have e3 : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
    have h : 2 * k + 3 = (2 * k + 1) + 2 := by omega
    rw [h, Nat.fib_add_two]
  have e4 : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := by
    have h : 2 * k + 2 = 2 * k + 2 := by omega
    rw [h, Nat.fib_add_two]
  omega

/-- The odd-index Fibonacci sequence `h n = Nat.fib (2 * n - 1)` satisfies
`h (n + 2) + h n = 3 * h (n + 1)` for `n ≥ 1`. -/
private theorem domino_h_step (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * (n + 2) - 1) + Nat.fib (2 * n - 1)
      = 3 * Nat.fib (2 * (n + 1) - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have i1 : 2 * (1 + k + 2) - 1 = 2 * k + 5 := by omega
  have i2 : 2 * (1 + k) - 1 = 2 * k + 1 := by omega
  have i3 : 2 * (1 + k + 1) - 1 = 2 * k + 3 := by omega
  rw [i1, i2, i3]
  exact domino_fib_odd_step k

/-- Concrete values of `h n = Nat.fib (2 * n - 1)` at `n = 1, 2, 3, 4`. -/
private theorem domino_h1 : Nat.fib (2 * 1 - 1) = 1 := rfl

private theorem domino_h2 : Nat.fib (2 * 2 - 1) = 2 := rfl

private theorem domino_h3 : Nat.fib (2 * 3 - 1) = 5 := rfl

private theorem domino_h4 : Nat.fib (2 * 4 - 1) = 13 := rfl

/-- Product recurrence over `ℤ`: if `a` satisfies the second-order recurrence
with multiplier `5` and `b` the one with multiplier `3` at `n`, `n + 1`,
`n + 2`, then `e = a * b` satisfies
`e (n + 4) + 32 * e (n + 2) + e n = 15 * e (n + 3) + 15 * e (n + 1)`. -/
private theorem domino_product_step (a b : ℕ → ℤ) (n : ℕ)
    (ha0 : a (n + 2) + a n = 5 * a (n + 1))
    (ha1 : a (n + 3) + a (n + 1) = 5 * a (n + 2))
    (ha2 : a (n + 4) + a (n + 2) = 5 * a (n + 3))
    (hb0 : b (n + 2) + b n = 3 * b (n + 1))
    (hb1 : b (n + 3) + b (n + 1) = 3 * b (n + 2))
    (hb2 : b (n + 4) + b (n + 2) = 3 * b (n + 3)) :
    a (n + 4) * b (n + 4) + 32 * (a (n + 2) * b (n + 2)) + a n * b n
      = 15 * (a (n + 3) * b (n + 3)) + 15 * (a (n + 1) * b (n + 1)) := by
  have sa2 : a (n + 2) = 5 * a (n + 1) - a n := by linarith
  have sa3 : a (n + 3) = 24 * a (n + 1) - 5 * a n := by
    linear_combination ha1 + 5 * ha0
  have sa4 : a (n + 4) = 115 * a (n + 1) - 24 * a n := by
    linear_combination ha2 + 5 * ha1 + 24 * ha0
  have sb2 : b (n + 2) = 3 * b (n + 1) - b n := by linarith
  have sb3 : b (n + 3) = 8 * b (n + 1) - 3 * b n := by
    linear_combination hb1 + 3 * hb0
  have sb4 : b (n + 4) = 21 * b (n + 1) - 8 * b n := by
    linear_combination hb2 + 3 * hb1 + 8 * hb0
  rw [sa2, sa3, sa4, sb2, sb3, sb4]
  ring

/-- The product sequence `e m = g m * Nat.fib (2 * m - 1)` satisfies `d`'s
fourth-order recurrence in `ℕ`. The proof moves to `ℤ` and applies
`domino_product_step`. -/
private theorem domino_product_rec (g : ℕ → ℕ)
    (hg : ∀ n, 1 ≤ n → g (n + 2) + g n = 5 * g (n + 1))
    (n : ℕ) (hn : 1 ≤ n) :
    g (n + 4) * Nat.fib (2 * (n + 4) - 1)
        + 32 * (g (n + 2) * Nat.fib (2 * (n + 2) - 1)) + g n * Nat.fib (2 * n - 1)
      = 15 * (g (n + 3) * Nat.fib (2 * (n + 3) - 1))
        + 15 * (g (n + 1) * Nat.fib (2 * (n + 1) - 1)) := by
  have ha0 : ((g (n + 2) : ℕ) : ℤ) + ((g n : ℕ) : ℤ) = 5 * ((g (n + 1) : ℕ) : ℤ) := by
    exact_mod_cast hg n hn
  have ha1 : ((g (n + 3) : ℕ) : ℤ) + ((g (n + 1) : ℕ) : ℤ)
      = 5 * ((g (n + 2) : ℕ) : ℤ) := by
    have h := hg (n + 1) (by omega)
    have e1 : n + 1 + 2 = n + 3 := by omega
    have e2 : n + 1 + 1 = n + 2 := by omega
    rw [e1, e2] at h
    exact_mod_cast h
  have ha2 : ((g (n + 4) : ℕ) : ℤ) + ((g (n + 2) : ℕ) : ℤ)
      = 5 * ((g (n + 3) : ℕ) : ℤ) := by
    have h := hg (n + 2) (by omega)
    have e1 : n + 2 + 2 = n + 4 := by omega
    have e2 : n + 2 + 1 = n + 3 := by omega
    rw [e1, e2] at h
    exact_mod_cast h
  have hb0 : ((Nat.fib (2 * (n + 2) - 1) : ℕ) : ℤ)
        + ((Nat.fib (2 * n - 1) : ℕ) : ℤ)
      = 3 * ((Nat.fib (2 * (n + 1) - 1) : ℕ) : ℤ) := by
    exact_mod_cast domino_h_step n hn
  have hb1 : ((Nat.fib (2 * (n + 3) - 1) : ℕ) : ℤ)
        + ((Nat.fib (2 * (n + 1) - 1) : ℕ) : ℤ)
      = 3 * ((Nat.fib (2 * (n + 2) - 1) : ℕ) : ℤ) := by
    have h := domino_h_step (n + 1) (by omega)
    have e1 : (n + 1) + 2 = n + 3 := by omega
    have e2 : (n + 1) + 1 = n + 2 := by omega
    rw [e1, e2] at h
    exact_mod_cast h
  have hb2 : ((Nat.fib (2 * (n + 4) - 1) : ℕ) : ℤ)
        + ((Nat.fib (2 * (n + 2) - 1) : ℕ) : ℤ)
      = 3 * ((Nat.fib (2 * (n + 3) - 1) : ℕ) : ℤ) := by
    have h := domino_h_step (n + 2) (by omega)
    have e1 : (n + 2) + 2 = n + 4 := by omega
    have e2 : (n + 2) + 1 = n + 3 := by omega
    rw [e1, e2] at h
    exact_mod_cast h
  have key := domino_product_step (fun m => ((g m : ℕ) : ℤ))
    (fun m => ((Nat.fib (2 * m - 1) : ℕ) : ℤ)) n ha0 ha1 ha2 hb0 hb1 hb2
  exact_mod_cast key

/-- Uniqueness: two sequences satisfying the fourth-order recurrence for every
`n ≥ 1` and agreeing at `1, 2, 3, 4` agree at every `n ≥ 1`. -/
private theorem domino_unique (d e : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ n → d (n + 4) + 32 * d (n + 2) + d n = 15 * d (n + 3) + 15 * d (n + 1))
    (he : ∀ n, 1 ≤ n → e (n + 4) + 32 * e (n + 2) + e n = 15 * e (n + 3) + 15 * e (n + 1))
    (h1 : d 1 = e 1) (h2 : d 2 = e 2) (h3 : d 3 = e 3) (h4 : d 4 = e 4) :
    ∀ n, 1 ≤ n → d n = e n := by
  have step : ∀ k, d (k + 1) = e (k + 1) ∧ d (k + 2) = e (k + 2)
      ∧ d (k + 3) = e (k + 3) ∧ d (k + 4) = e (k + 4) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using h1
      · simpa using h2
      · simpa using h3
      · simpa using h4
    | succ k ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih
      have hd' := hd (k + 1) (by omega)
      have he' := he (k + 1) (by omega)
      have e5 : k + 1 + 4 = k + 5 := by omega
      have e4 : k + 1 + 3 = k + 4 := by omega
      have e3 : k + 1 + 2 = k + 3 := by omega
      have e2 : k + 1 + 1 = k + 2 := by omega
      rw [e5, e4, e3, e2] at hd' he'
      have h5 : d (k + 5) = e (k + 5) := by omega
      have f1 : k + 1 + 1 = k + 2 := by omega
      have f2 : k + 1 + 2 = k + 3 := by omega
      have f3 : k + 1 + 3 = k + 4 := by omega
      have f4 : k + 1 + 4 = k + 5 := by omega
      rw [f1, f2, f3, f4]
      exact ⟨i2, i3, i4, h5⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact (step k).1

/--
**Factorization of the domino tiling sequence.** Let $d$ and $g$ be sequences of natural
numbers with $d_1 = 1$, $d_2 = 8$, $d_3 = 95$, $d_4 = 1183$ and
$d_{n+4} + 32 d_{n+2} + d_n = 15 d_{n+3} + 15 d_{n+1}$ for all $n \ge 1$, and with $g_1 = 1$,
$g_2 = 4$ and $g_{n+2} + g_n = 5 g_{n+1}$ for all $n \ge 1$. Then $d_n = g_n F_{2n-1}$ for every
$n \ge 1$, where $F_m$ is the $m$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).

These recurrences determine $d_n$ and $g_n$ for $n \ge 1$: $d_n$ is the number of domino tilings
of $P_5 \times P_{2n-2}$ (OEIS A003775) and $g_n$ is OEIS A004253.

Source: James A. Sellers, "Domino Tilings and Products of Fibonacci
and Pell Numbers," Journal of Integer Sequences 5 (2002),
Article 02.1.2, second Theorem (`d_n = g_n h_n`), lines 153–154,
with `d` defined at lines 146–150 and `g` at line 164,
https://cs.uwaterloo.ca/journals/JIS/VOL5/Sellers/sellers4.tex
-/
public theorem domino_tiling_sequence_factorization :
    ∀ (d g : Nat → Nat), d 1 = 1 → d 2 = 8 → d 3 = 95 → d 4 = 1183 →
    (∀ n, 1 ≤ n → d (n + 4) + 32 * d (n + 2) + d n = 15 * d (n + 3) + 15 * d (n + 1)) →
    g 1 = 1 → g 2 = 4 →
    (∀ n, 1 ≤ n → g (n + 2) + g n = 5 * g (n + 1)) →
    ∀ n, 1 ≤ n → d n = g n * Nat.fib (2 * n - 1) := by
  intro d g hd1 hd2 hd3 hd4 hdrec hg1 hg2 hgrec n hn
  have hg3 : g 3 = 19 := by
    have h := hgrec 1 (by omega)
    have e1 : 1 + 2 = 3 := by omega
    have e2 : 1 + 1 = 2 := by omega
    rw [e1, e2, hg1, hg2] at h
    omega
  have hg4 : g 4 = 91 := by
    have h := hgrec 2 (by omega)
    have e1 : 2 + 2 = 4 := by omega
    have e2 : 2 + 1 = 3 := by omega
    rw [e1, e2, hg2, hg3] at h
    omega
  refine domino_unique d (fun m => g m * Nat.fib (2 * m - 1)) hdrec ?he ?h1 ?h2 ?h3 ?h4 n hn
  · intro m hm
    exact domino_product_rec g hgrec m hm
  · show d 1 = g 1 * Nat.fib (2 * 1 - 1)
    rw [hd1, hg1, domino_h1]
  · show d 2 = g 2 * Nat.fib (2 * 2 - 1)
    rw [hd2, hg2, domino_h2]
  · show d 3 = g 3 * Nat.fib (2 * 3 - 1)
    rw [hd3, hg3, domino_h3]
  · show d 4 = g 4 * Nat.fib (2 * 4 - 1)
    rw [hd4, hg4, domino_h4]

end MetaMathlibExt
