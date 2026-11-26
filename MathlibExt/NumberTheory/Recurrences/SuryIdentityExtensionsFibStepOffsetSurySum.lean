/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensions
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution

/-!
# Offset step extension of Sury's identity, Fibonacci form

This module proves the Fibonacci form of the offset step extension of Sury's identity
(`fib_step_offset_sury_sum`): for natural numbers `j` and `n` and integers `k` with
`0 < |k| < j`, the `j`-step Fibonacci number `F_{j(n+1)}` equals `F_j / F_k` times a
weighted sum of the offset terms `F_{ji+k}`.

The proof applies the initial-one form of Sury's identity
(`second_order_recurrence_initial_one_sury_sum`) to the normalized `j`-step sequence
`A m = F_{jm+k} / F_k`. The recurrence for `A` is the `j`-step Fibonacci recurrence,
the summation ratio is identified through the same recurrence at offset `k`, and the
two sides are matched with a Catalan-type identity for Fibonacci numbers at integer
indices.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity",
*Journal of Integer Sequences* 29 (2026), Article 26.3.2, Theorem 5
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dresden/dresden34.html>).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

/-- The zeroth Fibonacci number, over `ℚ`. -/
private theorem fib_zero_q : fibAtInt 0 = 0 := by
  simp only [fibAtInt]
  exact_mod_cast Int.fib_zero

/-- The first Fibonacci number, over `ℚ`. -/
private theorem fib_one_q : fibAtInt 1 = 1 := by
  simp only [fibAtInt]
  exact_mod_cast Int.fib_one

/-- Fibonacci recurrence at integer indices, over `ℚ`. -/
private theorem fib_add_two_q (n : ℤ) :
    fibAtInt (n + 2) = fibAtInt n + fibAtInt (n + 1) := by
  simp only [fibAtInt]
  exact_mod_cast Int.fib_add_two n

/-- Fibonacci addition formula at integer indices, over `ℚ`. -/
private theorem fib_add_q (m n : ℤ) :
    fibAtInt (m + n) =
      fibAtInt (m - 1) * fibAtInt n + fibAtInt m * fibAtInt (n + 1) := by
  simp only [fibAtInt]
  exact_mod_cast Int.fib_add m n

/-- Fibonacci negation formula at integer indices, over `ℚ`. -/
private theorem fib_neg_q (n : ℤ) :
    fibAtInt (-n) = (-1 : ℚ) ^ (n + 1) * fibAtInt n := by
  simp only [fibAtInt]
  exact Int.coe_fib_neg n

/-- Fibonacci numbers vanish only at index zero, over `ℚ`. -/
private theorem fib_ne_zero_q {n : ℤ} (hn : n ≠ 0) : fibAtInt n ≠ 0 := by
  simp only [fibAtInt, ne_eq]
  intro h
  have h2 : Int.fib n = 0 := by exact_mod_cast h
  exact hn (Int.fib_eq_zero.mp h2)

/-- Lucas numbers at natural indices, as rationals. -/
private theorem lucasAtInt_natCast (j : ℕ) :
    lucasAtInt (j : ℤ) = (MetaMathlibExt.lucasNumber j : ℚ) := by
  simp [lucasAtInt]

/-- Catalan-type identity for Fibonacci numbers at integer indices: for all integers `a`,
`b` and `c`, `F_{a+c} F_{b-c} - F_a F_b = (-1)^{b+c+1} F_{a+c-b} F_c`. Both sides
satisfy the Fibonacci recurrence in `a`, so it suffices to check `a = 0` and `a = 1`,
where the addition and negation formulas apply. -/
private theorem fib_catalan (a b c : ℤ) :
    fibAtInt (a + c) * fibAtInt (b - c) - fibAtInt a * fibAtInt b =
      (-1 : ℚ) ^ (b + c + 1) * fibAtInt (a + c - b) * fibAtInt c := by
  set P : ℤ → Prop := fun x =>
    fibAtInt (x + c) * fibAtInt (b - c) - fibAtInt x * fibAtInt b =
      (-1 : ℚ) ^ (b + c + 1) * fibAtInt (x + c - b) * fibAtInt c with hP
  have h0 : P 0 := by
    simp only [hP]
    have hneg : fibAtInt (c - b) = (-1 : ℚ) ^ (b - c + 1) * fibAtInt (b - c) := by
      have h := fib_neg_q (b - c)
      rwa [show -((b : ℤ) - c) = c - b by ring] at h
    have hpow : (-1 : ℚ) ^ (b + c + 1) * (-1 : ℚ) ^ (b - c + 1) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      rw [show (b + c + 1) + (b - c + 1) = 2 * (b + 1) by ring]
      exact Even.neg_one_zpow ⟨b + 1, by ring⟩
    rw [show (0 : ℤ) + c = c by ring, fib_zero_q, hneg]
    linear_combination (-(fibAtInt c * fibAtInt (b - c))) * hpow
  have h1 : P 1 := by
    simp only [hP]
    have hadd : fibAtInt b = fibAtInt (b - c - 1) * fibAtInt c +
        fibAtInt (b - c) * fibAtInt (c + 1) := by
      have h := fib_add_q (b - c) c
      rwa [show (b : ℤ) - c + c = b by ring] at h
    have hneg : fibAtInt (1 + c - b) = (-1 : ℚ) ^ (b - c) * fibAtInt (b - c - 1) := by
      have h := fib_neg_q (b - c - 1)
      rw [show -((b : ℤ) - c - 1) = 1 + c - b by ring,
        show (b : ℤ) - c - 1 + 1 = b - c by ring] at h
      exact h
    have hpow : (-1 : ℚ) ^ (b + c + 1) * (-1 : ℚ) ^ (b - c) = -1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      rw [show (b + c + 1) + (b - c) = 2 * b + 1 by ring]
      rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
        Even.neg_one_zpow (⟨b, by ring⟩ : Even (2 * b))]
      simp
    rw [hneg, show (1 : ℤ) + c = c + 1 by ring, fib_one_q]
    linear_combination -hadd - (fibAtInt (b - c - 1) * fibAtInt c) * hpow
  have fwd : ∀ x : ℤ, P x → P (x + 1) → P (x + 2) := by
    intro x hx hx1
    simp only [hP] at hx hx1 ⊢
    have r1 := fib_add_two_q (x + c)
    have r2 := fib_add_two_q x
    have r3 := fib_add_two_q (x + c - b)
    rw [show x + 1 + c - b = (x + c - b) + 1 by ring,
      show x + 1 + c = (x + c) + 1 by ring] at hx1
    rw [show x + 2 + c - b = (x + c - b) + 2 by ring,
      show x + 2 + c = (x + c) + 2 by ring]
    linear_combination hx + hx1 + fibAtInt (b - c) * r1 - fibAtInt b * r2 -
      ((-1 : ℚ) ^ (b + c + 1) * fibAtInt c) * r3
  have bwd : ∀ x : ℤ, P (x + 1) → P (x + 2) → P x := by
    intro x hx1 hx2
    simp only [hP] at hx1 hx2 ⊢
    have r1 := fib_add_two_q (x + c)
    have r2 := fib_add_two_q x
    have r3 := fib_add_two_q (x + c - b)
    rw [show x + 1 + c - b = (x + c - b) + 1 by ring,
      show x + 1 + c = (x + c) + 1 by ring] at hx1
    rw [show x + 2 + c - b = (x + c - b) + 2 by ring,
      show x + 2 + c = (x + c) + 2 by ring] at hx2
    linear_combination hx2 - hx1 - fibAtInt (b - c) * r1 + fibAtInt b * r2 +
      ((-1 : ℚ) ^ (b + c + 1) * fibAtInt c) * r3
  have hnonneg : ∀ n : ℕ, P (n : ℤ) ∧ P ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero =>
      have e0 : ((0 : ℕ) : ℤ) = 0 := by simp
      rw [e0]
      refine ⟨h0, ?_⟩
      have e1 : (0 : ℤ) + 1 = 1 := by ring
      rw [e1]
      exact h1
    | succ n ih =>
      have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by simp
      rw [e1]
      refine ⟨ih.2, ?_⟩
      have e2 : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
      rw [e2]
      exact fwd _ ih.1 ih.2
  have hneg : ∀ n : ℕ, P (-(n : ℤ)) ∧ P (-(n : ℤ) + 1) := by
    intro n
    induction n with
    | zero =>
      have e0 : (-((0 : ℕ) : ℤ)) = 0 := by simp
      rw [e0]
      refine ⟨h0, ?_⟩
      have e1 : (0 : ℤ) + 1 = 1 := by ring
      rw [e1]
      exact h1
    | succ n ih =>
      have e1 : (-((n + 1 : ℕ) : ℤ)) = -(n : ℤ) - 1 := by push_cast; ring
      rw [e1]
      have e2 : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by ring
      rw [e2]
      refine ⟨?_, ih.1⟩
      have g1 : P (-(n : ℤ) - 1 + 1) := by
        rw [e2]
        exact ih.1
      have g2 : P (-(n : ℤ) - 1 + 2) := by
        have e4 : -(n : ℤ) - 1 + 2 = -(n : ℤ) + 1 := by ring
        rw [e4]
        exact ih.2
      exact bwd _ g1 g2
  change P a
  rcases lt_or_ge a 0 with ha | ha
  · have hneg' : 0 ≤ -a := by omega
    have ea : a = -(((-a).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hneg']
      simp
    rw [ea]
    exact (hneg ((-a).toNat)).1
  · have ea : a = ((a.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg ha).symm
    rw [ea]
    exact (hnonneg a.toNat).1

/-- The `j`-step Fibonacci recurrence: for every natural number `j` and integer `u`,
`F_{u+j} = L_j F_u + (-1)^{j+1} F_{u-j}`. Both sides satisfy the Fibonacci recurrence
in `j`. -/
private theorem fib_step_recurrence (j : ℕ) (u : ℤ) :
    fibAtInt (u + (j : ℤ)) =
      lucasAtInt (j : ℤ) * fibAtInt u +
        (-1 : ℚ) ^ (j + 1) * fibAtInt (u - (j : ℤ)) := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have hL0 : lucasAtInt ((0 : ℕ) : ℤ) = 2 := by
      rw [lucasAtInt_natCast, MetaMathlibExt.cb_lucas_zero]
      norm_num
    have hpow : (-1 : ℚ) ^ (0 + 1) = -1 := by norm_num
    rw [hL0, hpow]
    simp only [Nat.cast_zero, add_zero, sub_zero]
    ring
  | one =>
    have hL1 : lucasAtInt ((1 : ℕ) : ℤ) = 1 := by
      rw [lucasAtInt_natCast, MetaMathlibExt.cb_lucas_one]
      norm_num
    have hpow : (-1 : ℚ) ^ (1 + 1) = 1 := by norm_num
    have hrec : fibAtInt (u + 1) = fibAtInt (u - 1) + fibAtInt u := by
      have h := fib_add_two_q (u - 1)
      rwa [show (u : ℤ) - 1 + 2 = u + 1 by ring,
        show (u : ℤ) - 1 + 1 = u by ring] at h
    rw [hL1, hpow, show (u : ℤ) + ((1 : ℕ) : ℤ) = u + 1 by simp,
      show (u : ℤ) - ((1 : ℕ) : ℤ) = u - 1 by simp]
    linear_combination hrec
  | more j ih0 ih1 =>
    have hL : lucasAtInt (((j + 2 : ℕ)) : ℤ) =
        lucasAtInt (((j + 1 : ℕ)) : ℤ) + lucasAtInt (j : ℤ) := by
      rw [lucasAtInt_natCast, lucasAtInt_natCast, lucasAtInt_natCast,
        MetaMathlibExt.cb_lucas_add_two]
      exact Nat.cast_add _ _
    have he : (-1 : ℚ) ^ (j + 2 + 1) = (-1 : ℚ) ^ (j + 1) := by
      rw [show j + 2 + 1 = (j + 1) + 2 by ring, pow_add,
        show (-1 : ℚ) ^ (2 : ℕ) = 1 by norm_num, mul_one]
    have he1 : (-1 : ℚ) ^ (j + 1 + 1) = -(-1 : ℚ) ^ (j + 1) := by
      rw [pow_succ]
      ring
    have rfib1 : fibAtInt (u + ((j + 2 : ℕ) : ℤ)) =
        fibAtInt (u + (j : ℤ)) + fibAtInt (u + ((j + 1 : ℕ) : ℤ)) := by
      have h := fib_add_two_q (u + (j : ℤ))
      rwa [show (u : ℤ) + (j : ℤ) + 2 = u + ((j + 2 : ℕ) : ℤ) by push_cast; ring,
        show (u : ℤ) + (j : ℤ) + 1 = u + ((j + 1 : ℕ) : ℤ) by push_cast; ring] at h
    have rfib2 : fibAtInt (u - (j : ℤ)) = fibAtInt (u - ((j + 2 : ℕ) : ℤ)) +
        fibAtInt (u - ((j + 1 : ℕ) : ℤ)) := by
      have h := fib_add_two_q (u - (j : ℤ) - 2)
      rw [show (u : ℤ) - (j : ℤ) - 2 + 1 = u - ((j + 1 : ℕ) : ℤ) by push_cast; ring,
        show (u : ℤ) - (j : ℤ) - 2 + 2 = u - (j : ℤ) by ring,
        show (u : ℤ) - (j : ℤ) - 2 = u - ((j + 2 : ℕ) : ℤ) by push_cast; ring] at h
      exact h
    linear_combination ih0 + ih1 + rfib1 - fibAtInt u * hL +
      (-1 : ℚ) ^ (j + 1) * rfib2 - fibAtInt (u - ((j + 2 : ℕ) : ℤ)) * he +
      fibAtInt (u - ((j + 1 : ℕ) : ℤ)) * he1

/-- The `j`-step ratio: `L_j F_k - F_{j+k} = (-1)^{k+1} F_{j-k}`. This is the `j`-step
recurrence at offset `k`, rewritten with the negation formula. -/
private theorem step_ratio (j : ℕ) (k : ℤ) :
    lucasAtInt (j : ℤ) * fibAtInt k - fibAtInt ((j : ℤ) + k) =
      (-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) := by
  have hG := fib_step_recurrence j k
  have hneg : fibAtInt (k - (j : ℤ)) =
      (-1 : ℚ) ^ ((j : ℤ) - k + 1) * fibAtInt ((j : ℤ) - k) := by
    have h := fib_neg_q ((j : ℤ) - k)
    rwa [show -((j : ℤ) - k) = k - (j : ℤ) by ring] at h
  have hsign : -(-1 : ℚ) ^ (j + 1) = (-1 : ℚ) ^ j := by
    rw [pow_succ']
    ring
  have hpow : (-1 : ℚ) ^ j * (-1 : ℚ) ^ ((j : ℤ) - k + 1) = (-1 : ℚ) ^ (k + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
    rw [show (j : ℤ) + ((j : ℤ) - k + 1) = (k + 1) + 2 * ((j : ℤ) - k) by ring,
      zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
    rw [Even.neg_one_zpow (⟨(j : ℤ) - k, by ring⟩ : Even (2 * ((j : ℤ) - k))), mul_one]
  rw [show (j : ℤ) + k = k + (j : ℤ) by ring, hG, hneg]
  linear_combination fibAtInt ((j : ℤ) - k) * hpow +
    fibAtInt ((j : ℤ) - k) * (-1 : ℚ) ^ ((j : ℤ) - k + 1) * hsign

/-- Casorati-type identity for the offset `j`-step sequence:
`F_{j(n+2)+k} F_k - F_{j(n+1)+k} F_{j+k} = (-1)^{k+1} F_{j(n+1)} F_j`. This is the
Catalan-type identity with `a = j(n+1)+k`, `b = j+k` and `c = j`. -/
private theorem fib_step_casorati (j : ℕ) (k : ℤ) (n : ℕ) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 2) + k) * fibAtInt k -
        fibAtInt ((j : ℤ) * ((n : ℤ) + 1) + k) * fibAtInt ((j : ℤ) + k) =
      (-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) *
        fibAtInt (j : ℤ) := by
  have hC := fib_catalan ((j : ℤ) * ((n : ℤ) + 1) + k) ((j : ℤ) + k) (j : ℤ)
  have hpow : (-1 : ℚ) ^ (((j : ℤ) + k) + (j : ℤ) + 1) = (-1 : ℚ) ^ (k + 1) := by
    rw [show ((j : ℤ) + k) + (j : ℤ) + 1 = (k + 1) + 2 * (j : ℤ) by ring,
      zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
    rw [Even.neg_one_zpow (⟨(j : ℤ), by ring⟩ : Even (2 * (j : ℤ))), mul_one]
  rw [show ((j : ℤ) * ((n : ℤ) + 1) + k) + (j : ℤ) - ((j : ℤ) + k) =
      (j : ℤ) * ((n : ℤ) + 1) by ring,
    show ((j : ℤ) * ((n : ℤ) + 1) + k) + (j : ℤ) =
      (j : ℤ) * ((n : ℤ) + 2) + k by ring,
    show ((j : ℤ) + k) - (j : ℤ) = k by ring, hpow] at hC
  exact hC

/-- Clearing denominators in a Casorati-type expression. -/
private theorem div_casorati (j : ℕ) (k : ℤ) (hFk : fibAtInt k ≠ 0) (x y : ℚ) :
    x / fibAtInt k - (fibAtInt ((j : ℤ) + k) / fibAtInt k) * (y / fibAtInt k) =
      (x * fibAtInt k - y * fibAtInt ((j : ℤ) + k)) / (fibAtInt k) ^ 2 := by
  field_simp [hFk]

/-- **Offset step extension of Sury's identity, Fibonacci form.** Let $F_n$ be the Fibonacci
numbers at integer indices. For all natural numbers $j$ and $n$ and every integer $k$ with
$0 < |k| < j$,
$$F_{j(n+1)} = \frac{F_j}{F_k} \sum_{i=0}^{n}
\left(\frac{(-1)^{k+1} F_{j-k}}{F_k}\right)^{n-i} F_{ji+k}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula
(53). -/
theorem fib_step_offset_sury_sum
    (j : ℕ) (k : ℤ) (n : ℕ)
    (hjk : |k| < (j : ℤ)) (hk : k ≠ 0) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / fibAtInt k) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k) ^
              (n - i) *
            fibAtInt ((j : ℤ) * (i : ℤ) + k) := by
  have hjpos : (0 : ℤ) < (j : ℤ) := lt_of_le_of_lt (abs_nonneg k) hjk
  have hjne : (j : ℤ) ≠ 0 := ne_of_gt hjpos
  have hkj : k < (j : ℤ) := lt_of_le_of_lt (le_abs_self k) hjk
  have hjkne : (j : ℤ) - k ≠ 0 := ne_of_gt (sub_pos.mpr hkj)
  have hFk : fibAtInt k ≠ 0 := fib_ne_zero_q hk
  have hFj : fibAtInt (j : ℤ) ≠ 0 := fib_ne_zero_q hjne
  have hFjk : fibAtInt ((j : ℤ) - k) ≠ 0 := fib_ne_zero_q hjkne
  set A : ℕ → ℚ := fun m => fibAtInt ((j : ℤ) * (m : ℤ) + k) / fibAtInt k with hA
  set c1 : ℚ := lucasAtInt (j : ℤ) with hc1
  set c2 : ℚ := (-1 : ℚ) ^ (j + 1) with hc2eq
  have hc2 : c2 ≠ 0 := by
    rw [hc2eq]
    exact pow_ne_zero _ (by norm_num)
  have hA0 : A 0 = 1 := by
    simp only [hA]
    rw [show (j : ℤ) * (((0 : ℕ)) : ℤ) + k = k by simp, div_self hFk]
  have hrec : ∀ m : ℕ, A (m + 2) = c1 * A (m + 1) + c2 * A m := by
    intro m
    have hG := fib_step_recurrence j ((j : ℤ) * (((m + 1 : ℕ)) : ℤ) + k)
    rw [show ((j : ℤ) * (((m + 1 : ℕ)) : ℤ) + k) + (j : ℤ) =
        (j : ℤ) * (((m + 2 : ℕ)) : ℤ) + k by push_cast; ring,
      show ((j : ℤ) * (((m + 1 : ℕ)) : ℤ) + k) - (j : ℤ) =
        (j : ℤ) * ((m : ℤ)) + k by push_cast; ring] at hG
    simp only [hA, hc1, hc2eq]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, hG]
  have htform : c1 - A 1 =
      (-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k := by
    have hT := step_ratio j k
    simp only [hA, hc1]
    rw [show (j : ℤ) * (((1 : ℕ)) : ℤ) + k = (j : ℤ) + k by simp, eq_div_iff hFk, sub_mul,
      div_mul_cancel₀ _ hFk]
    exact hT
  have ht : c1 - A 1 ≠ 0 := by
    rw [htform]
    exact div_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num)) hFjk) hFk
  have hThm := second_order_recurrence_initial_one_sury_sum A c1 c2 hc2 hA0 hrec ht n
  have hLHS : ∀ m : ℕ, (A (m + 2) - A 1 * A (m + 1)) * (fibAtInt k) ^ 2 =
      (-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) * ((m : ℤ) + 1)) * fibAtInt (j : ℤ) := by
    intro m
    have hD := fib_step_casorati j k m
    simp only [hA]
    rw [show (j : ℤ) * (((m + 2 : ℕ)) : ℤ) + k = (j : ℤ) * ((m : ℤ) + 2) + k by push_cast; ring,
      show (j : ℤ) * (((1 : ℕ)) : ℤ) + k = (j : ℤ) + k by simp,
      show (j : ℤ) * (((m + 1 : ℕ)) : ℤ) + k = (j : ℤ) * ((m : ℤ) + 1) + k by push_cast; ring,
      div_casorati j k hFk, div_mul_cancel₀ _ (pow_ne_zero 2 hFk)]
    exact hD
  have hC : (A 2 - A 1 ^ 2) * (fibAtInt k) ^ 2 =
      (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) * fibAtInt (j : ℤ) := by
    have h0 := hLHS 0
    rw [show (0 : ℕ) + 2 = 2 by norm_num, show (0 : ℕ) + 1 = 1 by norm_num,
      show (j : ℤ) * ((((0 : ℕ)) : ℤ) + 1) = (j : ℤ) by simp] at h0
    rw [pow_two (A 1)]
    exact h0
  have hS : (∑ i ∈ Finset.range (n + 1), (c1 - A 1) ^ (n - i) * A i) * fibAtInt k =
      ∑ i ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k) ^ (n - i) *
          fibAtInt ((j : ℤ) * (i : ℤ) + k) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [htform]
    simp only [hA]
    rw [mul_assoc, div_mul_cancel₀ _ hFk]
  have key0 : (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) * fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) ^ 2 *
        (∑ i ∈ Finset.range (n + 1), (c1 - A 1) ^ (n - i) * A i) := by
    linear_combination -(hLHS n) +
      (∑ i ∈ Finset.range (n + 1), (c1 - A 1) ^ (n - i) * A i) * hC +
      (fibAtInt k) ^ 2 * hThm
  have key1 : (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) *
        (fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) * fibAtInt k) =
      (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) * (fibAtInt (j : ℤ) *
        (∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k) ^ (n - i) *
            fibAtInt ((j : ℤ) * (i : ℤ) + k))) := by
    linear_combination fibAtInt k * key0 +
      (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) ^ 2 * hS
  have hEFj : (-1 : ℚ) ^ (k + 1) * fibAtInt (j : ℤ) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (by norm_num)) hFj
  have hfin : fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) * fibAtInt k = fibAtInt (j : ℤ) *
      (∑ i ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k) ^ (n - i) *
          fibAtInt ((j : ℤ) * (i : ℤ) + k)) := mul_left_cancel₀ hEFj key1
  rw [div_mul_eq_mul_div, eq_div_iff hFk]
  exact hfin

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
