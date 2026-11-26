/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Int.Fib.Basic
public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Ring

/-!
# Further extensions of Sury's identity

Multiplication by `c₁ - A 1` advances the weights of all terms already in the sum.
This gives the induction step in Gregory Dresden and Xiaoya Gao,
"Further Extensions of Sury's Identity", Theorem 1 (<https://arxiv.org/abs/2512.12841>).

For the Lucas step identity (Theorem 4), Binet's formulas give
`L_j F_{k+j} - F_j L_{k+j} = 2 (-1)^j F_k`. At `k = j*n` this accounts for the new
summand, while multiplication by `(-1)^j` updates the signs of the previous terms.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

/-- **Fibonacci numbers extended to negative indices.** For an integer $n$, the Fibonacci number
$F_n$ as a rational number, where $F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$ for natural
numbers $m$, and $F_{-m} = (-1)^{m+1} F_m$ for natural numbers $m$. -/
abbrev fibAtInt (n : ℤ) : ℚ :=
  (Int.fib n : ℚ)

/-- **Lucas numbers at integer indices.** For an integer $n$, the Lucas number $L_n$ as a
rational number, where $L_0 = 2$, $L_1 = 1$, $L_{m+2} = L_{m+1} + L_m$ for natural numbers $m$,
and $L_{-m} = (-1)^m L_m$ for natural numbers $m$. -/
def lucasAtInt (n : ℤ) : ℚ :=
  if 0 ≤ n then
    (MetaMathlibExt.lucasNumber n.toNat : ℚ)
  else
    (-1 : ℚ) ^ ((-n).toNat) *
      (MetaMathlibExt.lucasNumber (-n).toNat : ℚ)

set_option linter.unusedVariables false in
/-- **Sury's identity for a second-order recurrence starting at 1.** Let $c_1, c_2$ be rational
numbers with $c_2 \neq 0$, and let $(A_n)_{n \ge 0}$ be a sequence of rational numbers with
$A_0 = 1$ and $A_{n+2} = c_1 A_{n+1} + c_2 A_n$ for all $n \ge 0$. Put $t = c_1 - A_1$ and
assume $t \neq 0$. Then for every natural number $n$,
$$A_{n+2} - A_1 A_{n+1} = (A_2 - A_1^2) \sum_{i=0}^{n} t^{n-i} A_i.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 1. -/
theorem second_order_recurrence_initial_one_sury_sum
    (A : ℕ → ℚ) (c₁ c₂ : ℚ)
    (hc₂ : c₂ ≠ 0) (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, A (n + 2) = c₁ * A (n + 1) + c₂ * A n)
    (ht : c₁ - A 1 ≠ 0) (n : ℕ) :
    A (n + 2) - A 1 * A (n + 1) =
      (A 2 - A 1 ^ 2) *
        ∑ i ∈ Finset.range (n + 1), (c₁ - A 1) ^ (n - i) * A i := by
  let t := c₁ - A 1
  let S (k : ℕ) := ∑ i ∈ Finset.range (k + 1), t ^ (k - i) * A i
  change A (n + 2) - A 1 * A (n + 1) = (A 2 - A 1 ^ 2) * S n
  induction n with
  | zero => simp [S, hA0, pow_two]
  | succ n ih =>
    have hS : S (n + 1) = t * S n + A (n + 1) := by
      dsimp only [S]
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ', mul_assoc]
    have hA2 : A 2 = c₁ * A 1 + c₂ := by simpa [hA0] using hrec 0
    calc
      A (n + 3) - A 1 * A (n + 2) =
          t * (A (n + 2) - A 1 * A (n + 1)) + (A 2 - A 1 ^ 2) * A (n + 1) := by
            rw [hrec (n + 1), hA2]
            dsimp [t]
            ring
      _ = _ := by
        rw [ih, hS]
        ring

private theorem lucas_mul_fib_sub_fib_mul_lucas (j k : ℕ) :
    lucasAtInt j * fibAtInt ↑(k + j) - fibAtInt j * lucasAtInt ↑(k + j) =
      2 * (-1 : ℚ) ^ j * fibAtInt k := by
  change (MetaMathlibExt.lucasNumber j : ℚ) * (k + j).fib -
    (j.fib : ℚ) * MetaMathlibExt.lucasNumber (k + j) = 2 * (-1 : ℚ) ^ j * k.fib
  rify
  simp only [← MetaMathlibExt.cb_lucas_binet, Real.coe_fib_eq, ← Real.goldenRatio_mul_goldenConj,
    pow_add, mul_pow]
  ring

/-- **Step extension of Sury's identity for Lucas numbers.** Let $F_n$ and $L_n$ be the Fibonacci
and Lucas numbers at integer indices. For all natural numbers $j \ge 1$ and $n$, in the rational
numbers,
$$2 \left(\frac{L_j}{2}\right)^{n+1} \frac{F_{jn}}{F_j} + 2 (-1)^{jn} =
\sum_{i=0}^{n} (-1)^{j(n+i)} \left(\frac{L_j}{2}\right)^i L_{ji}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 4. -/
theorem lucas_step_sury_sum
    (j n : ℕ) (hj : 1 ≤ j) :
    2 * (lucasAtInt (j : ℤ) / 2) ^ (n + 1) *
          (fibAtInt ((j : ℤ) * (n : ℤ)) / fibAtInt (j : ℤ)) +
        2 * (-1 : ℚ) ^ (j * n) =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (j * (n + i)) * (lucasAtInt (j : ℤ) / 2) ^ i *
          lucasAtInt ((j : ℤ) * (i : ℤ)) := by
  simp only [← Nat.cast_mul]
  set a := lucasAtInt (j : ℤ) / 2 with ha
  have hF : fibAtInt (j : ℤ) ≠ 0 := by
    simp [fibAtInt, Nat.ne_of_gt hj]
  induction n with
  | zero => simp [fibAtInt, lucasAtInt, MetaMathlibExt.lucasNumber]
  | succ n ih =>
    -- Increasing the upper index multiplies each previous summand by the same sign.
    have hterm (i : ℕ) :
        (-1 : ℚ) ^ (j * (n + 1 + i)) * a ^ i * lucasAtInt ↑(j * i) =
          (-1 : ℚ) ^ j * ((-1 : ℚ) ^ (j * (n + i)) * a ^ i * lucasAtInt ↑(j * i)) := by
      rw [show n + 1 + i = 1 + (n + i) by omega, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    have hlast : (-1 : ℚ) ^ (j * (n + 1 + (n + 1))) = 1 :=
      Even.neg_one_pow ⟨j * (n + 1), Nat.mul_add ..⟩
    have hshift := lucas_mul_fib_sub_fib_mul_lucas j (j * n)
    rw [← Nat.mul_succ] at hshift
    have hstep : 2 * a * (fibAtInt ↑(j * (n + 1)) / fibAtInt j) =
        2 * (-1 : ℚ) ^ j * (fibAtInt ↑(j * n) / fibAtInt j) +
          lucasAtInt ↑(j * (n + 1)) := by
      rw [ha]
      field_simp [hF]
      linear_combination hshift
    rw [Finset.sum_range_succ, hlast, one_mul]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← ih, pow_succ a (n + 1),
      show (-1 : ℚ) ^ (j * (n + 1)) = (-1 : ℚ) ^ (j * n) * (-1 : ℚ) ^ j by
        rw [Nat.mul_succ, pow_add]]
    linear_combination a ^ (n + 1) * hstep

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
