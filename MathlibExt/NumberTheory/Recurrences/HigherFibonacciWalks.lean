/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.Recurrences.WeightedHigherFibSum

/-!
# Fibonacci walk counts

This file defines shifted Fibonacci self-convolutions.
`evenFibWalkCount_odd_length_eq_oddFibWalkCount` proves that the even and odd parts of the
ordinary Fibonacci self-convolution agree at odd length.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

/-- **The standard order-$m$ Fibonacci sequence.** A sequence $F : \mathbb{Z} \to \mathbb{Q}$ is
the standard order-$m$ Fibonacci sequence if it satisfies the $m$-step Fibonacci recurrence,
$F_i = 0$ for every natural number $i < m - 1$, and $F_{m-1} = 1$, where $m - 1$ is computed in
the integers. -/
def IsStandardHigherFib (m : ℕ) (F : ℤ → ℚ) : Prop :=
  IsHigherFibRecurrence m F ∧
    (∀ i : ℕ, i < m - 1 → F (i : ℤ) = 0) ∧
    F ((m : ℤ) - 1) = 1

/-- **First-moment weighted sum.** For a sequence $F : \mathbb{Z} \to \mathbb{Q}$, a natural number
$m$, integers $N$ and $l$, and a rational number $q$, $S_2(m,N,l,q) = \sum_{k=0}^{N} k q^k F_{k+l}$;
for $N < 0$ this is the empty sum $0$. The value does not depend on $m$. -/
def weightedHigherFibMomentSum (F : ℤ → ℚ) (_m : ℕ) (N l : ℤ)
    (q : ℚ) : ℚ :=
  if N < 0 then
    0
  else
    ∑ k ∈ Finset.range (N.toNat + 1),
      (k : ℚ) * q ^ (k : ℤ) * F ((k : ℤ) + l)

/-- **Shifted self-convolution.** For a sequence $F : \mathbb{Z} \to \mathbb{Q}$ and natural
numbers $m$ and $n$, the shifted self-convolution is
$w_n^{(m)} = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$, with the indices computed in the integers. -/
def higherFibWalk (F : ℤ → ℚ) (m n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    F ((j : ℤ) + (m : ℤ) - 1) * F ((n : ℤ) - (j : ℤ) + (m : ℤ) - 1)

/-- **Fibonacci numbers at integer indices.** For an integer $n$, $F_n$ is the $n$-th Fibonacci
number as a rational number: $F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$ for $n \ge 0$, and
$F_{-n} = (-1)^{n+1} F_n$ for $n > 0$. -/
abbrev fibQ (n : ℤ) : ℚ :=
  (Int.fib n : ℚ)

/-- **Fibonacci self-convolution.** For $n \ge 0$, $v_n$ is the rational number
$v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$, where $F_i$ is the $i$-th Fibonacci number
($F_0 = 0$, $F_1 = 1$).

This sum encodes algebraically the number of Fibonacci tiling walks. -/
def fibWalkCount (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)

/-- **Even part of the Fibonacci self-convolution.** For $n \ge 0$, $E_n$ is the rational number
$\sum F_{j+1} F_{n-j+1}$, the sum taken over the even integers $j$ with $0 \le j \le n$, where
$F_i$ is the $i$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$). -/
def evenFibWalkCount (n : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range (n + 1)).filter Even,
    fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)

/-- **Odd part of the Fibonacci walk count.** For a natural number $n$, this is the sum of
$F_{j+1} F_{n-j+1}$ over the odd $j$ with $0 \le j \le n$, where $F_k$ are the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{k+2} = F_{k+1} + F_k$). It is the part of
$v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$ that comes from odd $j$. -/
def oddFibWalkCount (n : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range (n + 1)).filter Odd,
    fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)

/-- **Even and odd parts of the Fibonacci self-convolution agree at odd length.** Let $F_n$
denote the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $E_n$ and $O_n$ be
the sums of $F_{j+1} F_{n-j+1}$ over the even and over the odd integers $j$ with
$0 \le j \le n$. For every integer $k \ge 1$, $E_{2k-1} = O_{2k-1}$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Lemma 5. -/
theorem evenFibWalkCount_odd_length_eq_oddFibWalkCount
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k - 1) = oddFibWalkCount (2 * k - 1) := by
  let n := 2 * k - 1
  change evenFibWalkCount n = oddFibWalkCount n
  have hn : n % 2 = 1 := by
    dsimp [n]
    omega
  unfold evenFibWalkCount oddFibWalkCount
  -- Reflection across the interval swaps parity and interchanges the Fibonacci factors.
  refine Finset.sum_nbij' (n - ·) (n - ·) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.even_iff, Nat.odd_iff]
  all_goals intro j hj
  · omega
  · omega
  · exact Nat.sub_sub_self hj.1
  · exact Nat.sub_sub_self hj.1
  · rw [Nat.cast_sub hj.1, sub_sub_cancel]
    exact mul_comm _ _

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
