/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Walks in tiled rectangles and higher-order Fibonacci convolutions

Statements from Jan Sedlák and Antonín Slavík, "Walks in Tiled
Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.3.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Slavik/slavik4.html>).

Sequences are integer-indexed and valued in `ℚ`.  For `m ≥ 1`, an
`m`-step Fibonacci recurrence means
`F n = F (n-1) + ⋯ + F (n-m)` for every integer `n`.  The standard
sequence also has `F 0 = ⋯ = F (m-2) = 0` and `F (m-1) = 1`.

The weighted sums `S` and `S₂` allow an integer upper limit; a
negative upper limit gives the empty sum.  This is the convention
needed at `n = 0` in Theorem 3.

Theorem 4 is stated for `n ≥ 2*m - 2`.  The printed theorem says
all `n ≥ 0`, but its derivation substitutes `n - 2*m + 2` into a
formula for `w` at a nonnegative index.  Under the empty-sum
convention the unrestricted displayed formula already fails at
`(m, n) = (2, 0)`: the self-convolution is `0`, while the formula
gives `9 / 16`.  The restricted range is therefore recorded
explicitly here and in the source-audit table.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.Data.Rat.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

/-- **The $m$-step Fibonacci recurrence.** A sequence $F : \mathbb{Z} \to \mathbb{Q}$ satisfies the
$m$-step Fibonacci recurrence if $F_n = F_{n-1} + F_{n-2} + \dots + F_{n-m}$ for every integer
$n$, that is, $F_n = \sum_{i=0}^{m-1} F_{n-i-1}$. For $m = 0$ this says $F_n = 0$ for all $n$. -/
def IsHigherFibRecurrence (m : ℕ) (F : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, F n = ∑ i ∈ Finset.range m, F (n - (i : ℤ) - 1)

/-- **The standard order-$m$ Fibonacci sequence.** A sequence $F : \mathbb{Z} \to \mathbb{Q}$ is
the standard order-$m$ Fibonacci sequence if it satisfies the $m$-step Fibonacci recurrence,
$F_i = 0$ for every natural number $i < m - 1$, and $F_{m-1} = 1$, where $m - 1$ is computed in
the integers. -/
def IsStandardHigherFib (m : ℕ) (F : ℤ → ℚ) : Prop :=
  IsHigherFibRecurrence m F ∧
    (∀ i : ℕ, i < m - 1 → F (i : ℤ) = 0) ∧
    F ((m : ℤ) - 1) = 1

/-- **Weighted sum of a sequence.** For a sequence $F : \mathbb{Z} \to \mathbb{Q}$, a natural number
$m$, integers $N$ and $l$, and a rational number $q$, $S(m,N,l,q) = \sum_{k=0}^{N} q^k F_{k+l}$;
for $N < 0$ this is the empty sum $0$.

The order $m$ is carried explicitly to match the paper notation, although the sum itself only
uses $F$, $N$, $l$, and $q$. -/
def weightedHigherFibSum (F : ℤ → ℚ) (_m : ℕ) (N l : ℤ) (q : ℚ) : ℚ :=
  if N < 0 then
    0
  else
    ∑ k ∈ Finset.range (N.toNat + 1), q ^ (k : ℤ) * F ((k : ℤ) + l)

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

/-- **Recurrence for the shifted self-convolution of higher-order Fibonacci numbers.** Let
$m \ge 1$ and let $(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$, and for $n \ge 0$ let $w_n = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$. Then for
every integer $n \ge 0$, $(m+1) w_{n+1} - 2m w_n = (n+m+2) F_{n+m} - (n+m) F_{n+m-1}$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 1. -/
theorem_wanted higherFibWalk_recurrence
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) :
    ((m : ℚ) + 1) * higherFibWalk F m (n + 1) -
        2 * (m : ℚ) * higherFibWalk F m n =
      ((n : ℚ) + (m : ℚ) + 2) * F ((n : ℤ) + (m : ℤ)) -
        ((n : ℚ) + (m : ℚ)) * F ((n : ℤ) + (m : ℤ) - 1)

/-- **Closed form for weighted sums of an $m$-step Fibonacci sequence.** Let $m \ge 1$ and let
$F : \mathbb{Z} \to \mathbb{Q}$ satisfy the $m$-step Fibonacci recurrence
$F_k = F_{k-1} + \dots + F_{k-m}$ for every integer $k$. For every natural number $n$, every
integer $l$ and every rational number $q$ with $q^{m+1} - 2q + 1 \ne 0$, the weighted sum
$S(m,n,l,q) = \sum_{k=0}^{n} q^k F_{k+l}$ equals
$$
\frac{(q-1)\Bigl(q^{n+1}F_{n+l+1} - F_l +
\sum_{i=1}^{m-1}\sum_{j=1}^{i} q^{i+1-j}\bigl(q^{n+1}F_{n+l-j+1} - F_{l-j}\bigr)\Bigr)}
{q^{m+1} - 2q + 1}.
$$

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 2. -/
theorem_wanted weightedHigherFibSum_eq
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsHigherFibRecurrence m F)
    (n : ℕ) (l : ℤ) (q : ℚ)
    (hq : q ^ (m + 1) - 2 * q + 1 ≠ 0) :
    weightedHigherFibSum F m (n : ℤ) l q =
      ((q - 1) *
        (q ^ (n + 1) * F ((n : ℤ) + l + 1) - F l +
          ∑ i ∈ Finset.Icc 1 (m - 1),
            ∑ j ∈ Finset.Icc 1 i,
              q ^ (i + 1 - j) *
                (q ^ (n + 1) * F ((n : ℤ) + l - (j : ℤ) + 1) -
                  F (l - (j : ℤ))))) /
        (q ^ (m + 1) - 2 * q + 1)

/-- **Explicit formula for the shifted self-convolution of higher-order Fibonacci numbers.** Let
$m \ge 1$ and let $(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $n \ge 0$ let $w_n = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 0$,

$$
w_n = \left(\frac{2m}{m+1}\right)^{n} +
\frac{(2m)^{n-1}}{(m+1)^{n}} \bigl((m+2) S(n-1, m, q) + S_2(n-1, m, q) -
m S(n-1, m-1, q) - S_2(n-1, m-1, q)\bigr).
$$

At $n = 0$ the weighted sums have upper limit $-1$ and are empty.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 3. -/
theorem_wanted higherFibWalk_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) :
    higherFibWalk F m n =
      (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ n +
        ((2 * (m : ℚ)) ^ ((n : ℤ) - 1) / ((m : ℚ) + 1) ^ n) *
          (((m : ℚ) + 2) *
              weightedHigherFibSum F m ((n : ℤ) - 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) +
            weightedHigherFibMomentSum F m ((n : ℤ) - 1) (m : ℤ)
              (((m : ℚ) + 1) / (2 * (m : ℚ))) -
            (m : ℚ) *
              weightedHigherFibSum F m ((n : ℤ) - 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
            weightedHigherFibMomentSum F m ((n : ℤ) - 1)
              ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))))

/-- **Self-convolution of higher-order Fibonacci numbers.** Let $m \ge 1$ and let
$(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $p \ge 0$ let $w_p = \sum_{j=0}^{p} F_{j+m-1} F_{p-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 2m - 2$, writing $p = n - 2m + 2$,

$$
\sum_{i=0}^{n} F_i F_{n-i} = w_p = \left(\frac{2m}{m+1}\right)^{p} +
\frac{(2m)^{p-1}}{(m+1)^{p}} \bigl((m+2) S(p-1, m, q) + S_2(p-1, m, q) -
m S(p-1, m-1, q) - S_2(p-1, m-1, q)\bigr).
$$

The source states the formula for all $n \ge 0$, but for $m \ge 2$ it fails when
$n < 2m - 2$: at $m = 2$ and $n = 0$ the left side is $0$ and the right side is $9/16$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 4. -/
theorem_wanted higherFib_selfConvolution_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) (hn : 2 * m - 2 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        higherFibWalk F m (n - (2 * m - 2)) ∧
      (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ ((n : ℤ) - 2 * (m : ℤ) + 2) +
          ((2 * (m : ℚ)) ^ ((n : ℤ) - 2 * (m : ℤ) + 1) /
              ((m : ℚ) + 1) ^ ((n : ℤ) - 2 * (m : ℤ) + 2)) *
            (((m : ℚ) + 2) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  (m : ℤ) (((m : ℚ) + 1) / (2 * (m : ℚ))) +
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              (m : ℚ) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ))))

/-- **Even and odd parts of the Fibonacci self-convolution agree at odd length.** Let $F_n$
denote the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $E_n$ and $O_n$ be
the sums of $F_{j+1} F_{n-j+1}$ over the even and over the odd integers $j$ with
$0 \le j \le n$. For every integer $k \ge 1$, $E_{2k-1} = O_{2k-1}$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Lemma 5. -/
theorem_wanted evenFibWalkCount_odd_length_eq_oddFibWalkCount
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k - 1) = oddFibWalkCount (2 * k - 1)

/-- **Even and odd parts of the Fibonacci self-convolution at even length.** Let $F_n$ denote
the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $E_n$ and $O_n$ be the
sums of $F_{j+1} F_{n-j+1}$ over the even and over the odd integers $j$ with $0 \le j \le n$.
For every integer $k \ge 1$, $E_{2k} = O_{2k} + F_{2k+2}$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Lemma 5. -/
theorem_wanted evenFibWalkCount_even_length_eq_odd_add_fib
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
      oddFibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)

/-- **Halving the Fibonacci self-convolution at odd length.** Let $F_n$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$,
and let $E_n$ and $O_n$ be the sums of the same terms $F_{j+1} F_{n-j+1}$ over the even and over
the odd integers $j$ with $0 \le j \le n$. For every integer $k \ge 1$,
$E_{2k-1} = v_{2k-1}/2$ and $O_{2k-1} = v_{2k-1}/2$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem_wanted fibWalkCounts_odd_length_eq_half
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k - 1) = fibWalkCount (2 * k - 1) / 2 ∧
      oddFibWalkCount (2 * k - 1) = fibWalkCount (2 * k - 1) / 2

/-- **Halving the Fibonacci self-convolution at even length.** Let $F_n$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$,
and let $E_n$ and $O_n$ be the sums of the same terms $F_{j+1} F_{n-j+1}$ over the even and over
the odd integers $j$ with $0 \le j \le n$. For every integer $k \ge 1$,
$E_{2k} = (v_{2k} + F_{2k+2})/2$ and $O_{2k} = (v_{2k} - F_{2k+2})/2$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem_wanted fibWalkCounts_even_length_eq
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)) / 2 ∧
      oddFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) - fibQ (2 * (k : ℤ) + 2)) / 2

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
