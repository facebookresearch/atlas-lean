/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Monotone.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Rectangles of size `r × s` in nondecreasing words (wanted statements)

Statements from Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing
and Smirnov Words*, Journal of Integer Sequences 27 (2024), Article 24.8.4. A word `w_1 ⋯ w_n`
over `[k] = {1, …, k}` is drawn as a bargraph (column `i` has height `w_i`); an occurrence of an
`r × s` rectangle (height `r`, width `s`) is a placement of the rectangle inside the bargraph.
The rectangle statistic is defined as in the paper's Introduction and Figure 2.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of $r \times s$ rectangles in a bargraph.** Let $w = w_0 w_1 \cdots w_{m-1}$ be a word
of natural numbers, drawn as a bargraph whose column $i$ has height $w_i$. The number of
occurrences of an $r \times s$ rectangle (height $r$, width $s$) in $w$ is the number of pairs
$(i, y)$ of natural numbers with $i < m$, $i + s \le m$ and $y \le w_0 + \cdots + w_{m-1}$ such
that $y + r \le w_{i+j}$ for every $j < s$.

Here $(i, y)$ is the rectangle whose lower left cell is in column $i$ and row $y$, both counted
from $0$. For $s \ge 1$ the conditions $i < m$ and $y \le w_0 + \cdots + w_{m-1}$ follow from the
others; for $s = 0$ the count is $m(w_0 + \cdots + w_{m-1} + 1)$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Introduction and Figure 2. -/
def rectangleCapacity (r s : ℕ) (w : List ℕ) : ℕ :=
  ((Finset.range w.length ×ˢ Finset.range (w.sum + 1)).filter fun p =>
    p.1 + s ≤ w.length ∧ ∀ j < s, p.2 + r ≤ w.getD (p.1 + j) 0).card

/-- **Example: $3 \times 2$ rectangles in the word $345134$.** The bargraph of the word $345134$
contains exactly four rectangles of height $3$ and width $2$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Figure 2. -/
theorem rectangleCapacity_example : rectangleCapacity 3 2 [3, 4, 5, 1, 3, 4] = 4 := by
  decide

/-- **Total number of $r \times s$ rectangles in nondecreasing words.** For natural numbers $k$,
$r$, $s$ and $n$, this is the sum, over all nondecreasing words $w_1 \le w_2 \le \cdots \le w_n$ of
length $n$ over the alphabet $[k] = \{1, \dots, k\}$ (the set $W^{\nearrow}_{n,k}$), of the number
of $r \times s$ rectangles in the bargraph of $w$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollaries 2 and 6. -/
def nondecreasingRectangleTotal (k r s n : ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (Fin n → Fin k)).filter (fun w => Monotone w),
    rectangleCapacity r s (List.ofFn fun i => (w i : ℕ) + 1)

/-- **Example: $1 \times 2$ rectangles in nondecreasing words of length $2$.** The nondecreasing
words of length $2$ over $[2] = \{1, 2\}$ are $11$, $12$ and $22$, which contain $1$, $1$ and $2$
rectangles of size $1 \times 2$ respectively, so the total number of $1 \times 2$ rectangles over
all nondecreasing words of length $2$ over $[2]$ is $4$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 2. -/
theorem nondecreasingRectangleTotal_two_one_two_two : nondecreasingRectangleTotal 2 1 2 2 = 4 := by
  decide

/-- **Generating function for $1 \times s$ rectangles in nondecreasing words.** Let $k \ge 1$ and
$s \ge 1$, and let $f_k(n)$ be the total number of $1 \times s$ rectangles over all nondecreasing
words of length $n$ over $[k] = \{1, \dots, k\}$. Then, as formal power series over $\mathbb{Z}$,
$$
\Big(\sum_{n \ge 0} f_k(n)\, x^n\Big) (1 - x)^{k+1} =
x^s \sum_{i=0}^{k-1} (-1)^i \binom{i+s-2}{i} \binom{k+s}{s+i+1} x^i,
$$
and for every $n \ge s$,
$$
f_k(n) = \sum_{i=0}^{\min(k-1,\, n-s)} (-1)^i \binom{i+s-2}{i} \binom{k+s}{s+i+1}
\binom{n-s-i+k}{k}.
$$

For $s = 1$ the factor $\binom{i+s-2}{i} = \binom{i-1}{i}$ is $1$ at $i = 0$ and $0$ for $i \ge 1$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 2 (`jis-2024-24.8.4-cor-2`). -/
public theorem_wanted nondecreasingRectangleTotal_one_by_s (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    PowerSeries.mk (fun n => (nondecreasingRectangleTotal k 1 s n : ℤ)) *
        (1 - PowerSeries.X) ^ (k + 1) =
      PowerSeries.X ^ s * ∑ i ∈ Finset.range k,
        PowerSeries.C ((-1 : ℤ) ^ i * ((i + s - 2).choose i * (k + s).choose (s + i + 1) : ℕ)) *
          PowerSeries.X ^ i ∧
    ∀ n, s ≤ n → (nondecreasingRectangleTotal k 1 s n : ℤ) =
      ∑ i ∈ Finset.range (min (k - 1) (n - s) + 1),
        (-1 : ℤ) ^ i * ((i + s - 2).choose i * (k + s).choose (s + i + 1) *
          (n - s - i + k).choose k : ℕ)

/-- **Generating function for $r \times s$ rectangles in nondecreasing words.** Let $k \ge 1$,
$r \ge 1$ and $s \ge 1$, let $g_k(n)$ be the total number of $r \times s$ rectangles over all
nondecreasing words of length $n$ over $[k] = \{1, \dots, k\}$, and let $m = \max(k + 1 - r, 0)$.
Then, as formal power series over $\mathbb{Z}$,
$$
\Big(\sum_{n \ge 0} g_k(n)\, x^n\Big) (1 - x)^{k+1} =
x^s \sum_{0 \le i \le k+1-r} (-1)^i \binom{i+s-2}{i} \binom{m+s}{s+i+1} x^i,
$$
where the sum is empty when $r \ge k + 2$, and for every $n \ge s$,
$$
g_k(n) = \sum_{i=0}^{\min(m,\, n-s)} (-1)^i \binom{i+s-2}{i} \binom{m+s}{s+i+1}
\binom{n-s-i+k}{k}.
$$

For $s = 1$ the factor $\binom{i+s-2}{i} = \binom{i-1}{i}$ is $1$ at $i = 0$ and $0$ for $i \ge 1$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 6 (`jis-2024-24.8.4-cor-6`). -/
public theorem_wanted nondecreasingRectangleTotal_r_by_s (k r s : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hs : 1 ≤ s) :
    PowerSeries.mk (fun n => (nondecreasingRectangleTotal k r s n : ℤ)) *
        (1 - PowerSeries.X) ^ (k + 1) =
      PowerSeries.X ^ s * ∑ i ∈ Finset.range (k + 2 - r),
        PowerSeries.C ((-1 : ℤ) ^ i *
          ((i + s - 2).choose i * (k + 1 - r + s).choose (s + i + 1) : ℕ)) * PowerSeries.X ^ i ∧
    ∀ n, s ≤ n → (nondecreasingRectangleTotal k r s n : ℤ) =
      ∑ i ∈ Finset.range (min (k + 1 - r) (n - s) + 1),
        (-1 : ℤ) ^ i * ((i + s - 2).choose i * (k + 1 - r + s).choose (s + i + 1) *
          (n - s - i + k).choose k : ℕ)

end

end MetaMathlibExt
