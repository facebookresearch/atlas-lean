/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.RectangleCapacityNondecreasingWords

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

end

end MetaMathlibExt
