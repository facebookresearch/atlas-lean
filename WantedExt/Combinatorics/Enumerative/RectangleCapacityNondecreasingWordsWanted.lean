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

/-- The number of occurrences of an `r × s` rectangle (height `r`, width `s`) in the bargraph of
the word `w`: pairs `(i, y)` (0-indexed column, row) such that columns `i, …, i + s - 1` exist and
all have height at least `y + r`.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Introduction and Figure 2. -/
def rectangleCapacity (r s : ℕ) (w : List ℕ) : ℕ :=
  ((Finset.range w.length ×ˢ Finset.range (w.sum + 1)).filter fun p =>
    p.1 + s ≤ w.length ∧ ∀ j < s, p.2 + r ≤ w.getD (p.1 + j) 0).card

/-- Characteristic value: the word `345134` contains four `3 × 2` rectangles.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Figure 2. -/
theorem rectangleCapacity_example : rectangleCapacity 3 2 [3, 4, 5, 1, 3, 4] = 4 := by
  decide

/-- The total number of `r × s` rectangles over all nondecreasing words of length `n` over `[k]`
(the set `W^↗_{n,k}`); a word is a monotone map `Fin n → Fin k`, letter `i` read as `i + 1`.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollaries 2 and 6. -/
def nondecreasingRectangleTotal (k r s n : ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (Fin n → Fin k)).filter (fun w => Monotone w),
    rectangleCapacity r s (List.ofFn fun i => (w i : ℕ) + 1)

/-- Characteristic values: over `[2]` the nondecreasing words of length `2` are `11, 12, 22`,
containing `1 + 1 + 2 = 4` rectangles of size `1 × 2`.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 2. -/
theorem nondecreasingRectangleTotal_two_one_two_two : nondecreasingRectangleTotal 2 1 2 2 = 4 := by
  decide

/-- The total number `f_k(n)` of `1 × s` rectangles over `W^↗_{n,k}` has generating function
`x^s ∑_{i=0}^{k-1} (-1)^i C(i+s-2, i) C(k+s, s+i+1) x^i / (1 - x)^{k+1}`; hence for `n ≥ s`,
`f_k(n) = ∑_{i=0}^{min(k-1, n-s)} (-1)^i C(i+s-2, i) C(k+s, s+i+1) C(n-s-i+k, k)`. The generating
function is stated after multiplying by `(1 - X)^{k+1}`; `C(i+s-2, i)` uses truncated subtraction,
which agrees with the paper's value at `s = 1` (`C(-1, 0) = 1`, `C(i-1, i) = 0`).

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

/-- The total number `g_k(n)` of `r × s` rectangles over `W^↗_{n,k}` has generating function
`x^s ∑_{i=0}^{k-r+1} (-1)^i C(i+s-2, i) C(k-r+1+s, s+i+1) x^i / (1 - x)^{k+1}`; hence for `n ≥ s`,
`g_k(n) = ∑_{i=0}^{min(k-r+1, n-s)} (-1)^i C(i+s-2, i) C(k-r+1+s, s+i+1) C(n-s-i+k, k)`.
`k - r + 1` is the truncated `k + 1 - r` (for `k < r - 1` both sides vanish); the generating
function is stated after multiplying by `(1 - X)^{k+1}`.

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
