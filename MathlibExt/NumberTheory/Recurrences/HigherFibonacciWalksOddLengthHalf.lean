/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

/-!
# Halving the Fibonacci self-convolution at odd length

At odd length, the sums over even and odd summation indices each equal half the full convolution.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

/-- **Halving the Fibonacci self-convolution at odd length.** Let $F_n$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$,
and let $E_n$ and $O_n$ be the sums of the same terms $F_{j+1} F_{n-j+1}$ over the even and over
the odd integers $j$ with $0 \le j \le n$. For every integer $k \ge 1$,
$E_{2k-1} = v_{2k-1}/2$ and $O_{2k-1} = v_{2k-1}/2$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem fibWalkCounts_odd_length_eq_half
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k - 1) = fibWalkCount (2 * k - 1) / 2 ∧
      oddFibWalkCount (2 * k - 1) = fibWalkCount (2 * k - 1) / 2 := by
  let n := 2 * k - 1
  change evenFibWalkCount n = fibWalkCount n / 2 ∧ oddFibWalkCount n = fibWalkCount n / 2
  have hParity : evenFibWalkCount n = oddFibWalkCount n :=
    evenFibWalkCount_odd_length_eq_oddFibWalkCount k hk
  have hSum : evenFibWalkCount n + oddFibWalkCount n = fibWalkCount n := by
    unfold evenFibWalkCount oddFibWalkCount fibWalkCount
    have hFilter : (Finset.range (n + 1)).filter (fun j => ¬ Even j) =
        (Finset.range (n + 1)).filter Odd :=
      Finset.filter_congr fun _ _ => Nat.not_even_iff_odd
    rw [← hFilter]
    exact Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) Even _
  constructor <;> linarith only [hParity, hSum]

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
