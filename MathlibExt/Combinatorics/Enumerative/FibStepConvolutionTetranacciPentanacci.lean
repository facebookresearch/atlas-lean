/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FibStepConvolution
import all MathlibExt.Combinatorics.Enumerative.FibStepConvolution

/-!
# Tetranacci–pentanacci convolution

The consecutive-order coefficient identity from `FibStepConvolution` gives the
tetranacci–pentanacci convolution at order four. The shared Lean argument is adapted from
the original proof of `sum_trib_mul_tetra` in `FibStepConvolutionTribonacciTetranacci`.

## References

* Robert Frontczak and Karol Gryszka, *General Convolution Sums Involving Fibonacci m-Step
  Numbers*, Journal of Integer Sequences 27 (2024), Article 24.8.8, pp. 4–5, Theorem 1 and
  Corollary 2, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.html>.
* Robert Frontczak, *Some Fibonacci-Lucas-Tribonacci-Lucas Identities*, The Fibonacci
  Quarterly 56 (2018), pp. 263–274, Theorem 2.1. Frontczak and Gryszka credit this result
  for the Fibonacci–tribonacci case of Corollary 2.
-/

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

/-- **Convolution of the Fibonacci 4-step and 5-step numbers.** Let $Q_j$ and $P_j$ be the
Fibonacci $4$-step and $5$-step numbers, where the Fibonacci $k$-step numbers start $0, 1$ and
each later term is the sum of the $k$ terms before it (terms of negative index being $0$). For
every natural number $n$,

$$\sum_{j=0}^{n} Q_j \, P_{n-j} = P_{n+4} - Q_{n+4}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
public theorem sum_tetra_mul_penta (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 4 j * fibStep 5 (n - j) =
      fibStep 5 (n + 4) - fibStep 4 (n + 4) :=
  sum_fibStep_mul_succ_eq_sub 4 n

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
