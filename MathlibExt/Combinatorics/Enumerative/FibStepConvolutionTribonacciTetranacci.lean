/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FibStepConvolution
import all MathlibExt.Combinatorics.Enumerative.FibStepConvolution
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination

/-!
# Tribonacci–tetranacci convolution

## References

* Robert Frontczak and Karol Gryszka, *General Convolution Sums Involving Fibonacci m-Step
  Numbers*, Journal of Integer Sequences 27 (2024), Article 24.8.8, pp. 4–5, Theorem 1 and
  Corollary 2, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.html>.
* Robert Frontczak, *Some Fibonacci-Lucas-Tribonacci-Lucas Identities*, The Fibonacci Quarterly
  56 (2018), pp. 263–274, Theorem 2.1. The source credits this theorem for Corollary 2's
  Fibonacci–tribonacci identity, the preceding case of the same generating-function argument.
-/

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

open PowerSeries

/-- **Convolution of the Fibonacci 3-step and 4-step numbers.** Let $T_j$ and $Q_j$ be the
Fibonacci $3$-step and $4$-step numbers, where the Fibonacci $k$-step numbers start $0, 1$ and
each later term is the sum of the $k$ terms before it (terms of negative index being $0$). For
every natural number $n$,

$$\sum_{j=0}^{n} T_j \, Q_{n-j} = Q_{n+3} - T_{n+3}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
public theorem sum_trib_mul_tetra (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 3 j * fibStep 4 (n - j) =
      fibStep 4 (n + 3) - fibStep 3 (n + 3) := by
  have hg : X ^ 3 * (fibStepGF 3 * fibStepGF 4) = fibStepGF 4 - fibStepGF 3 := by
    linear_combination fibStepGF_sub_succ 3
  have hc := congrArg (coeff (n + 3) (R := ℚ)) hg
  rw [coeff_X_pow_mul] at hc
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sub,
    fibStepGF, coeff_mk] at hc
  exact_mod_cast hc

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
