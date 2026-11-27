/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import MathlibExt.Combinatorics.Enumerative.FibStepConvolution
import all MathlibExt.Combinatorics.Enumerative.FibStepConvolution

/-!
# Tetranacci–pentanacci convolution

Shifting the product of the tetranacci and pentanacci series by four gives the difference
of the two series. The coefficients of this product give the convolution.

## References

* Robert Frontczak and Karol Gryszka, *General Convolution Sums Involving Fibonacci $m$-Step
  Numbers*, Journal of Integer Sequences 27 (2024), Article 24.8.8, pp. 1–29, Theorem 1
  and Corollary 2.
* Robert Frontczak, *Some Fibonacci-Lucas-Tribonacci-Lucas Identities*, The Fibonacci
  Quarterly 56 (2018), pp. 263–274, Theorem 2.1. Frontczak and Gryszka credit this result
  for the Fibonacci–tribonacci case of Corollary 2.
-/

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

open PowerSeries

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
      fibStep 5 (n + 4) - fibStep 4 (n + 4) := by
  have h : X ^ 4 * (fibStepGF 4 * fibStepGF 5) = fibStepGF 5 - fibStepGF 4 := by
    simpa only [neg_sub, neg_mul, neg_neg, mul_assoc] using
      (congrArg Neg.neg (fibStepGF_sub_succ 4)).symm
  have hc := congrArg (coeff (n + 4) (R := ℚ)) h
  rw [coeff_X_pow_mul] at hc
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sub,
    fibStepGF, coeff_mk] at hc
  exact_mod_cast hc

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
