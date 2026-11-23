/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.SeriesDivisorInverseConvolution

open PowerSeries MetaMathlibExt

-- Degree two is the first degree with an interior term in the self-convolution.
example {R : Type*} [CommRing R] (A B : PowerSeries R) (hAB : A * B = 1)
    (s : ℕ → R) (hs0 : s 0 = 0)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A) :
    s 2 = 2 * coeff 2 A * coeff 0 B + coeff 1 A * coeff 1 B ∧
      s 1 ^ 2 = -(coeff 1 A * coeff 1 B) := by
  have h := series_divisor_inverse_convolution A B hAB s hs0 hA 2
  norm_num [Finset.sum_range_succ, show Finset.Icc 1 2 = {1, 2} by decide, hs0, pow_two] at h ⊢
  exact h
