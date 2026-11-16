/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.QFTAmplitudes
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Tests for QFT amplitudes

* The one-output case: with `N = 1` and `s = 1` the single amplitude has `normSq = 1`.
* The four-point QFT, `ω = exp (2πi / 4)` and `s = 1 / 2`: row `1` is normalized, and the
  distinct rows `1` and `3` are orthogonal, from the primitive-root fact
  `Complex.isPrimitiveRoot_exp`.
-/

@[expose] public section

namespace MathlibExtTest.Quantum.QFTAmplitudes

open MathlibExt.Quantum.QFTAmplitudes

/-- With `N = 1`, `s = 1`, the single amplitude has normSq 1. -/
example : ∑ k ∈ Finset.range 1, Complex.normSq (qftAmp 1 1 0 k) = 1 :=
  qftAmp_norm_sum (N := 1) 1 (by norm_num) 1 (by norm_num) 0

/-- `exp (2πi / 4)` is a primitive fourth root of unity. -/
theorem omega4_isPrimitiveRoot :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) 4 :=
  Complex.isPrimitiveRoot_exp 4 (by norm_num)

/-- Row `1` of the four-point QFT is normalized. -/
example : ∑ k ∈ Finset.range 4,
    Complex.normSq (qftAmp (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) (1 / 2) 1 k) = 1 :=
  qftAmp_norm_sum (N := 4) _ (omega4_isPrimitiveRoot.norm'_eq_one (by norm_num)) (1 / 2)
    (by norm_num) 1

/-- Rows `1` and `3` of the four-point QFT are orthogonal. -/
example : ∑ k ∈ Finset.range 4,
    (starRingEnd ℂ (qftAmp (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) (1 / 2) 1 k)) *
      (qftAmp (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) (1 / 2) 3 k) = 0 :=
  qftAmp_inner_eq_zero omega4_isPrimitiveRoot (1 / 2) (j₁ := 1) (j₂ := 3) (by decide)

end MathlibExtTest.Quantum.QFTAmplitudes
