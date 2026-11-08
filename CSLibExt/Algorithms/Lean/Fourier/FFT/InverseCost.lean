/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Inverse
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Cost
import Mathlib.Tactic.Linarith

/-! # Charges of the actual conjugation-based inverse FFT -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

@[simp] theorem fftConjugate_time {R : Type u} [Star R] {n : Nat} (xs : Vector R n) :
    (fftConjugate xs).time = 3 * n := rfl

@[simp] theorem fftScale_time {R : Type u} [Mul R] {n : Nat} (scale : R) (xs : Vector R n) :
    (fftScale scale xs).time = 3 * n := rfl

/-- The three materialized maps and shared normalization add `9*n + 1` operations. -/
theorem ifft_time_add_one {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (ifft d omega xs).time + 1 = (7 * d + 10) * 2 ^ d + 1 := by
  have h := fft_time_add_one d omega (fftConjugate xs).ret
  simp only [ifft, time_bind, fftConjugate_time, fftScale_time]
  nlinarith

/-- The inverse's actual maps and actual FFT satisfy the linear-plus-FFT bound. -/
theorem ifft_time_le {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (ifft d omega xs).time ≤ 8 * (2 ^ d) * d + 9 * (2 ^ d) + 1 := by
  have h := fft_time_le d omega (fftConjugate xs).ret
  simp only [ifft, time_bind, fftConjugate_time, fftScale_time]
  nlinarith

end Cslib.Algorithms.Lean.TimeM
