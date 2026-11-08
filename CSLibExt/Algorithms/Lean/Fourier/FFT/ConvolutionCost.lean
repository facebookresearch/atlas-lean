/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Convolution
public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCost
import Mathlib.Tactic.Linarith

/-! # Costs of actual stored-transform convolution and direct zero padding -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

@[simp] theorem fftPointwise_time {R : Type u} [Mul R] {n : Nat}
    (xs ys : Vector R n) : (fftPointwise xs ys).time = 4 * n := rfl

@[simp] theorem fftPad_time {R : Type u} [Zero R] (d : Nat)
    (xs : Vector R (2 ^ d)) : (fftPad d xs).time = 3 * 2 ^ d := rfl

/-- Two actual forward calls, product materialization and the actual inverse. -/
theorem fftCircular_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircular d omega xs ys).time + 2 = (21 * d + 16) * 2 ^ d := by
  have hx := fft_time_add_one d omega xs
  have hy := fft_time_add_one d omega ys
  have hi := ifft_time_add_one d omega
    (fftPointwise (fft d omega xs).ret (fft d omega ys).ret).ret
  simp only [fftCircular, time_bind, fftPointwise_time]
  nlinarith

/-- The complete circular executor has an `n*log2 n + n` bound. -/
theorem fftCircular_time_le {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircular d omega xs ys).time ≤ (21 * d + 16) * 2 ^ d := by
  have h := fftCircular_time_add_two d omega xs ys
  omega

/-- Both direct padding calls and circular convolution at twice the input length. -/
theorem fftLinear_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinear d omega xs ys).time + 2 = (42 * d + 80) * 2 ^ d := by
  have h := fftCircular_time_add_two (d + 1) omega (fftPad d xs).ret (fftPad d ys).ret
  simp only [pow_succ] at h
  simp only [fftLinear, time_bind, fftPad_time]
  nlinarith

/-- The complete padded executor has an `n*log2 n + n` bound. -/
theorem fftLinear_time_le {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinear d omega xs ys).time ≤ (42 * d + 80) * 2 ^ d := by
  have h := fftLinear_time_add_two d omega xs ys
  omega

end Cslib.Algorithms.Lean.TimeM
