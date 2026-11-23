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

/-- **Exact cost of FFT circular convolution.** Let $R$ be a field with a star-ring structure,
let $d$ be a natural number, let $\omega \in R$, and let $x$ and $y$ be vectors of length $2^d$
over $R$. The cost charged by circular convolution of $x$ and $y$ with root $\omega$, plus $2$,
equals $(21d + 16) \cdot 2^d$.

The cost is the sum of the costs of the two forward transforms, the pointwise product and the
inverse transform. -/
theorem fftCircular_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircular d omega xs ys).time + 2 = (21 * d + 16) * 2 ^ d := by
  have hx := fft_time_add_one d omega xs
  have hy := fft_time_add_one d omega ys
  have hi := ifft_time_add_one d omega
    (fftPointwise (fft d omega xs).ret (fft d omega ys).ret).ret
  simp only [fftCircular, time_bind, fftPointwise_time]
  nlinarith

/-- **Cost bound for FFT circular convolution.** Let $R$ be a field with a star-ring structure,
let $d$ be a natural number, let $\omega \in R$, and let $x$ and $y$ be vectors of length $2^d$
over $R$. The cost charged by circular convolution of $x$ and $y$ with root $\omega$ is at most
$(21d + 16) \cdot 2^d$, that is, $21 n \log_2 n + 16 n$ for the input length $n = 2^d$. -/
theorem fftCircular_time_le {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircular d omega xs ys).time ≤ (21 * d + 16) * 2 ^ d := by
  have h := fftCircular_time_add_two d omega xs ys
  omega

/-- **Exact cost of FFT linear convolution.** Let $R$ be a field with a star-ring structure,
let $d$ be a natural number, let $\omega \in R$, and let $x$ and $y$ be vectors of length $2^d$
over $R$. The cost charged by zero-padded linear convolution of $x$ and $y$ with root $\omega$,
plus $2$, equals $(42d + 80) \cdot 2^d$.

The cost is that of zero padding both inputs to length $2^{d+1}$ plus that of circular
convolution at length $2^{d+1}$. -/
theorem fftLinear_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinear d omega xs ys).time + 2 = (42 * d + 80) * 2 ^ d := by
  have h := fftCircular_time_add_two (d + 1) omega (fftPad d xs).ret (fftPad d ys).ret
  simp only [pow_succ] at h
  simp only [fftLinear, time_bind, fftPad_time]
  nlinarith

/-- **Cost bound for FFT linear convolution.** Let $R$ be a field with a star-ring structure,
let $d$ be a natural number, let $\omega \in R$, and let $x$ and $y$ be vectors of length $2^d$
over $R$. The cost charged by zero-padded linear convolution of $x$ and $y$ with root $\omega$
is at most $(42d + 80) \cdot 2^d$, that is, $42 n \log_2 n + 80 n$ for the input length
$n = 2^d$. -/
theorem fftLinear_time_le {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinear d omega xs ys).time ≤ (42 * d + 80) * 2 ^ d := by
  have h := fftLinear_time_add_two d omega xs ys
  omega

end Cslib.Algorithms.Lean.TimeM
