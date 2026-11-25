/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness
public import MathlibExt.Analysis.Fourier.VectorDFT

/-!
# Both source signs of the actual radix-two FFT

Princeton's negative principal root is `stdAddChar (-1)`, equal to
`exp (-2*pi*I/n)`. MIT/CLRS use `stdAddChar 1`, equal to `exp (2*pi*I/n)`.
The negative transform is Mathlib's canonical DFT. The positive transform
is unnormalized; multiplying it by `1/n` gives the canonical inverse DFT.
The exported root support proves the explicit exponential equalities.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open MathlibExt.Analysis.Fourier.FastFourierTransformWanted

/-- **The radix-two FFT with root $e^{-2\pi i/n}$ computes the DFT.** Let $n = 2^d$ and let
$x_0, \dots, x_{n-1}$ be complex numbers, indexed by $\mathbb{Z}/n\mathbb{Z}$. Run the radix-two
FFT on $x$ with sample root $\omega = e^{-2\pi i/n}$, the value at $-1$ of the standard additive
character of $\mathbb{Z}/n\mathbb{Z}$. Then for every $k < n$, entry $k$ of the returned vector
equals the discrete Fourier transform coefficient
$\sum_{j \in \mathbb{Z}/n\mathbb{Z}} e^{-2\pi i jk/n} x_j$. -/
theorem fft_stdAddChar_neg_one (d : Nat) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret[k.val] =
      ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0)
        (k.val : ZMod (2 ^ d)) := by
  rw [fft_correct d _ isPrimitiveRoot_stdAddChar_neg_one xs k]
  exact dftSum_stdAddChar_neg_vector xs k.val

/-- **The radix-two FFT with root $e^{2\pi i/n}$, divided by $n$, computes the inverse DFT.** Let
$n = 2^d$ and let $x_0, \dots, x_{n-1}$ be complex numbers, indexed by $\mathbb{Z}/n\mathbb{Z}$.
Run the radix-two FFT on $x$ with sample root $\omega = e^{2\pi i/n}$, the value at $1$ of the
standard additive character of $\mathbb{Z}/n\mathbb{Z}$. Then for every $k < n$, entry $k$ of
the returned vector multiplied by $1/n$ equals the inverse discrete Fourier transform coefficient
$\frac{1}{n} \sum_{j \in \mathbb{Z}/n\mathbb{Z}} e^{2\pi i jk/n} x_j$. -/
theorem fft_stdAddChar_one_normalized (d : Nat) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (2 ^ d : ℂ)⁻¹ * (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret[k.val] =
      ZMod.dft.symm (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0)
        (k.val : ZMod (2 ^ d)) := by
  rw [fft_correct d _ isPrimitiveRoot_stdAddChar_one xs k]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    invDFT_eq_dftSum_stdAddChar_vector xs k.val

end Cslib.Algorithms.Lean.TimeM
