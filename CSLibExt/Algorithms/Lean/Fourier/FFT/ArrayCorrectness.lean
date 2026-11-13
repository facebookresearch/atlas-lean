/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public import CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Cost

/-! # The admitted array has the actual FFT coefficients and actual execution charge -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- **The array FFT agrees with the vector FFT.** Let $R$ be a commutative ring, $d$ a natural
number, $\omega \in R$ and $x$ a vector over $R$ of length $2^d$. Then the array FFT of $x$,
viewed as an array, with root $\omega$ returns a result, namely the output of the radix-two FFT
of the length-$2^d$ vector $x$ with root $\omega$, viewed as an array. -/
theorem fftArray_ret_of_vector {R : Type u} [CommRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).ret = some (fft d omega xs).ret.toArray := by
  rcases xs with ⟨values, hsize⟩
  have hlog : values.size.log2 = d := by rw [hsize, Nat.log2_two_pow]
  subst d
  unfold fftArray
  rw [dite_eq_left hsize]
  rfl

/-- **The array FFT costs the same as the vector FFT.** Let $R$ be a commutative ring, $d$ a
natural number, $\omega \in R$ and $x$ a vector over $R$ of length $2^d$. Then the cost of the
array FFT of $x$, viewed as an array, with root $\omega$ equals the cost of the radix-two FFT of
the length-$2^d$ vector $x$ with root $\omega$. -/
theorem fftArray_time_of_vector {R : Type u} [CommRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).time = (fft d omega xs).time := by
  rcases xs with ⟨values, hsize⟩
  have hlog : values.size.log2 = d := by rw [hsize, Nat.log2_two_pow]
  subst d
  unfold fftArray
  rw [dite_eq_left hsize]
  rfl

/-- **The array FFT computes the discrete Fourier transform.** Let $d$ be a natural number,
$\omega \in \mathbb{C}$ a primitive $2^d$-th root of unity, $x_0, \dots, x_{2^d - 1}$ complex
numbers and $k < 2^d$. Then the array FFT of the array $(x_0, \dots, x_{2^d - 1})$ with root
$\omega$ returns an array $y$ of length $2^d$ whose entry at index $k$ is the discrete Fourier
sum $\sum_{j=0}^{2^d - 1} \omega^{jk} x_j$. -/
theorem fftArray_correct (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    ∃ ys : Array ℂ, (fftArray omega xs.toArray).ret = some ys ∧
      ys.size = 2 ^ d ∧
      ys.getD k.val 0 =
        MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum
          (2 ^ d) omega (fun j => xs.toArray.getD j 0) k.val := by
  refine ⟨(fft d omega xs).ret.toArray, fftArray_ret_of_vector d omega xs,
    (fft d omega xs).ret.size_toArray, ?_⟩
  have hsample : (fft d omega xs).ret.toArray.getD k.val 0 =
      (fft d omega xs).ret[k.val] :=
    (Array.getElem_eq_getD (h := by simp) 0).symm
  exact hsample.trans (fft_correct d omega hroot xs k)

/-- **Exact cost of the array FFT.** Let $R$ be a commutative ring, $d$ a natural number,
$\omega \in R$ and $x$ a vector over $R$ of length $2^d$. Then the cost $T$ of the array FFT of
$x$, viewed as an array, with root $\omega$ satisfies $T + 1 = (7d + 1) \cdot 2^d$.

Costs are counted in the scalar-operation and array-access model of the radix-two FFT. -/
theorem fftArray_time_add_one {R : Type u} [CommRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).time + 1 = (7 * d + 1) * 2 ^ d := by
  rw [fftArray_time_of_vector]
  exact fft_time_add_one d omega xs

end Cslib.Algorithms.Lean.TimeM
