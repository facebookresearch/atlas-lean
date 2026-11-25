/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Butterfly

/-! # Characteristic return values of the actual radix-two executor -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {R : Type u} [CommRing R]

omit [CommRing R] in
/-- **The FFT split extracts the even-indexed entries.** Let $R$ be a type, $m$ a natural number
and $x = (x_0, \dots, x_{2m-1})$ a vector of length $2m$ over $R$. For every $k < m$, entry $k$
of the first (even) vector returned by the FFT split of $x$ is $x_{2k}$. -/
theorem fftSplit_ret_even {m : Nat} (xs : Vector R (m * 2)) (k : Fin m) :
    (fftSplit xs).ret.1[k.val] = xs[2 * k.val]'(by have h := k.isLt; omega) := by
  simp [fftSplit]

omit [CommRing R] in
/-- **The FFT split extracts the odd-indexed entries.** Let $R$ be a type, $m$ a natural number
and $x = (x_0, \dots, x_{2m-1})$ a vector of length $2m$ over $R$. For every $k < m$, entry $k$
of the second (odd) vector returned by the FFT split of $x$ is $x_{2k+1}$. -/
theorem fftSplit_ret_odd {m : Nat} (xs : Vector R (m * 2)) (k : Fin m) :
    (fftSplit xs).ret.2[k.val] = xs[2 * k.val + 1]'(by have h := k.isLt; omega) := by
  simp [fftSplit]

/-- **The FFT of depth zero returns its input.** Let $R$ be a commutative ring. For every
$\omega \in R$ and every vector $x \in R^{2^0}$, the vector returned by the radix-two FFT of
depth $0$ with root $\omega$ on $x$ is $x$ itself. -/
theorem fft_ret_zero (omega : R) (xs : Vector R (2 ^ 0)) :
    (fft 0 omega xs).ret = xs := rfl

private theorem fft_ret_succ (d : Nat) (omega : R) (xs : Vector R (2 ^ (d + 1))) :
    (fft (d + 1) omega xs).ret =
      (fftButterflies omega
        (fft d (omega * omega) (fftSplit xs).ret.1).ret
        (fft d (omega * omega) (fftSplit xs).ret.2).ret
        (Vector.replicate (2 ^ d * 2) 0)).ret.2 := rfl

/-- **Low half of the FFT butterfly recurrence.** Let $R$ be a commutative ring, $d$ a natural
number, $\omega \in R$ and $x \in R^{2^{d+1}}$, with entries indexed from $0$. Let
$e, o \in R^{2^d}$ be the even- and odd-indexed subsequences of $x$ returned by the FFT split,
and let $E$ and $O$ be the vectors returned by the radix-two FFT of depth $d$ with root
$\omega \cdot \omega$ on $e$ and on $o$. Then for every $k < 2^d$, entry $k$ of the vector
returned by the radix-two FFT of depth $d + 1$ with root $\omega$ on $x$ equals
$E_k + \omega^k O_k$. -/
theorem fft_ret_succ_low (d : Nat) (omega : R) (xs : Vector R (2 ^ (d + 1)))
    (k : Fin (2 ^ d)) :
    (fft (d + 1) omega xs).ret[k.val]'(by have h := k.isLt; simp only [pow_succ]; omega) =
      (fft d (omega * omega) (fftSplit xs).ret.1).ret[k.val] +
        omega ^ k.val * (fft d (omega * omega) (fftSplit xs).ret.2).ret[k.val] := by
  rw [fft_ret_succ]
  exact ((fftButterflies_ret omega _ _ _).2 k).1

/-- **High half of the FFT butterfly recurrence.** Let $R$ be a commutative ring, $d$ a natural
number, $\omega \in R$ and $x \in R^{2^{d+1}}$, with entries indexed from $0$. Let
$e, o \in R^{2^d}$ be the even- and odd-indexed subsequences of $x$ returned by the FFT split,
and let $E$ and $O$ be the vectors returned by the radix-two FFT of depth $d$ with root
$\omega \cdot \omega$ on $e$ and on $o$. Then for every $k < 2^d$, entry $k + 2^d$ of the
vector returned by the radix-two FFT of depth $d + 1$ with root $\omega$ on $x$ equals
$E_k - \omega^k O_k$. -/
theorem fft_ret_succ_high (d : Nat) (omega : R) (xs : Vector R (2 ^ (d + 1)))
    (k : Fin (2 ^ d)) :
    (fft (d + 1) omega xs).ret[k.val + 2 ^ d]'
        (by have h := k.isLt; simp only [pow_succ]; omega) =
      (fft d (omega * omega) (fftSplit xs).ret.1).ret[k.val] -
        omega ^ k.val * (fft d (omega * omega) (fftSplit xs).ret.2).ret[k.val] := by
  rw [fft_ret_succ]
  exact ((fftButterflies_ret omega _ _ _).2 k).2

end Cslib.Algorithms.Lean.TimeM
