/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.CircularCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.PaddingCircular

/-!
# The actual FFT linear result is the complete polynomial product

Both source signs execute the same two materialized zero pads followed by
circular convolution at twice the input length. Every returned coefficient
is the canonical polynomial product coefficient, including the zero final
slot. The represented polynomial equality also checks all higher coefficients.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- **FFT linear convolution gives the product coefficients (Princeton sign).** Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{-2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
write $P_x = \sum_{j < 2^d} x_j X^j$ and $P_y = \sum_{j < 2^d} y_j X^j$, and let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then for
every $k < N$, the entry $z_k$ is the coefficient of $X^k$ in $P_x P_y$. -/
theorem fftLinear_stdAddChar_neg_one_coeff (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      (fftPolynomial xs * fftPolynomial ys).coeff k.val := by
  rw [fftLinear_ret, fftCircular_stdAddChar_neg_one]
  exact fftPad_circular_coeff_eq_polynomial d xs ys k

/-- **FFT linear convolution computes the convolution sums (Princeton sign).** Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{-2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
extended by $x_j = y_j = 0$ for $j \ge 2^d$, let $z \in \mathbb{C}^N$ be the output of the FFT
linear convolution of $x$ and $y$ with root $\omega$, which pads both vectors with zeros to length
$N$ and convolves them circularly by FFT. Then for every $k < N$,
$$z_k = \sum_{j=0}^{k} x_j \, y_{k-j}.$$
-/
theorem fftLinear_stdAddChar_neg_one_sum (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      ∑ j ∈ Finset.range (k.val + 1),
        xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 := by
  rw [fftLinear_stdAddChar_neg_one_coeff, fftPolynomial_mul_coeff]

/-- **FFT linear convolution returns the product polynomial (Princeton sign).** Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{-2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
write $P_x = \sum_{j < 2^d} x_j X^j$ and $P_y = \sum_{j < 2^d} y_j X^j$, and let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then
$\sum_{k < N} z_k X^k = P_x P_y$ as polynomials over $\mathbb{C}$. -/
theorem fftPolynomial_fftLinear_stdAddChar_neg_one (d : Nat)
    (xs ys : Vector ℂ (2 ^ d)) :
    fftPolynomial (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret =
      fftPolynomial xs * fftPolynomial ys := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 ^ (d + 1)
  · rw [fftPolynomial_coeff]
    rw [← Array.getElem_eq_getD (h := by simpa using hk) 0]
    exact fftLinear_stdAddChar_neg_one_coeff d xs ys ⟨k, hk⟩
  · have hp : 2 * 2 ^ d ≤ k := by
      simpa only [pow_succ, Nat.mul_comm (2 ^ d) 2] using Nat.le_of_not_gt hk
    have hout :
        (fftPolynomial (fftLinear d
          (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret).coeff k = 0 := by
      unfold fftPolynomial
      exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)
    rw [hout, fftPolynomial_mul_coeff_eq_zero_of_two_mul_le xs ys k hp]

/-- **The last entry of FFT linear convolution is zero (Princeton sign).** Let $d$ be a natural
number, $N = 2^{d+1}$ and $\omega = e^{-2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$, let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then the
last entry $z_{N-1}$ is $0$. -/
theorem fftLinear_stdAddChar_neg_one_last (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret.toArray.getD
      (2 * 2 ^ d - 1) 0 = 0 := by
  have hn : 0 < 2 ^ d := pow_pos (by decide) d
  have hslot : 2 * 2 ^ d - 1 < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  rw [← Array.getElem_eq_getD (h := by simpa using hslot) 0]
  exact (fftLinear_stdAddChar_neg_one_coeff d xs ys
    ⟨2 * 2 ^ d - 1, hslot⟩).trans (fftPolynomial_mul_last d xs ys)

/-- **FFT linear convolution gives the product coefficients (MIT/CLRS sign).** Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
write $P_x = \sum_{j < 2^d} x_j X^j$ and $P_y = \sum_{j < 2^d} y_j X^j$, and let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then for
every $k < N$, the entry $z_k$ is the coefficient of $X^k$ in $P_x P_y$. -/
theorem fftLinear_stdAddChar_one_coeff (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      (fftPolynomial xs * fftPolynomial ys).coeff k.val := by
  rw [fftLinear_ret, fftCircular_stdAddChar_one]
  exact fftPad_circular_coeff_eq_polynomial d xs ys k

/-- **FFT linear convolution computes the convolution sums (MIT/CLRS sign).** Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
extended by $x_j = y_j = 0$ for $j \ge 2^d$, let $z \in \mathbb{C}^N$ be the output of the FFT
linear convolution of $x$ and $y$ with root $\omega$, which pads both vectors with zeros to length
$N$ and convolves them circularly by FFT. Then for every $k < N$,
$$z_k = \sum_{j=0}^{k} x_j \, y_{k-j}.$$
-/
theorem fftLinear_stdAddChar_one_sum (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      ∑ j ∈ Finset.range (k.val + 1),
        xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 := by
  rw [fftLinear_stdAddChar_one_coeff, fftPolynomial_mul_coeff]

/-- **FFT linear convolution returns the product polynomial (MIT/CLRS sign).** Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
write $P_x = \sum_{j < 2^d} x_j X^j$ and $P_y = \sum_{j < 2^d} y_j X^j$, and let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then
$\sum_{k < N} z_k X^k = P_x P_y$ as polynomials over $\mathbb{C}$. -/
theorem fftPolynomial_fftLinear_stdAddChar_one (d : Nat)
    (xs ys : Vector ℂ (2 ^ d)) :
    fftPolynomial (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret =
      fftPolynomial xs * fftPolynomial ys := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 ^ (d + 1)
  · rw [fftPolynomial_coeff]
    rw [← Array.getElem_eq_getD (h := by simpa using hk) 0]
    exact fftLinear_stdAddChar_one_coeff d xs ys ⟨k, hk⟩
  · have hp : 2 * 2 ^ d ≤ k := by
      simpa only [pow_succ, Nat.mul_comm (2 ^ d) 2] using Nat.le_of_not_gt hk
    have hout :
        (fftPolynomial (fftLinear d
          (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret).coeff k = 0 := by
      unfold fftPolynomial
      exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)
    rw [hout, fftPolynomial_mul_coeff_eq_zero_of_two_mul_le xs ys k hp]

/-- **The last entry of FFT linear convolution is zero (MIT/CLRS sign).** Let $d$ be a natural
number, $N = 2^{d+1}$ and $\omega = e^{2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$, let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then the
last entry $z_{N-1}$ is $0$. -/
theorem fftLinear_stdAddChar_one_last (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret.toArray.getD
      (2 * 2 ^ d - 1) 0 = 0 := by
  have hn : 0 < 2 ^ d := pow_pos (by decide) d
  have hslot : 2 * 2 ^ d - 1 < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  rw [← Array.getElem_eq_getD (h := by simpa using hslot) 0]
  exact (fftLinear_stdAddChar_one_coeff d xs ys
    ⟨2 * 2 ^ d - 1, hslot⟩).trans (fftPolynomial_mul_last d xs ys)

end Cslib.Algorithms.Lean.TimeM
