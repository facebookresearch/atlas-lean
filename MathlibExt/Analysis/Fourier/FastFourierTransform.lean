/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.Fourier.FastFourierTransformWanted

/-!
# Fast Fourier transform

The radix-2 Cooley–Tukey splitting identity (correctness core of the FFT) and
the operation-count recurrence with its `n log n` closed form (complexity
skeleton).

Sources: `undergrad.yaml`, section "Fourier transform", entry "fast Fourier
transform" (empty); J. W. Cooley and J. W. Tukey, An algorithm for the machine
calculation of complex Fourier series, Math. Comp. 19 (1965), 297–301.
-/

/-- **Discrete Fourier sum.** For a natural number $N$, a complex number $\omega$, a sequence
$f : \mathbb{N} \to \mathbb{C}$ and a natural number $k$, the unnormalized discrete Fourier sum of
length $N$ at frequency $k$ is $\sum_{j=0}^{N-1} \omega^{jk} f(j)$.

No condition is placed on $\omega$; the usual DFT takes $\omega = e^{-2\pi i/N}$. -/
def dftSum (N : ℕ) (ω : ℂ) (f : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, ω ^ (j * k) * f j

private theorem fft_sum_range_even_odd (g : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), g j =
      (∑ t ∈ Finset.range n, g (2 * t)) + ∑ t ∈ Finset.range n, g (2 * t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.mul_succ, Finset.sum_range_succ]
    rw [ih]
    ac_rfl

private theorem fft_pow_even (ω : ℂ) (t K : ℕ) :
    ω ^ ((2 * t) * K) = (ω ^ 2) ^ (t * K) := by
  rw [mul_assoc, pow_mul]

private theorem fft_pow_odd (ω : ℂ) (t K : ℕ) :
    ω ^ ((2 * t + 1) * K) = ω ^ K * (ω ^ 2) ^ (t * K) := by
  rw [add_mul, one_mul, mul_assoc, add_comm, pow_add, pow_mul]

/-- **Even–odd splitting of the DFT sum.** For every natural number $n$, every
$\omega \in \mathbb{C}$, every $f : \mathbb{N} \to \mathbb{C}$ and every natural number $K$,
$$\sum_{j < 2n} \omega^{jK} f(j) = \sum_{t < n} (\omega^2)^{tK} f(2t)
  + \omega^K \sum_{t < n} (\omega^2)^{tK} f(2t + 1).$$ -/
public theorem dftSum_two_mul (n : ℕ) (ω : ℂ) (f : ℕ → ℂ) (K : ℕ) :
    dftSum (2 * n) ω f K =
      dftSum n (ω ^ 2) (fun t => f (2 * t)) K +
        ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) K := by
  unfold dftSum
  rw [fft_sum_range_even_odd]
  simp_rw [fft_pow_even, fft_pow_odd]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

private theorem fft_pow_mul_mod (a : ℂ) (n t K : ℕ) (ha : a ^ n = 1) :
    a ^ (t * K) = a ^ (t * (K % n)) := by
  have hat : (a ^ t) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ha, one_pow]
  calc
    a ^ (t * K) = (a ^ t) ^ K := pow_mul a t K
    _ = (a ^ t) ^ (K % n) := pow_eq_pow_mod K hat
    _ = a ^ (t * (K % n)) := (pow_mul a t (K % n)).symm

/-- A DFT sum at an `n`th root of unity depends only on the frequency modulo `n`. -/
public theorem dftSum_mod (n : ℕ) (ω : ℂ) (hω : ω ^ n = 1) (f : ℕ → ℂ) (K : ℕ) :
    dftSum n ω f K = dftSum n ω f (K % n) := by
  unfold dftSum
  apply Finset.sum_congr rfl
  intro t _
  rw [fft_pow_mul_mod ω n t K hω]

/--
**Radix-2 Cooley–Tukey splitting.** For $\omega \in \mathbb{C}$, $f : \mathbb{N} \to \mathbb{C}$
and natural numbers $N$ and $k$, write $D_N(\omega, f, k) = \sum_{j < N} \omega^{jk} f(j)$ for the
discrete Fourier sum. Let $n$ be a natural number and let $\omega \in \mathbb{C}$ satisfy
$\omega^{2n} = 1$. Then for every $f : \mathbb{N} \to \mathbb{C}$ and every natural number $K$,
$$D_{2n}(\omega, f, K) = D_n(\omega^2, f_0, K \bmod n)
  + \omega^K D_n(\omega^2, f_1, K \bmod n),$$
where $f_0(t) = f(2t)$, $f_1(t) = f(2t + 1)$, and $K \bmod n$ is the remainder of $K$ on division
by $n$ (with $K \bmod 0 = K$). So a length-$2n$ transform is two length-$n$ transforms on the
even and odd samples, combined with the twiddle factor $\omega^K$.

Proves `Wanted` entry `cooley_tukey`.

Proof: Split the range into even and odd indices, rewrite the powers, and use
root-of-unity periodicity to reduce the frequency modulo $n$, as in the
section "The radix-2 DIT case" of Wikipedia, "Cooley–Tukey FFT algorithm".

Sources: `undergrad.yaml`, section "Fourier transform", entry "fast Fourier
transform"; J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (decimation
in time).
-/
public theorem cooley_tukey (n : ℕ) (ω : ℂ) (hω : ω ^ (2 * n) = 1)
    (f : ℕ → ℂ) (K : ℕ) :
    dftSum (2 * n) ω f K =
      dftSum n (ω ^ 2) (fun t => f (2 * t)) (K % n) +
        ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) (K % n) := by
  have hω2 : (ω ^ 2) ^ n = 1 := by
    simpa only [pow_mul] using hω
  calc
    dftSum (2 * n) ω f K =
        dftSum n (ω ^ 2) (fun t => f (2 * t)) K +
          ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) K :=
      dftSum_two_mul n ω f K
    _ = dftSum n (ω ^ 2) (fun t => f (2 * t)) (K % n) +
        ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) (K % n) := by
      rw [dftSum_mod n (ω ^ 2) hω2 (fun t => f (2 * t)) K]
      rw [dftSum_mod n (ω ^ 2) hω2 (fun t => f (2 * t + 1)) K]

/-- **FFT operation count.** For a natural number $n$, the closed-form FFT operation count is
$n \lfloor \log_2 n \rfloor$, where $\lfloor \log_2 n \rfloor$ is the largest $m$ with $2^m \le n$
(taken to be $0$ when $n = 0$). -/
def fftCost (n : ℕ) : ℕ :=
  n * Nat.log 2 n

private theorem fft_log_two_mul (n : ℕ) (hn : 0 < n) :
    Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
  simpa only [Nat.mul_comm] using
    Nat.log_mul_base (b := 2) (n := n) (by decide) (Nat.ne_of_gt hn)

/--
**The FFT cost satisfies the radix-2 recurrence.** Let $C(n) = n \lfloor \log_2 n \rfloor$ be the
closed-form FFT operation count. For every natural number $n > 0$, $C(2n) = 2\,C(n) + 2n$.

Proves `Wanted` entry `fftCost_recurrence`.

Proof: Since $n > 0$, $\lfloor \log_2 (2n) \rfloor = \lfloor \log_2 n \rfloor + 1$; expand the
product.

Sources: `undergrad.yaml`, section "Fourier transform", entry "fast Fourier
transform"; J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (`n log n`
operation count).
-/
public theorem fftCost_recurrence (n : ℕ) (hn : 0 < n) :
    fftCost (2 * n) = 2 * fftCost n + 2 * n := by
  unfold fftCost
  rw [fft_log_two_mul n hn, mul_add, mul_one, mul_assoc]

end MathlibExt.Analysis.Fourier.FastFourierTransformWanted
