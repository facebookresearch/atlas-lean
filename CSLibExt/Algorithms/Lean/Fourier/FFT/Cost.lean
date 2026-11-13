/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # Operation counts of the actual array FFT executor -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {R : Type u} [CommRing R]

omit [CommRing R] in
/-- **Cost of the FFT even/odd split.** For every natural number $m$ and every vector $x$ of length
$2m$, splitting $x$ into its even-indexed and its odd-indexed subsequences costs exactly $4m$
charged operations: two reads and two writes for each of the $m$ even/odd pairs. -/
@[simp] theorem fftSplit_time {m : Nat} (xs : Vector R (m * 2)) :
    (fftSplit xs).time = 4 * m := by
  simp [fftSplit]

/-- **Cost of one FFT butterfly.** Let $R$ be a commutative ring and $m$ a natural number. For every
$\omega \in R$, all vectors $q, r \in R^m$, every current twiddle $w \in R$ and output vector of
length $2m$ over $R$, and every index $k < m$, one butterfly step costs exactly $8$ charged
operations: two reads, four scalar operations and two writes. -/
@[simp] theorem fftButterfly_time {m : Nat} (omega : R) (q r : Vector R m)
    (state : R × Vector R (m * 2)) (k : Fin m) :
    (fftButterfly omega q r state k).time = 8 := by
  rcases state with ⟨w, out⟩
  simp [fftButterfly]

private theorem fftButterflies_fold_time {m : Nat} (omega : R) (q r : Vector R m)
    (indices : List (Fin m)) (state : R × Vector R (m * 2)) :
    (indices.foldlM (fftButterfly omega q r) state).time = 8 * indices.length := by
  induction indices generalizing state with
  | nil => simp
  | cons k indices ih =>
      simp only [List.foldlM_cons, time_bind, fftButterfly_time, ih, List.length_cons]
      omega

/-- **Cost of the FFT butterfly pass.** Let $R$ be a commutative ring and $m$ a natural number. For
every $\omega \in R$, all vectors $q, r \in R^m$ and every output vector of length $2m$ over $R$,
the pass that, starting from twiddle $1$, applies one butterfly for each index $k < m$ in
increasing order costs exactly $8m$ charged operations. -/
theorem fftButterflies_time {m : Nat} (omega : R) (q r : Vector R m)
    (out : Vector R (m * 2)) :
    (fftButterflies omega q r out).time = 8 * m := by
  simpa only [fftButterflies, List.length_finRange] using
    fftButterflies_fold_time omega q r (List.finRange m) (1, out)

/-- **Exact cost of the radix-two FFT.** Let $R$ be a commutative ring. For every natural number
$d$, every $\omega \in R$ and every vector $x \in R^{2^d}$, the radix-two FFT of $x$ with root
$\omega$ costs $T$ charged operations, where $T + 1 = (7d + 1) \cdot 2^d$; that is,
$T = (7d + 1) \cdot 2^d - 1$.

The count includes the charged reads and writes of the even/odd splits and the writes that
initialize each output vector. -/
theorem fft_time_add_one (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fft d omega xs).time + 1 = (7 * d + 1) * 2 ^ d := by
  induction d generalizing omega with
  | zero => simp [fft]
  | succ d ih =>
      have hq := ih (omega * omega) (fftSplit xs).ret.1
      have hr := ih (omega * omega) (fftSplit xs).ret.2
      have hs := fftSplit_time (m := 2 ^ d) xs
      simp only [fft, time_bind, time_pure, fftButterflies_time,
        Nat.pow_succ]
      rw [hs]
      nlinarith [hq, hr]

/-- **Exact cost of the radix-two FFT in terms of the input length.** Let $R$ be a commutative
ring. For every natural number $d$, every $\omega \in R$ and every vector $x$ over $R$ of length
$n = 2^d$, the radix-two FFT of $x$ with root $\omega$ costs $T$ charged operations, where
$T + 1 = (7 \log_2 n + 1) \cdot n$. -/
theorem fft_time_add_one_log2 (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fft d omega xs).time + 1 = (7 * Nat.log2 (2 ^ d) + 1) * 2 ^ d := by
  simpa only [Nat.log2_two_pow] using fft_time_add_one d omega xs

/-- **Cost bound for the radix-two FFT.** Let $R$ be a commutative ring. For every natural number
$d$, every $\omega \in R$ and every vector $x \in R^{2^d}$, the radix-two FFT of $x$ with root
$\omega$ costs at most $8 \cdot 2^d \cdot d$ charged operations, that is, at most eight per entry
per recursion level. -/
theorem fft_time_le (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fft d omega xs).time ≤ 8 * (2 ^ d) * d := by
  by_cases hd : d = 0
  · subst d
    simp [fft]
  · have hd1 : 1 ≤ d := by omega
    have hmul := Nat.mul_le_mul_right (2 ^ d) hd1
    nlinarith [fft_time_add_one d omega xs, hmul]

end Cslib.Algorithms.Lean.TimeM
