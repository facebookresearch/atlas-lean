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
/-- The actual split reads and writes each even/odd pair. -/
@[simp] theorem fftSplit_time {m : Nat} (xs : Vector R (m * 2)) :
    (fftSplit xs).time = 4 * m := by
  simp [fftSplit]

/-- The actual butterfly charges its two reads, four scalar operations and two writes. -/
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

/-- Combining the stored child vectors performs exactly one butterfly per half-index. -/
theorem fftButterflies_time {m : Nat} (omega : R) (q r : Vector R m)
    (out : Vector R (m * 2)) :
    (fftButterflies omega q r out).time = 8 * m := by
  simpa only [fftButterflies, List.length_finRange] using
    fftButterflies_fold_time omega q r (List.finRange m) (1, out)

/-- The actual recursive run has cost `(7*d + 1)*2^d - 1`, including charged split/output writes. -/
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

/-- The exact actual-run count expressed in terms of its input size and binary logarithm. -/
theorem fft_time_add_one_log2 (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fft d omega xs).time + 1 = (7 * Nat.log2 (2 ^ d) + 1) * 2 ^ d := by
  simpa only [Nat.log2_two_pow] using fft_time_add_one d omega xs

/-- The actual FFT performs at most eight charged operations per entry per recursion level. -/
theorem fft_time_le (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fft d omega xs).time ≤ 8 * (2 ^ d) * d := by
  by_cases hd : d = 0
  · subst d
    simp [fft]
  · have hd1 : 1 ≤ d := by omega
    have hmul := Nat.mul_le_mul_right (2 ^ d) hd1
    nlinarith [fft_time_add_one d omega xs, hmul]

end Cslib.Algorithms.Lean.TimeM
