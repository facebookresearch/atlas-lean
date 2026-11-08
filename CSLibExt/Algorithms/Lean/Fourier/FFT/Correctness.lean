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
/-- The materialized even subsequence preserves the ordered even input entries. -/
theorem fftSplit_ret_even {m : Nat} (xs : Vector R (m * 2)) (k : Fin m) :
    (fftSplit xs).ret.1[k.val] = xs[2 * k.val]'(by have h := k.isLt; omega) := by
  simp [fftSplit]

omit [CommRing R] in
/-- The materialized odd subsequence preserves the ordered odd input entries. -/
theorem fftSplit_ret_odd {m : Nat} (xs : Vector R (m * 2)) (k : Fin m) :
    (fftSplit xs).ret.2[k.val] = xs[2 * k.val + 1]'(by have h := k.isLt; omega) := by
  simp [fftSplit]

/-- The length-one actual call returns its input vector. -/
theorem fft_ret_zero (omega : R) (xs : Vector R (2 ^ 0)) :
    (fft 0 omega xs).ret = xs := rfl

private theorem fft_ret_succ (d : Nat) (omega : R) (xs : Vector R (2 ^ (d + 1))) :
    (fft (d + 1) omega xs).ret =
      (fftButterflies omega
        (fft d (omega * omega) (fftSplit xs).ret.1).ret
        (fft d (omega * omega) (fftSplit xs).ret.2).ret
        (Vector.replicate (2 ^ d * 2) 0)).ret.2 := rfl

/-- Each low-half output uses the two stored actual child transforms. -/
theorem fft_ret_succ_low (d : Nat) (omega : R) (xs : Vector R (2 ^ (d + 1)))
    (k : Fin (2 ^ d)) :
    (fft (d + 1) omega xs).ret[k.val]'(by have h := k.isLt; simp only [pow_succ]; omega) =
      (fft d (omega * omega) (fftSplit xs).ret.1).ret[k.val] +
        omega ^ k.val * (fft d (omega * omega) (fftSplit xs).ret.2).ret[k.val] := by
  rw [fft_ret_succ]
  exact ((fftButterflies_ret omega _ _ _).2 k).1

/-- Each high-half output uses the two stored actual child transforms. -/
theorem fft_ret_succ_high (d : Nat) (omega : R) (xs : Vector R (2 ^ (d + 1)))
    (k : Fin (2 ^ d)) :
    (fft (d + 1) omega xs).ret[k.val + 2 ^ d]'
        (by have h := k.isLt; simp only [pow_succ]; omega) =
      (fft d (omega * omega) (fftSplit xs).ret.1).ret[k.val] -
        omega ^ k.val * (fft d (omega * omega) (fftSplit xs).ret.2).ret[k.val] := by
  rw [fft_ret_succ]
  exact ((fftButterflies_ret omega _ _ _).2 k).2

end Cslib.Algorithms.Lean.TimeM
