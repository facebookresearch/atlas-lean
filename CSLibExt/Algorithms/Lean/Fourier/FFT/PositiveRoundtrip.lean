/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCanonicalDFT

/-!
# Both actual round trips for the positive MIT/CLRS source sign

The actual positive forward is the unnormalized canonical inverse. Its source
inverse is the normalized canonical forward. The proofs reuse the canonical
linear equivalence, preserving the explicitly executed nonzero normalization.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private theorem fft_pos_normalized_samples (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (fun j : ZMod (2 ^ d) => (2 ^ d : ℂ)⁻¹ *
      (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0) =
      ZMod.dft.symm (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) := by
  funext j
  have h := fft_stdAddChar_one_normalized d xs ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.natCast_zmod_val] at h
  rw [← Array.getElem_eq_getD (h := by simpa using ZMod.val_lt j) 0]
  exact h

private theorem ifft_pos_samples (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (fun j : ZMod (2 ^ d) =>
      (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0) =
      (fun j : ZMod (2 ^ d) => (2 ^ d : ℂ)⁻¹ *
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j) := by
  funext j
  have h := ifft_stdAddChar_one d xs ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.natCast_zmod_val] at h
  exact (Array.getElem_eq_getD (h := by simpa using ZMod.val_lt j) 0).symm.trans h

/-- Execute positive-sign forward and source inverse on every admitted vector. -/
theorem ifft_fft_stdAddChar_one (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d)))
      (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret).ret = xs := by
  apply Vector.ext
  intro k hk
  rw [ifft_stdAddChar_one d _ ⟨k, hk⟩]
  rw [← congr_fun (ZMod.dft_const_mul (2 ^ d : ℂ)⁻¹
    (fun j : ZMod (2 ^ d) =>
      (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0))
    (k : ZMod (2 ^ d))]
  rw [fft_pos_normalized_samples, LinearEquiv.apply_symm_apply,
    ZMod.val_natCast_of_lt hk]
  exact (Array.getElem_eq_getD (h := by simpa using hk) 0).symm

/-- Execute positive-sign source inverse and forward on every admitted vector. -/
theorem fft_ifft_stdAddChar_one (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d)))
      (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret).ret = xs := by
  apply Vector.ext
  intro k hk
  have h := fft_stdAddChar_one_normalized d
    (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret ⟨k, hk⟩
  rw [ifft_pos_samples] at h
  change (2 ^ d : ℂ)⁻¹ *
      (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d)))
        (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret).ret[k] =
      ZMod.dft.symm ((2 ^ d : ℂ)⁻¹ •
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0))
        (k : ZMod (2 ^ d)) at h
  rw [LinearEquiv.map_smul, LinearEquiv.symm_apply_apply] at h
  change (2 ^ d : ℂ)⁻¹ *
      (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d)))
        (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret).ret[k] =
      (2 ^ d : ℂ)⁻¹ * xs.toArray.getD (k : ZMod (2 ^ d)).val 0 at h
  rw [ZMod.val_natCast_of_lt hk] at h
  have hscale : (2 ^ d : ℂ)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by norm_num))
  exact (mul_left_cancel₀ hscale h).trans
    (Array.getElem_eq_getD (h := by simpa using hk) 0).symm

end Cslib.Algorithms.Lean.TimeM
