/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.CanonicalDFT
public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCorrectness

/-!
# Canonical inverse coefficients and the negative-sign source round trips

The actual inverse conjugates the source root. At the negative principal root
its returned coefficients are canonical inverse DFT; at the positive root
they are the explicitly normalized canonical forward DFT. The two negative
source round trips reuse the canonical linear equivalence on actual samples.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open MathlibExt.Analysis.Fourier.FastFourierTransformWanted

/-- Actual negative-sign source inverse coefficients equal canonical inverse DFT. -/
theorem ifft_stdAddChar_neg_one (d : Nat) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (ifft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret[k.val] =
      ZMod.dft.symm (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0)
        (k.val : ZMod (2 ^ d)) := by
  have hstar : star (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) =
      ZMod.stdAddChar (1 : ZMod (2 ^ d)) := by
    simpa only [starRingAut_apply, neg_neg] using
      ZMod.conj_stdAddChar (-1 : ZMod (2 ^ d))
  rw [ifft_correct d _ isPrimitiveRoot_stdAddChar_neg_one xs k, hstar]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    invDFT_eq_dftSum_stdAddChar_vector xs k.val

/-- Actual positive-sign source inverse coefficients equal normalized forward DFT. -/
theorem ifft_stdAddChar_one (d : Nat) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (ifft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret[k.val] =
      (2 ^ d : ℂ)⁻¹ * ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0)
        (k.val : ZMod (2 ^ d)) := by
  have hstar : star (ZMod.stdAddChar (1 : ZMod (2 ^ d))) =
      ZMod.stdAddChar (-1 : ZMod (2 ^ d)) := by
    simpa only [starRingAut_apply] using ZMod.conj_stdAddChar (1 : ZMod (2 ^ d))
  rw [ifft_correct d _ isPrimitiveRoot_stdAddChar_one xs k, hstar,
    dftSum_stdAddChar_neg_vector]

private theorem fft_neg_samples (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (fun j : ZMod (2 ^ d) =>
      (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0) =
      ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) := by
  funext j
  have h := fft_stdAddChar_neg_one d xs ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.natCast_zmod_val] at h
  exact (Array.getElem_eq_getD (h := by simpa using ZMod.val_lt j) 0).symm.trans h

private theorem ifft_neg_samples (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (fun j : ZMod (2 ^ d) =>
      (ifft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0) =
      ZMod.dft.symm (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) := by
  funext j
  have h := ifft_stdAddChar_neg_one d xs ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.natCast_zmod_val] at h
  exact (Array.getElem_eq_getD (h := by simpa using ZMod.val_lt j) 0).symm.trans h

/-- Execute the actual negative forward and inverse procedures on every admitted vector. -/
theorem ifft_fft_stdAddChar_neg_one (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (ifft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d)))
      (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret).ret = xs := by
  apply Vector.ext
  intro k hk
  rw [ifft_stdAddChar_neg_one d _ ⟨k, hk⟩, fft_neg_samples,
    LinearEquiv.symm_apply_apply, ZMod.val_natCast_of_lt hk]
  exact (Array.getElem_eq_getD (h := by simpa using hk) 0).symm

/-- Execute the actual negative inverse and forward procedures on every admitted vector. -/
theorem fft_ifft_stdAddChar_neg_one (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d)))
      (ifft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret).ret = xs := by
  apply Vector.ext
  intro k hk
  rw [fft_stdAddChar_neg_one d _ ⟨k, hk⟩, ifft_neg_samples,
    LinearEquiv.apply_symm_apply, ZMod.val_natCast_of_lt hk]
  exact (Array.getElem_eq_getD (h := by simpa using hk) 0).symm

end Cslib.Algorithms.Lean.TimeM
