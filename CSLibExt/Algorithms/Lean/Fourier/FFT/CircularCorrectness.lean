/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCharacteristic
public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCanonicalDFT
public import MathlibExt.Analysis.Fourier.ZModConvolution

/-!
# Coefficients of the actual circular convolution for both source signs

The proof follows the two stored forward arrays, their materialized pointwise
product and the actual source inverse. Canonical finite convolution supplies
the coefficient identity after these execution results have been identified.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- The executed return uses precisely the two stored transforms and their stored product. -/
theorem fftCircular_ret {R : Type u} [Field R] [StarRing R] (d : Nat)
    (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircular d omega xs ys).ret =
      (ifft d omega (fftPointwise (fft d omega xs).ret (fft d omega ys).ret).ret).ret := by
  rfl

/-- The executed linear return calls circular convolution on both actual padded arrays. -/
theorem fftLinear_ret {R : Type u} [Field R] [StarRing R] (d : Nat)
    (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinear d omega xs ys).ret =
      (fftCircular (d + 1) omega (fftPad d xs).ret (fftPad d ys).ret).ret := by
  exact (ret_bind (fftPad d xs) (fun left =>
    fftPad d ys >>= fun right => fftCircular (d + 1) omega left right)).trans
    (ret_bind (fftPad d ys)
      (fun right => fftCircular (d + 1) omega (fftPad d xs).ret right))

private theorem fftPointwise_getD {n : Nat} [NeZero n] (xs ys : Vector ℂ n)
    (j : ZMod n) :
    (fftPointwise xs ys).ret.toArray.getD j.val 0 =
      xs.toArray.getD j.val 0 * ys.toArray.getD j.val 0 := by
  have hj : j.val < n := ZMod.val_lt j
  calc
    (fftPointwise xs ys).ret.toArray.getD j.val 0 = (fftPointwise xs ys).ret[j.val] :=
      (Array.getElem_eq_getD (h := by simpa using hj) 0).symm
    _ = xs[j.val] * ys[j.val] := fftPointwise_ret xs ys ⟨j.val, hj⟩
    _ = xs.toArray.getD j.val 0 * ys.toArray.getD j.val 0 := by
      congr 1 <;> exact Array.getElem_eq_getD (h := by simpa using hj) 0

private theorem fft_negative_getD (d : Nat) (xs : Vector ℂ (2 ^ d))
    (j : ZMod (2 ^ d)) :
    (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0 =
      ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j := by
  have h := fft_stdAddChar_neg_one d xs ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.natCast_zmod_val] at h
  exact (Array.getElem_eq_getD (h := by simpa using ZMod.val_lt j) 0).symm.trans h

private theorem fft_positive_getD (d : Nat) (xs : Vector ℂ (2 ^ d))
    (j : ZMod (2 ^ d)) :
    (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret.toArray.getD j.val 0 =
      ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) (-j) := by
  have hj : j.val < 2 ^ d := ZMod.val_lt j
  have h := fft_stdAddChar_one_normalized d xs ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.natCast_zmod_val, ZMod.invDFT_apply'] at h
  have h' : (2 ^ d : ℂ)⁻¹ *
      (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret[j.val] =
      (2 ^ d : ℂ)⁻¹ * ZMod.dft
        (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) (-j) := by
    simpa only [smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hscale : (2 ^ d : ℂ)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by norm_num))
  exact (Array.getElem_eq_getD (h := by simpa using ZMod.val_lt j) 0).symm.trans
    (mul_left_cancel₀ hscale h')

private theorem fftProduct_neg_samples (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fun j : ZMod (2 ^ d) =>
      (fftPointwise (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs).ret
        (fft d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) ys).ret).ret.toArray.getD j.val 0) =
      (fun j : ZMod (2 ^ d) =>
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j *
        ZMod.dft (fun j : ZMod (2 ^ d) => ys.toArray.getD j.val 0) j) := by
  funext j
  rw [fftPointwise_getD, fft_negative_getD, fft_negative_getD]

private theorem fftProduct_pos_samples (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fun j : ZMod (2 ^ d) =>
      (fftPointwise (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs).ret
        (fft d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) ys).ret).ret.toArray.getD j.val 0) =
      (fun j : ZMod (2 ^ d) =>
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) (-j) *
        ZMod.dft (fun j : ZMod (2 ^ d) => ys.toArray.getD j.val 0) (-j)) := by
  funext j
  rw [fftPointwise_getD, fft_positive_getD, fft_positive_getD]

/-- Every actual Princeton-sign circular output is its cyclic convolution coefficient. -/
theorem fftCircular_stdAddChar_neg_one (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (fftCircular d (ZMod.stdAddChar (-1 : ZMod (2 ^ d))) xs ys).ret[k.val] =
      ∑ j : ZMod (2 ^ d), xs.toArray.getD j.val 0 *
        ys.toArray.getD ((k.val : ZMod (2 ^ d)) - j).val 0 := by
  rw [fftCircular_ret, ifft_stdAddChar_neg_one d _ k, fftProduct_neg_samples]
  exact ZMod.invDFT_mul_dft _ _ _

/-- Every actual MIT/CLRS-sign circular output is its cyclic convolution coefficient. -/
theorem fftCircular_stdAddChar_one (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (fftCircular d (ZMod.stdAddChar (1 : ZMod (2 ^ d))) xs ys).ret[k.val] =
      ∑ j : ZMod (2 ^ d), xs.toArray.getD j.val 0 *
        ys.toArray.getD ((k.val : ZMod (2 ^ d)) - j).val 0 := by
  rw [fftCircular_ret, ifft_stdAddChar_one d _ k, fftProduct_pos_samples]
  rw [ZMod.dft_comp_neg (fun j : ZMod (2 ^ d) =>
    ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j *
    ZMod.dft (fun j : ZMod (2 ^ d) => ys.toArray.getD j.val 0) j)]
  have hinv : (2 ^ d : ℂ)⁻¹ * ZMod.dft
      (fun j : ZMod (2 ^ d) =>
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j *
        ZMod.dft (fun j : ZMod (2 ^ d) => ys.toArray.getD j.val 0) j)
      (-(k.val : ZMod (2 ^ d))) =
      ZMod.dft.symm (fun j : ZMod (2 ^ d) =>
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j *
        ZMod.dft (fun j : ZMod (2 ^ d) => ys.toArray.getD j.val 0) j)
        (k.val : ZMod (2 ^ d)) := by
    simpa only [smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.invDFT_apply' (fun j : ZMod (2 ^ d) =>
        ZMod.dft (fun j : ZMod (2 ^ d) => xs.toArray.getD j.val 0) j *
        ZMod.dft (fun j : ZMod (2 ^ d) => ys.toArray.getD j.val 0) j)
        (k.val : ZMod (2 ^ d))).symm
  rw [hinv]
  exact ZMod.invDFT_mul_dft _ _ _

end Cslib.Algorithms.Lean.TimeM
