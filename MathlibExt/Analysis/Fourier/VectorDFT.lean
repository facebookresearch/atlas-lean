/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import MathlibExt.Analysis.Fourier.FastFourierTransform
public import Init.Data.Vector.Basic

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.Fourier.FastFourierTransformWanted

variable {n : ℕ} [NeZero n]

private theorem stdAddChar_neg_pow (j : ZMod n) (k : ℕ) :
    ZMod.stdAddChar (-1 : ZMod n) ^ (j.val * k) =
      ZMod.stdAddChar (-(j * (k : ZMod n))) := by
  rw [← AddChar.mulShift_spec', AddChar.mulShift_apply, Nat.cast_mul,
    ZMod.natCast_zmod_val, mul_neg_one]

theorem dftSum_stdAddChar_neg_vector (xs : Vector ℂ n) (k : ℕ) :
    dftSum n (ZMod.stdAddChar (-1 : ZMod n))
        (fun j => xs.toArray.getD j 0) k =
      ZMod.dft (fun j : ZMod n => xs.toArray.getD j.val 0) (k : ZMod n) := by
  unfold dftSum
  rw [← Fin.sum_univ_eq_sum_range, ZMod.dft_apply]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro j
  have hval : (ZMod.finEquiv n j).val = j.val := by
    cases n with
    | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
    | succ n => rfl
  rw [← hval, stdAddChar_neg_pow, smul_eq_mul]
  rfl

private theorem stdAddChar_pos_pow (j : ZMod n) (k : ℕ) :
    ZMod.stdAddChar (1 : ZMod n) ^ (j.val * k) =
      ZMod.stdAddChar (j * (k : ZMod n)) := by
  rw [← AddChar.mulShift_spec', AddChar.mulShift_apply, Nat.cast_mul,
    ZMod.natCast_zmod_val, mul_one]

theorem invDFT_eq_dftSum_stdAddChar_vector (xs : Vector ℂ n) (k : ℕ) :
    (n : ℂ)⁻¹ * dftSum n (ZMod.stdAddChar (1 : ZMod n))
        (fun j => xs.toArray.getD j 0) k =
      ZMod.dft.symm (fun j : ZMod n => xs.toArray.getD j.val 0) (k : ZMod n) := by
  rw [ZMod.invDFT_apply, smul_eq_mul]
  congr 1
  unfold dftSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro j
  have hval : (ZMod.finEquiv n j).val = j.val := by
    cases n with
    | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
    | succ n => rfl
  rw [← hval, stdAddChar_pos_pow, smul_eq_mul]
  rfl

theorem isPrimitiveRoot_stdAddChar_one :
    IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod n)) n := by
  have hroot : ZMod.stdAddChar (1 : ZMod n) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := by
    simpa using ZMod.stdAddChar_coe (N := n) (1 : ℤ)
  rw [hroot]
  exact Complex.isPrimitiveRoot_exp n (NeZero.ne n)

theorem isPrimitiveRoot_stdAddChar_neg_one :
    IsPrimitiveRoot (ZMod.stdAddChar (-1 : ZMod n)) n := by
  rw [AddChar.map_neg_eq_inv]
  exact isPrimitiveRoot_stdAddChar_one.inv

theorem stdAddChar_one_eq_exp :
    ZMod.stdAddChar (1 : ZMod n) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := by
  simpa using ZMod.stdAddChar_coe (N := n) (1 : ℤ)

theorem stdAddChar_neg_one_eq_exp :
    ZMod.stdAddChar (-1 : ZMod n) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) := by
  simpa only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_div] using
    ZMod.stdAddChar_coe (N := n) (-1 : ℤ)

end MathlibExt.Analysis.Fourier.FastFourierTransformWanted

namespace ZMod

theorem conj_stdAddChar {n : ℕ} [NeZero n] (j : ZMod n) :
    starRingAut (R := ℂ) (stdAddChar j) = stdAddChar (-j) := by
  rw [AddChar.map_neg_eq_inv]
  simp only [stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj (toCircle j)).symm.trans (Circle.coe_inv (toCircle j))

end ZMod
