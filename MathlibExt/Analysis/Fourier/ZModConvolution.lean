/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section

open scoped BigOperators

namespace ZMod
variable {n : ℕ} [NeZero n]

private noncomputable def toAlgebra (f : ZMod n → ℂ) : AddMonoidAlgebra ℂ (ZMod n) :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm f)

private theorem toAlgebra_coeff (f : ZMod n → ℂ) (j : ZMod n) :
    (toAlgebra f).coeff j = f j := by
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply f) j

private theorem toAlgebra_mul_coeff (f g : ZMod n → ℂ) (t : ZMod n) :
    (toAlgebra f * toAlgebra g).coeff t =
      ∑ j : ZMod n, f j * g (t - j) := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
  simp only [toAlgebra_coeff, sub_eq_add_neg, add_comm]

private theorem lift_coeff_dft (a : AddMonoidAlgebra ℂ (ZMod n)) (k : ZMod n) :
    AddMonoidAlgebra.lift ℂ ℂ (ZMod n) ((stdAddChar.mulShift (-k)).toMonoidHom) a =
      dft a.coeff k := by
  classical
  rw [AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum_fintype _ _ (by intro j; simp), dft_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [AddChar.toMonoidHom_apply, AddChar.mulShift_apply, smul_eq_mul]
  change a.coeff j * stdAddChar ((-k) * j) = stdAddChar (-(j * k)) * a.coeff j
  rw [neg_mul, mul_comm k j, mul_comm]

/-- The normalized inverse DFT turns pointwise products into circular convolution.
Uses the canonical additive monoid algebra product and its character lift.
Source: MIT 6.046J Spring 2015 Lecture 3, polynomial product theorem, cyclic form. -/
theorem invDFT_mul_dft (f g : ZMod n → ℂ) (t : ZMod n) :
    dft.symm (fun k => dft f k * dft g k) t = ∑ j : ZMod n, f j * g (t - j) := by
  have hf : ((toAlgebra f).coeff : ZMod n → ℂ) = f :=
    funext (toAlgebra_coeff f)
  have hg : ((toAlgebra g).coeff : ZMod n → ℂ) = g :=
    funext (toAlgebra_coeff g)
  have hproduct : dft ((toAlgebra f * toAlgebra g).coeff) =
      (fun k => dft f k * dft g k) := by
    funext k
    rw [← lift_coeff_dft (toAlgebra f * toAlgebra g) k, map_mul,
      lift_coeff_dft, lift_coeff_dft, hf, hg]
  rw [← hproduct, LinearEquiv.symm_apply_apply]
  exact toAlgebra_mul_coeff f g t

end ZMod
