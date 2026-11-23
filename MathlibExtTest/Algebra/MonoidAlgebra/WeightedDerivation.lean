/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.MonoidAlgebra.WeightedDerivation
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.ZMod.Basic

open AddMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommMonoid Γ]

example (w : Γ →+ R) (f : AddMonoidAlgebra R Γ) (g : Γ) :
    (weightedDerivation w f).coeff g = w g * f.coeff g := by
  simp

example (w : Γ →+ R) (g : Γ) (r : R) :
    weightedDerivation w (single g r) = single g (w g * r) := by
  simp

example (w : Γ →+ R) (f h : AddMonoidAlgebra R Γ) :
    weightedDerivation w (f + h) = weightedDerivation w f + weightedDerivation w h := by
  exact map_add (weightedDerivation w) f h

example (w : Γ →+ R) (r : R) (f : AddMonoidAlgebra R Γ) :
    weightedDerivation w (r • f) = r • weightedDerivation w f := by
  exact (weightedDerivation w).map_smul r f

example (w : Γ →+ R) (f h : AddMonoidAlgebra R Γ) :
    weightedDerivation w (f * h) =
      f * weightedDerivation w h + h * weightedDerivation w f := by
  exact (weightedDerivation w).leibniz f h

example (f : AddMonoidAlgebra R Γ) :
    weightedDerivation (0 : Γ →+ R) f = 0 := by
  simp

example (w : Γ →+ R) (r : R) :
    weightedDerivation w (single 0 r) = 0 := by
  simp

example (w : Γ →+ R) : weightedDerivation w 0 = 0 := by
  simp

example (w : Γ →+ R) : weightedDerivation w 1 = 0 := by
  simp

private noncomputable def sourceThI : LaurentPolynomial ℚ →+ LaurentPolynomial ℚ where
  toFun p := AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset p.coeff.support (fun x ↦ (x : ℚ) * p.coeff x) fun x h ↦ by
      rw [Finsupp.mem_support_iff]
      exact right_ne_zero_of_mul h)
  map_zero' := by ext x; simp
  map_add' p q := by ext x; simp [mul_add]

example (p : LaurentPolynomial ℚ) :
    sourceThI p = weightedDerivation (Int.castAddHom ℚ) p := by
  ext x
  simp [sourceThI]

private noncomputable def f : AddMonoidAlgebra ℤ ℤ := single (-2) 3 + single 1 (-4)

example : (weightedDerivation (Int.castAddHom ℤ) f).coeff (-2) = -6 := by
  rw [coeff_weightedDerivation, f, coeff_add, coeff_single, coeff_single]
  norm_num [Finsupp.single_apply]

example : (weightedDerivation (Int.castAddHom ℤ) f).coeff 1 = -4 := by
  rw [coeff_weightedDerivation, f, coeff_add, coeff_single, coeff_single]
  norm_num [Finsupp.single_apply]

example : weightedDerivation (Int.castAddHom ℤ) (f * single 3 5) =
    single 1 15 + single 4 (-80) := by
  have hp : f * single 3 5 = single 1 15 + single 4 (-20) := by
    rw [f, add_mul, single_mul_single, single_mul_single]
    norm_num
  rw [hp, map_add, weightedDerivation_single, weightedDerivation_single]
  norm_num

example : weightedDerivation (2 • Int.castAddHom ℤ) (single (-2) 3) = single (-2) (-12) := by
  rw [weightedDerivation_single]
  norm_num

example : weightedDerivation (Int.castAddHom (ZMod 2)) (single 2 1) = 0 := by
  rw [weightedDerivation_single]
  have h : (Int.castAddHom (ZMod 2)) 2 = 0 := by
    change ((2 : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  rw [h, zero_mul, single_zero]

#print axioms AddMonoidAlgebra.weightedDerivation
#print axioms AddMonoidAlgebra.coeff_weightedDerivation
#print axioms AddMonoidAlgebra.weightedDerivation_single
#print axioms AddMonoidAlgebra.weightedDerivation_zero
