/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.HahnSeries.GradedCoefficientMap
import MathlibExt.RingTheory.HahnSeries.CoefficientDerivation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.ZMod.Basic

open HahnSeries Polynomial

private noncomputable def sourceTwist {R : Type*} [CommRing R]
    (D : ℤ → R →+ R) (f : HahnSeries ℤ R) : HahnSeries ℤ R where
  coeff y := D y (f.coeff y)
  isPWO_support' := f.isPWO_support.mono fun y hy h => hy (by simp [h])

example {R : Type*} [CommRing R] (D : ℤ → R →+ R) (f : HahnSeries ℤ R) :
    sourceTwist D f = gradedCoefficientMap D f := by
  rfl

private def intWeight (i : ℤ) : ℤ →+ ℤ := i • AddMonoidHom.id ℤ

private theorem intWeight_mul (i j a b : ℤ) :
    intWeight (i + j) (a * b) = intWeight i a * b + a * intWeight j b := by
  simp only [intWeight, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
  ring

private noncomputable def f : HahnSeries ℤ ℤ := single (-2) 3 + single 1 (-4)

private noncomputable def g : HahnSeries ℤ ℤ := single 3 5

example : gradedCoefficientMap intWeight f = single (-2) (-6) + single 1 (-4) := by
  simp [f, intWeight]

example : gradedCoefficientMap intWeight (f * g) = single 1 15 + single 4 (-80) := by
  rw [gradedCoefficientMap_mul intWeight intWeight_mul]
  ext y
  simp [f, g, intWeight, add_mul]
  by_cases h1 : y = 1 <;> by_cases h4 : y = 4 <;> simp [h1, h4]

example (D : ℤ → ℤ →+ ℤ)
    (hD : ∀ i j a b, D (i + j) (a * b) = D i a * b + a * D j b)
    (x y : HahnSeries ℤ ℤ) :
    gradedCoefficientMap D (x * y) =
      gradedCoefficientMap D x * y + x * gradedCoefficientMap D y :=
  gradedCoefficientMap_mul D hD x y

example (D : ℤ → ℤ →+ ℤ) (x : HahnSeries ℤ ℤ) :
    (gradedCoefficientMap D x).support ⊆ x.support :=
  support_gradedCoefficientMap D x

example : gradedCoefficientMap (fun _ => (0 : ℤ →+ ℤ)) f = 0 := by
  simp

example : gradedCoefficientMap intWeight (single (-2 : ℤ) 3) = single (-2 : ℤ) (-6) := by
  simp [intWeight]

example :
    gradedCoefficientMap (fun _ : ℤ =>
      Polynomial.derivative'.toLinearMap.toAddMonoidHom)
      (single (-2 : ℤ) (X ^ 2)) = single (-2 : ℤ) (2 * X : Polynomial ℚ) := by
  simp [Polynomial.derivative']
  norm_num

example (x : HahnSeries ℤ (Polynomial ℚ)) :
    gradedCoefficientMap (fun _ : ℤ =>
      Polynomial.derivative'.toLinearMap.toAddMonoidHom) x =
      coefficientDerivation Polynomial.derivative' x := by
  ext y
  rfl

example :
    gradedCoefficientMap (fun _ : ℤ =>
      Polynomial.derivative'.toLinearMap.toAddMonoidHom)
      (HahnSeries.C (X ^ 2 : Polynomial ℚ)) ≠ 0 := by
  rw [gradedCoefficientMap_C]
  simp [Polynomial.derivative']

example :
    gradedCoefficientMap (fun i : ℤ => (i : ZMod 2) • AddMonoidHom.id (ZMod 2))
      (single (-2 : ℤ) 1 + single 1 1) = single 1 1 := by
  have h : ((-2 : ℤ) : ZMod 2) = 0 := by decide
  simp [h]

example : ¬∀ _i _j a b : ℤ,
    (AddMonoidHom.id ℤ) (a * b) =
      (AddMonoidHom.id ℤ) a * b + a * (AddMonoidHom.id ℤ) b := by
  intro h
  have := h 0 0 1 1
  norm_num at this

-- The source's `thV`: the outer exponent scales its own coefficient.
example (x : HahnSeries ℤ ℚ) (y : ℤ) :
    (gradedCoefficientMap (fun i : ℤ => (i : ℚ) • AddMonoidHom.id ℚ) x).coeff y =
      y * x.coeff y := by
  simp

-- The source's `thU`: one fixed coefficient derivation is used at every outer exponent.
example (x : HahnSeries ℤ (Polynomial ℚ)) (y : ℤ) :
    (gradedCoefficientMap (fun _ : ℤ =>
      Polynomial.derivative'.toLinearMap.toAddMonoidHom) x).coeff y =
      Polynomial.derivative' (x.coeff y) := by
  rfl

#print axioms HahnSeries.gradedCoefficientMap
#print axioms HahnSeries.coeff_gradedCoefficientMap
#print axioms HahnSeries.support_gradedCoefficientMap
#print axioms HahnSeries.gradedCoefficientMap_zero_family
#print axioms HahnSeries.gradedCoefficientMap_single
#print axioms HahnSeries.gradedCoefficientMap_C
#print axioms HahnSeries.gradedCoefficientMap_mul
