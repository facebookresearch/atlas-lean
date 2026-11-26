/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import MathlibExt.AlgebraicGeometry.LiFiniteComplexPresentations

/-!
# Actual tensor evaluation for Li's universal extension

The coefficient homomorphism evaluates the universal dual coefficient:
(v tensor i)(phi)=phi(v)*i. It is the native tensor-product lift of that
bilinear pairing. No arbitrary coefficient equivalence is selected.
Source: Jun Li arXiv:math/0110113v1, universal identity tensor and
the coefficient maps following equations1.15--1.19.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiTensorEvaluation

open scoped TensorProduct

variable (A V I : Type) [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup I] [Module A I]

def pairing : V →ₗ[A] I →ₗ[A] ((V →ₗ[A] A) →ₗ[A] I) where
  toFun v :=
    { toFun i :=
        { toFun f := f v • i
          map_add' f h := by change (f v + h v) • i = _; exact add_smul _ _ _
          map_smul' a f := by change (a * f v) • i = a • (f v • i); exact mul_smul _ _ _ }
      map_add' i j := by ext f; exact smul_add _ _ _
      map_smul' a i := by ext f; exact smul_comm _ _ _ }
  map_add' v w := by
    ext i f
    change f (v + w) • i = f v • i + f w • i
    rw [map_add, add_smul]
  map_smul' a v := by
    ext i f
    change f (a • v) • i = a • (f v • i)
    rw [f.map_smul, smul_eq_mul, mul_smul]

def evaluation : V ⊗[A] I →ₗ[A] ((V →ₗ[A] A) →ₗ[A] I) :=
  TensorProduct.lift (pairing A V I)

@[simp] theorem evaluation_tmul (v : V) (i : I) (f : V →ₗ[A] A) :
    evaluation A V I (v ⊗ₜ[A] i) f = f v • i := rfl

end MathlibExt.AlgebraicGeometry.LiTensorEvaluation
