/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension
public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeRowCore
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Noncommutative free-row calibration for actual scalar extension

The existing finite general linear group acts on free left modules through
its opposite group, by right multiplication of rows. The actual balanced
tensor coordinates intertwine that same action with the existing coefficient
map. No comparison map, free-projective or commutative-ring hypothesis is used.
-/

public section

noncomputable section
set_option autoImplicit false

open scoped Matrix
open MulOpposite

universe uR uS

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Scalar extension carries the original opposite-GL row action to its actual coefficient map. -/
theorem scalarExtension_rowGL (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n).toLinearMap.comp
        (ModuleCat.RingHomScalarExtension.linearMap f
          (rowGLLinearEquiv R n (op g)).toLinearMap) =
      (rowGLLinearEquiv S n
          (op (Matrix.GeneralLinearGroup.mapRingHom f g))).toLinearMap.comp
        (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n).toLinearMap := by
  apply ModuleCat.RingHomScalarExtension.linearMap_ext f (Fin n → R)
  intro s x
  apply funext
  intro j
  simp only [LinearMap.comp_apply,
    ModuleCat.RingHomScalarExtension.linearMap_pure,
    ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv_pure,
    LinearEquiv.coe_toLinearMap, rowGLLinearEquiv_apply]
  have hCoordinates :
      ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n
        (ModuleCat.RingHomScalarExtension.pure f (Fin n → R) s x) =
      (fun i => s * f (x i)) :=
    funext (fun i => ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv_pure
      f n s x i)
  rw [MulOpposite.unop_op, MulOpposite.unop_op, hCoordinates,
    Matrix.GeneralLinearGroup.coe_mapRingHom]
  simp only [Matrix.vecMul_apply, dotProduct, Matrix.col_apply, Matrix.map_apply]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, mul_assoc]

end FGProjectiveCat
