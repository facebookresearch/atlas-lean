/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.InnerProductSpace.TensorProduct.OperatorAlgebra

/-!
# Complex scalar operators on completed Hilbert tensors

Nonreal scalar endomorphisms of two copies of ℂ act on the Hilbert tensor
completion through the algebraic nonunital star-algebra homomorphism.
Their pure-vector values multiply the scalar coefficients; involution
conjugates these coefficients and multiplication composes the factor
endomorphisms.

A zero Hilbert factor gives zero action on the actual completed tensor
carrier.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open UniformSpace
open scoped TensorProduct

namespace CompletedTensorOperatorAlgebraSmoke

private instance (priority := 2000) complexOperatorSelfSMul :
    SMul (ℂ →L[ℂ] ℂ) (ℂ →L[ℂ] ℂ) :=
  (Monoid.toMulAction (M := (ℂ →L[ℂ] ℂ))).toSMul

private instance (priority := 2000) complexOperatorSelfModule :
    Module (ℂ →L[ℂ] ℂ) (ℂ →L[ℂ] ℂ) :=
  Semiring.toModule

private instance complexOperatorAlgebra : Algebra ℂ (ℂ →L[ℂ] ℂ) :=
  ContinuousLinearMap.algebra (R := ℂ) (S := ℂ) (M := ℂ)

private abbrev TensorHilbert := Completion (ℂ ⊗[ℂ] ℂ)
private def unitTensor : TensorHilbert := ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorHilbert)
private def scalarOperator (c : ℂ) : ℂ →L[ℂ] ℂ := c • ContinuousLinearMap.id ℂ ℂ

private theorem scalarOperator_mul (c d : ℂ) :
    scalarOperator c * scalarOperator d = scalarOperator (c * d) := by
  apply ContinuousLinearMap.ext
  intro x
  change c • (d • x) = (c * d) • x
  exact smul_smul c d x

private theorem scalarOperator_star (c : ℂ) :
    star (scalarOperator c) = scalarOperator (star c) := by
  simp only [scalarOperator, star_smul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_id]

private theorem scalarTensorAction (c d : ℂ) :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
        (scalarOperator c ⊗ₜ[ℂ] scalarOperator d) unitTensor =
      (c * d) • unitTensor := by
  unfold unitTensor
  rw [TensorProduct.mapLCompletionNonUnitalStarAlgHom_tmul,
    TensorProduct.mapLCompletion_tmul]
  change ((c • (1 : ℂ)) ⊗ₜ[ℂ] (d • (1 : ℂ)) : TensorHilbert) =
    (c * d) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorHilbert)
  rw [TensorProduct.smul_tmul_smul, Completion.coe_smul]

example :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
        (scalarOperator (1 + Complex.I) ⊗ₜ[ℂ] scalarOperator (2 - Complex.I)) unitTensor =
      ((1 + Complex.I) * (2 - Complex.I)) • unitTensor :=
  scalarTensorAction _ _

example :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
        (star (scalarOperator (1 + Complex.I) ⊗ₜ[ℂ] scalarOperator (2 - Complex.I)))
        unitTensor =
      (star (1 + Complex.I) * star (2 - Complex.I)) • unitTensor := by
  rw [TensorProduct.star_tmul, scalarOperator_star, scalarOperator_star]
  exact scalarTensorAction _ _

example :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
        ((scalarOperator (1 + Complex.I) ⊗ₜ[ℂ] scalarOperator (2 - Complex.I)) *
          (scalarOperator Complex.I ⊗ₜ[ℂ] scalarOperator (1 + Complex.I))) unitTensor =
      (((1 + Complex.I) * Complex.I) * ((2 - Complex.I) * (1 + Complex.I))) • unitTensor := by
  rw [map_mul]
  change
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
        (scalarOperator (1 + Complex.I) ⊗ₜ[ℂ] scalarOperator (2 - Complex.I))
        (TensorProduct.mapLCompletionNonUnitalStarAlgHom
          (scalarOperator Complex.I ⊗ₜ[ℂ] scalarOperator (1 + Complex.I)) unitTensor) =
      (((1 + Complex.I) * Complex.I) * ((2 - Complex.I) * (1 + Complex.I))) • unitTensor
  rw [scalarTensorAction, map_smul, scalarTensorAction, smul_smul]
  exact congrArg (fun c : ℂ => c • unitTensor)
    ((mul_comm (Complex.I * (1 + Complex.I)) ((1 + Complex.I) * (2 - Complex.I))).trans
      (mul_mul_mul_comm (1 + Complex.I) (2 - Complex.I) Complex.I (1 + Complex.I)))

private abbrev ZeroHilbert := (⊥ : Submodule ℂ ℂ)

example (x : Completion (ZeroHilbert ⊗[ℂ] ℂ)) :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
        (star (ContinuousLinearMap.id ℂ ZeroHilbert ⊗ₜ[ℂ]
          scalarOperator (1 + Complex.I)) *
          (ContinuousLinearMap.id ℂ ZeroHilbert ⊗ₜ[ℂ]
            scalarOperator (2 - Complex.I))) x =
      (0 : Completion (ZeroHilbert ⊗[ℂ] ℂ)) := by
  have hzero (z : Completion (ZeroHilbert ⊗[ℂ] ℂ)) : z = 0 := by
    refine Completion.induction_on z (isClosed_eq continuous_id continuous_const) ?_
    intro w
    have hw : w = 0 := Subsingleton.elim _ _
    simpa only [hw, Completion.coe_zero]
  exact hzero _

end CompletedTensorOperatorAlgebraSmoke
