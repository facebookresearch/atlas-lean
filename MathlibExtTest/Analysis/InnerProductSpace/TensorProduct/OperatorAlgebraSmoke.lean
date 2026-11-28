/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.OperatorAlgebra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.NormNum

/-!
# Stock endomorphisms on a completed finite-dimensional Hilbert tensor

Nonreal scalar endomorphisms of two stock complex Euclidean planes act
on their actual Hilbert tensor completion; involution conjugates their
coefficients. The coordinate rank-one operators E01 and E10 have different
composition orders. On a nonzero pure unit tensor, one order gives a
nonzero complex scalar multiple while the reverse order is zero.
A zero Hilbert factor retains zero action on the actual completion.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open UniformSpace
open scoped TensorProduct

namespace CompletedTensorOperatorAlgebraSmoke

private abbrev H := EuclideanSpace ℂ (Fin 2)
private abbrev TensorHilbert := Completion (H ⊗[ℂ] H)
private def e0 : H := EuclideanSpace.single 0 (1 : ℂ)
private def e1 : H := EuclideanSpace.single 1 (1 : ℂ)
private def unitTensor : TensorHilbert := (e0 ⊗ₜ[ℂ] e0 : TensorHilbert)
private def scalarOperator (c : ℂ) : H →L[ℂ] H := c • ContinuousLinearMap.id ℂ H
private abbrev E01 : H →L[ℂ] H := InnerProductSpace.rankOne ℂ e0 e1
private abbrev E10 : H →L[ℂ] H := InnerProductSpace.rankOne ℂ e1 e0

private theorem e0_norm : ‖e0‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)).norm_eq_one 0

private theorem e0_ne_zero : e0 ≠ 0 := by
  intro h
  have hn := e0_norm
  rw [h, norm_zero] at hn
  norm_num at hn

private theorem unitTensor_norm : ‖unitTensor‖ = 1 := by
  change ‖((e0 ⊗ₜ[ℂ] e0 : H ⊗[ℂ] H) : TensorHilbert)‖ = 1
  rw [Completion.norm_coe, TensorProduct.norm_tmul, e0_norm]
  norm_num

private theorem E01_e0 : E01 e0 = 0 := by
  simp [e0, e1, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left]

private theorem E01_e1 : E01 e1 = e0 := by
  simp [e0, e1, InnerProductSpace.rankOne_apply]

private theorem E10_e0 : E10 e0 = e1 := by
  simp [e0, e1, InnerProductSpace.rankOne_apply]

private theorem scalarOperator_star (c : ℂ) :
    star (scalarOperator c) = scalarOperator (star c) := by
  simp only [scalarOperator, star_smul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_id]

private theorem scalarTensorAction (c d : ℂ) :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      (scalarOperator c ⊗ₜ[ℂ] scalarOperator d) unitTensor = (c * d) • unitTensor := by
  unfold unitTensor
  rw [TensorProduct.mapLCompletionNonUnitalStarAlgHom_tmul, TensorProduct.mapLCompletion_tmul]
  change ((c • e0) ⊗ₜ[ℂ] (d • e0) : TensorHilbert) =
    (c * d) • ((e0 ⊗ₜ[ℂ] e0 : H ⊗[ℂ] H) : TensorHilbert)
  rw [TensorProduct.smul_tmul_smul, Completion.coe_smul]

example :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      (scalarOperator (1 + Complex.I) ⊗ₜ[ℂ] scalarOperator (2 - Complex.I)) unitTensor =
      ((1 + Complex.I) * (2 - Complex.I)) • unitTensor := scalarTensorAction _ _

example :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      (star (scalarOperator (1 + Complex.I) ⊗ₜ[ℂ] scalarOperator (2 - Complex.I))) unitTensor =
      (star (1 + Complex.I) * star (2 - Complex.I)) • unitTensor := by
  rw [TensorProduct.star_tmul, scalarOperator_star, scalarOperator_star]
  exact scalarTensorAction _ _

private theorem forward_product :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      ((E01 ⊗ₜ[ℂ] scalarOperator (1 + Complex.I)) *
        (E10 ⊗ₜ[ℂ] scalarOperator (2 - Complex.I))) unitTensor =
      ((1 + Complex.I) * (2 - Complex.I)) • unitTensor := by
  rw [map_mul]
  change TensorProduct.mapLCompletion E01 (scalarOperator (1 + Complex.I))
      (TensorProduct.mapLCompletion E10 (scalarOperator (2 - Complex.I)) unitTensor) = _
  unfold unitTensor
  rw [TensorProduct.mapLCompletion_tmul, E10_e0,
    TensorProduct.mapLCompletion_tmul, E01_e1]
  change (e0 ⊗ₜ[ℂ] ((1 + Complex.I) • ((2 - Complex.I) • e0)) : TensorHilbert) =
    (((1 + Complex.I) * (2 - Complex.I)) •
      ((e0 ⊗ₜ[ℂ] e0 : H ⊗[ℂ] H) : TensorHilbert))
  rw [smul_smul, TensorProduct.tmul_smul, Completion.coe_smul]

private theorem reverse_product :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      ((E10 ⊗ₜ[ℂ] scalarOperator (2 - Complex.I)) *
        (E01 ⊗ₜ[ℂ] scalarOperator (1 + Complex.I))) unitTensor = 0 := by
  rw [map_mul]
  change TensorProduct.mapLCompletion E10 (scalarOperator (2 - Complex.I))
      (TensorProduct.mapLCompletion E01 (scalarOperator (1 + Complex.I)) unitTensor) = 0
  unfold unitTensor
  rw [TensorProduct.mapLCompletion_tmul, E01_e0, TensorProduct.zero_tmul,
    Completion.coe_zero, map_zero]

example :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      ((E01 ⊗ₜ[ℂ] scalarOperator (1 + Complex.I)) *
        (E10 ⊗ₜ[ℂ] scalarOperator (2 - Complex.I))) unitTensor =
        ((1 + Complex.I) * (2 - Complex.I)) • unitTensor ∧
      TensorProduct.mapLCompletionNonUnitalStarAlgHom
        ((E10 ⊗ₜ[ℂ] scalarOperator (2 - Complex.I)) *
          (E01 ⊗ₜ[ℂ] scalarOperator (1 + Complex.I))) unitTensor = 0 ∧
      E01 * E10 ≠ E10 * E01 := by
  refine ⟨forward_product, reverse_product, ?_⟩
  intro h
  have he := congrArg (fun T : H →L[ℂ] H => T e0) h
  change E01 (E10 e0) = E10 (E01 e0) at he
  rw [E10_e0, E01_e1, E01_e0, map_zero] at he
  exact e0_ne_zero he

private abbrev ZeroHilbert := EuclideanSpace ℂ (Fin 0)

example (x : Completion (ZeroHilbert ⊗[ℂ] H)) :
    TensorProduct.mapLCompletionNonUnitalStarAlgHom
      (star (ContinuousLinearMap.id ℂ ZeroHilbert ⊗ₜ[ℂ] scalarOperator (1 + Complex.I)) *
        (ContinuousLinearMap.id ℂ ZeroHilbert ⊗ₜ[ℂ] scalarOperator (2 - Complex.I))) x =
      (0 : Completion (ZeroHilbert ⊗[ℂ] H)) := by
  have hzero (z : Completion (ZeroHilbert ⊗[ℂ] H)) : z = 0 := by
    refine Completion.induction_on z (isClosed_eq continuous_id continuous_const) ?_
    intro w
    have hw : w = 0 := Subsingleton.elim _ _
    simp only [hw, Completion.coe_zero]
  exact hzero _

end CompletedTensorOperatorAlgebraSmoke
