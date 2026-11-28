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

public import MathlibExt.LinearAlgebra.TensorProduct.HomFiniteFactorScalar
public import MathlibExt.LinearAlgebra.TensorProduct.SurjectiveScalarHom
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Semilinear Hom–tensor comparisons with an infinite source

Evaluation on the module of integer sequences gives a nonzero semilinear
map into the rationals. The finite tensor factors have ranks one and two.
A quotient-scalar example uses the same source with only its integer-module
structure and a tensor factor over `ZMod 2`.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace HomFiniteFactorSemilinearTests

private def rationalEval : (ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] ℚ :=
  (algebraMap ℤ ℚ).toSemilinearMap.comp
    (LinearMap.proj (0 : ℤ) : (ℤ → ℤ) →ₗ[ℤ] ℤ)

example : Function.Bijective
    (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ ℚ) :=
  TensorProduct.rTensorHomToHomRTensor_bijective_of_finite_projective
    (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ ℚ

private theorem rational_tensor_value :
    TensorProduct.rid ℚ ℚ
      (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ ℚ
        (rationalEval ⊗ₜ[ℚ] (3 : ℚ)) (fun _ => (2 : ℤ))) = 6 := by
  norm_num [rationalEval, TensorProduct.rTensorHomToHomRTensor_apply]

example : (rationalEval ⊗ₜ[ℚ] (3 : ℚ) :
    ((ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] ℚ) ⊗[ℚ] ℚ) ≠ 0 := by
  intro h
  have hv := rational_tensor_value
  rw [h, map_zero, LinearMap.zero_apply, map_zero] at hv
  norm_num at hv

example : Function.Bijective
    (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ (Fin 2 → ℚ)) :=
  TensorProduct.rTensorHomToHomRTensor_bijective_of_finite_projective
    (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ (Fin 2 → ℚ)

example :
    TensorProduct.piScalarRight ℚ ℚ ℚ (Fin 2)
      (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ (Fin 2 → ℚ)
        (rationalEval ⊗ₜ[ℚ] (fun i => if i = 0 then 3 else 5))
        (fun _ => (2 : ℤ))) (1 : Fin 2) = 10 := by
  norm_num [rationalEval, TensorProduct.rTensorHomToHomRTensor_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

private theorem modTwoScalars_surjective :
    Function.Surjective (algebraMap ℤ (ZMod 2)) := by
  change Function.Surjective ((↑) : ℤ → ZMod 2)
  exact ZMod.intCast_surjective

private def modTwoEval : (ℤ → ℤ) →ₗ[ℤ] ZMod 2 :=
  (Algebra.linearMap ℤ (ZMod 2)).comp
    (LinearMap.proj (0 : ℤ) : (ℤ → ℤ) →ₗ[ℤ] ℤ)

private def modTwoMultiply : ZMod 2 ⊗[ℤ] ZMod 2 →ₗ[ℤ] ZMod 2 :=
  (TensorProduct.rid (ZMod 2) (ZMod 2)).toLinearMap.restrictScalars ℤ ∘ₗ
    TensorProduct.mapOfCompatibleSMul (ZMod 2) ℤ ℤ (ZMod 2) (ZMod 2)

example : Function.Bijective
    (TensorProduct.rTensorHomToHomRTensor (.id ℤ) (ℤ → ℤ) (ZMod 2) (ZMod 2)) := by
  rw [← TensorProduct.homTensorFiniteFactorEquivOfSurjectiveScalars_toLinearMap
    (P := ℤ → ℤ) (N := ZMod 2) (U := ZMod 2) modTwoScalars_surjective]
  exact (TensorProduct.homTensorFiniteFactorEquivOfSurjectiveScalars
    (P := ℤ → ℤ) (N := ZMod 2) (U := ZMod 2) modTwoScalars_surjective).bijective

private theorem modTwo_tensor_value :
    modTwoMultiply
      (TensorProduct.homTensorFiniteFactorEquivOfSurjectiveScalars
        (P := ℤ → ℤ) (N := ZMod 2) (U := ZMod 2) modTwoScalars_surjective
        (modTwoEval ⊗ₜ[ℤ] (1 : ZMod 2)) (fun _ => (1 : ℤ))) = 1 := by
  rw [TensorProduct.homTensorFiniteFactorEquivOfSurjectiveScalars_tmul]
  change TensorProduct.rid (ZMod 2) (ZMod 2)
    (TensorProduct.mapOfCompatibleSMul (ZMod 2) ℤ ℤ (ZMod 2) (ZMod 2)
      ((modTwoEval (fun _ => (1 : ℤ))) ⊗ₜ[ℤ] (1 : ZMod 2))) = 1
  rw [TensorProduct.mapOfCompatibleSMul_tmul]
  simp [modTwoEval]

example : (modTwoEval ⊗ₜ[ℤ] (1 : ZMod 2) :
    ((ℤ → ℤ) →ₗ[ℤ] ZMod 2) ⊗[ℤ] ZMod 2) ≠ 0 := by
  intro h
  have hv := modTwo_tensor_value
  rw [h, map_zero, LinearMap.zero_apply, map_zero] at hv
  exact zero_ne_one hv

private def sourceDouble : ℤ →ₗ[ℤ] (ℤ → ℤ) :=
  (LinearMap.const (R := ℤ) : ℤ →ₗ[ℤ] (ℤ → ℤ)).comp
    ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private def coefficientTriple : ℚ →ₗ[ℚ] ℚ :=
  (3 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)

private def factorPair : ℚ →ₗ[ℚ] (Fin 2 → ℚ) :=
  LinearMap.pi fun i =>
    (if i = 0 then (4 : ℚ) else 5) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)

private def semilinearSquareInput :
    (((ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] ℚ) ⊗[ℚ] ℚ) →ₗ[ℚ]
      ((ℤ →ₛₗ[algebraMap ℤ ℚ] ℚ) ⊗[ℚ] (Fin 2 → ℚ)) :=
  TensorProduct.map
    ((LinearMap.llcomp ℚ ℤ ℚ ℚ coefficientTriple).comp
      (LinearMap.lcompₛₗ ℚ ℚ (algebraMap ℤ ℚ) sourceDouble)) factorPair

private def semilinearSquareOutput :
    ((ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] ℚ ⊗[ℚ] ℚ) →ₗ[ℚ]
      (ℤ →ₛₗ[algebraMap ℤ ℚ] ℚ ⊗[ℚ] (Fin 2 → ℚ)) :=
  (LinearMap.llcomp ℚ ℤ (ℚ ⊗[ℚ] ℚ) (ℚ ⊗[ℚ] (Fin 2 → ℚ))
    (TensorProduct.map coefficientTriple factorPair)).comp
      (LinearMap.lcompₛₗ ℚ (ℚ ⊗[ℚ] ℚ) (algebraMap ℤ ℚ) sourceDouble)

/-- All three nonidentity maps commute with the semilinear comparison, and
coordinate evaluation of the resulting square is nonzero. -/
example :
    TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) ℤ ℚ (Fin 2 → ℚ)
        (semilinearSquareInput (rationalEval ⊗ₜ[ℚ] (1 : ℚ))) =
      semilinearSquareOutput
        (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ ℚ
          (rationalEval ⊗ₜ[ℚ] (1 : ℚ))) ∧
    TensorProduct.piScalarRight ℚ ℚ ℚ (Fin 2)
        (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) ℤ ℚ (Fin 2 → ℚ)
          (semilinearSquareInput (rationalEval ⊗ₜ[ℚ] (1 : ℚ))) (3 : ℤ))
        (0 : Fin 2) = 72 := by
  constructor
  · exact LinearMap.congr_fun
      (TensorProduct.rTensorHomToHomRTensor_map_precomp
        (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ sourceDouble coefficientTriple factorPair)
      (rationalEval ⊗ₜ[ℚ] (1 : ℚ))
  · norm_num [semilinearSquareInput, sourceDouble, coefficientTriple, factorPair,
      rationalEval, TensorProduct.rTensorHomToHomRTensor_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

private def leftFactorPair : Fin 2 → ℚ :=
  fun i => if i = 0 then 4 else 5

private def leftCoefficientTriple : ℚ →ₗ[ℚ] (Fin 3 → ℚ) :=
  LinearMap.pi fun j =>
    (if j = 0 then (1 : ℚ) else if j = 1 then 2 else 3) •
      (LinearMap.id : ℚ →ₗ[ℚ] ℚ)

private def leftSemilinearHom : (ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] (Fin 3 → ℚ) :=
  leftCoefficientTriple.comp rationalEval

private def leftCoordinateProbe (i : Fin 2) (j : Fin 3) :
    (Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ) →ₗ[ℚ] ℚ :=
  (LinearMap.proj i).comp
    ((TensorProduct.rid ℚ (Fin 2 → ℚ)).toLinearMap.comp
      ((LinearMap.proj j).comp
        (TensorProduct.piRight ℚ ℚ (Fin 2 → ℚ) (fun _ : Fin 3 => ℚ)).toLinearMap))

example : Function.Bijective
    (TensorProduct.lTensorHomToHomLTensor
      (algebraMap ℤ ℚ) (ℤ → ℤ) (Fin 2 → ℚ) (Fin 3 → ℚ)) :=
  TensorProduct.lTensorHomToHomLTensor_bijective_of_finite_projective
    (algebraMap ℤ ℚ) (ℤ → ℤ) (Fin 3 → ℚ) (Fin 2 → ℚ)

/-- Unequal off-diagonal coordinates retain the left-factor index before
its coefficient-module index. -/
private theorem left_coefficient_order_values :
    leftCoordinateProbe 0 1
        (TensorProduct.lTensorHomToHomLTensorEquiv
          (algebraMap ℤ ℚ) (ℤ → ℤ) (Fin 3 → ℚ) (Fin 2 → ℚ)
          (leftFactorPair ⊗ₜ[ℚ] leftSemilinearHom) (fun _ => (2 : ℤ))) = 16 ∧
    leftCoordinateProbe 1 0
        (TensorProduct.lTensorHomToHomLTensorEquiv
          (algebraMap ℤ ℚ) (ℤ → ℤ) (Fin 3 → ℚ) (Fin 2 → ℚ)
          (leftFactorPair ⊗ₜ[ℚ] leftSemilinearHom) (fun _ => (2 : ℤ))) = 10 := by
  constructor <;>
    rw [TensorProduct.lTensorHomToHomLTensorEquiv_tmul] <;>
    norm_num [leftCoordinateProbe, leftFactorPair, leftSemilinearHom,
      leftCoefficientTriple, rationalEval, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]

example : (leftFactorPair ⊗ₜ[ℚ] leftSemilinearHom :
    (Fin 2 → ℚ) ⊗[ℚ] ((ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] (Fin 3 → ℚ))) ≠ 0 := by
  intro h
  have hv := left_coefficient_order_values.1
  rw [h, map_zero, LinearMap.zero_apply, map_zero] at hv
  norm_num at hv

private def rationalEquiv :
    (((ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] ℚ) ⊗[ℚ] ℚ) ≃ₗ[ℚ]
      ((ℤ → ℤ) →ₛₗ[algebraMap ℤ ℚ] ℚ ⊗[ℚ] ℚ) :=
  LinearEquiv.ofBijective
    (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ ℚ)
    (TensorProduct.rTensorHomToHomRTensor_bijective_of_finite_projective
      (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ ℚ)

private def pairEquiv :
    (ℤ →ₛₗ[algebraMap ℤ ℚ] ℚ) ⊗[ℚ] (Fin 2 → ℚ) ≃ₗ[ℚ]
      (ℤ →ₛₗ[algebraMap ℤ ℚ] ℚ ⊗[ℚ] (Fin 2 → ℚ)) :=
  LinearEquiv.ofBijective
    (TensorProduct.rTensorHomToHomRTensor (algebraMap ℤ ℚ) ℤ ℚ (Fin 2 → ℚ))
    (TensorProduct.rTensorHomToHomRTensor_bijective_of_finite_projective
      (algebraMap ℤ ℚ) ℤ ℚ (Fin 2 → ℚ))

-- The same three nonidentity maps also satisfy the inverse naturality square.
example :
    pairEquiv.symm
        (semilinearSquareOutput (rationalEquiv (rationalEval ⊗ₜ[ℚ] (1 : ℚ)))) =
      semilinearSquareInput (rationalEval ⊗ₜ[ℚ] (1 : ℚ)) := by
  have h := LinearMap.congr_fun
    (TensorProduct.rTensorHomToHomRTensor_symm_map_precomp
      (algebraMap ℤ ℚ) (ℤ → ℤ) ℚ sourceDouble coefficientTriple factorPair)
    (rationalEquiv (rationalEval ⊗ₜ[ℚ] (1 : ℚ)))
  simpa only [rationalEquiv, pairEquiv, semilinearSquareInput,
    semilinearSquareOutput, LinearMap.comp_apply, LinearEquiv.symm_apply_apply] using h

example :
    TensorProduct.piScalarRight ℚ ℚ ℚ (Fin 2)
        (pairEquiv
          (pairEquiv.symm
            (semilinearSquareOutput (rationalEquiv (rationalEval ⊗ₜ[ℚ] (1 : ℚ)))))
          (3 : ℤ)) (0 : Fin 2) = 72 := by
  rw [LinearEquiv.apply_symm_apply]
  norm_num [semilinearSquareOutput, rationalEquiv, sourceDouble, coefficientTriple,
    factorPair, rationalEval, TensorProduct.rTensorHomToHomRTensor_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

private def domainFiniteHom : ZMod 2 →ₗ[ℤ] ZMod 2 := LinearMap.id

private def infiniteResidueFactor : ℕ → ZMod 2 := fun _ => 1

private def residueProductProbe :
    (ZMod 2) ⊗[ℤ] (ℕ → ZMod 2) →ₗ[ℤ] ZMod 2 :=
  modTwoMultiply.comp ((LinearMap.proj (0 : ℕ)).lTensor (ZMod 2))

-- Finite projectivity is on the Hom domain; the tensor factor is an unrestricted product.
private theorem domain_finite_value :
    residueProductProbe
      (TensorProduct.rTensorHomEquivOfSurjectiveScalars
        (R := ℤ) (S := ZMod 2) (M := ZMod 2) (J := ZMod 2)
        (U := ℕ → ZMod 2) modTwoScalars_surjective
        (domainFiniteHom ⊗ₜ[ℤ] infiniteResidueFactor) (1 : ZMod 2)) = 1 := by
  rw [TensorProduct.rTensorHomEquivOfSurjectiveScalars_tmul]
  simp [residueProductProbe, domainFiniteHom, infiniteResidueFactor, modTwoMultiply]

example :
    (domainFiniteHom ⊗ₜ[ℤ] infiniteResidueFactor :
      ((ZMod 2) →ₗ[ℤ] ZMod 2) ⊗[ℤ] (ℕ → ZMod 2)) ≠ 0 := by
  intro h
  have h' := domain_finite_value
  rw [h, map_zero, LinearMap.zero_apply, map_zero] at h'
  exact zero_ne_one h'

end HomFiniteFactorSemilinearTests
