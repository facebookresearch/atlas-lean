/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExtTest.Algebra.Category.CommAlgCat.CotangentPushoutFlatNonflat

/-!
# Nonflat coefficients with independent algebra and module universes

The algebra is the universe-one lift of `ℤ`, and its scalar-change target is
identified with `ℤ`. The coefficient module is `ℤ/4ℤ` in universe zero, acted
on through that integer identification and reduction modulo four.

The degree-zero weight-zero tensor has value one in the original coefficient
carrier and `ULift.up 1` in the universe-one categorical carrier, and is nonzero.
Multiplication by four in the target ring witnesses the coefficient's nonflatness.
All higher-form coefficient models still admit their homotopy comparison, and
weight-zero degree-zero homology is nontrivial.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

namespace MathlibExtTest.CotangentPushout.IndependentCoefficient

/--
The integer ring lifted from universe zero to universe one.
-/
abbrev HigherAlgebra := ULift.{1, 0} ℤ

/--
The universe-one commutative `ℤ`-algebra represented by the lifted integer ring.
-/
def originalAlgebra : CommAlgCat.{1} ℤ := CommAlgCat.of ℤ HigherAlgebra
/--
The tensor-product target `ℤ ⊗[ℤ] ULift ℤ`, with its algebra-carrier height one.
-/
abbrev ActualTarget := CommAlgCat.CotangentPushout.target ℤ ℤ originalAlgebra

/--
The ring equivalence from the scalar-change target to `ℤ`, using tensor
cancellation and the lifted integer ring equivalence.
-/
def targetIntegerEquiv : ActualTarget ≃+* ℤ :=
  (Algebra.TensorProduct.lid ℤ HigherAlgebra).toRingEquiv.trans ULift.ringEquiv

/--
The ring map from the target to `ℤ/4ℤ`, through its integer equivalence and
reduction modulo four.
-/
def coefficientRingMap : ActualTarget →+* ZMod 4 :=
  (Int.castRingHom (ZMod 4)).comp targetIntegerEquiv.toRingHom

/--
The module structure on `ℤ/4ℤ` induced by the target's modulo-four ring map.
-/
instance originalCoefficientModule : Module ActualTarget (ZMod 4) :=
  Module.compHom (ZMod 4) coefficientRingMap

/--
The coefficient object `ℤ/4ℤ` in universe zero, with the target ring action.
-/
def originalCoefficient : ModuleCat.{0} ActualTarget := ModuleCat.of ActualTarget (ZMod 4)

/--
The canonical augmented polynomial resolution of the universe-one lifted
integer algebra.
-/
def canonicalResolution :
    Over ((SimplicialObject.const (CommAlgCat.{1} ℤ)).obj originalAlgebra) :=
  (CommAlgCat.polynomialResolutionOverFunctor.{0, 1} ℤ originalAlgebra).obj
    (Over.mk (𝟙 originalAlgebra))

/--
The weight-zero tensor `1_(ℤ/4ℤ) ⊗ (1 ⊗ 1)` in the degree-zero term of the
canonical coefficient diagram, with the coefficient as first factor.
-/
def literalZeroTensor :
    (CommAlgCat.CotangentPushout.sourceCoefficientSimplicial ℤ ℤ originalAlgebra
      originalCoefficient 0 canonicalResolution).obj (op ⦋0⦌) := by
  let P₀ := Over.mk (canonicalResolution.hom.app (op ⦋0⦌))
  letI : Algebra P₀.left originalAlgebra := CommAlgCat.cotangentAlgebra ℤ originalAlgebra P₀
  letI : Module originalAlgebra originalCoefficient :=
    Module.compHom originalCoefficient (algebraMap originalAlgebra ActualTarget)
  exact (1 : ZMod 4) ⊗ₜ[originalAlgebra]
    ((1 : originalAlgebra) ⊗ₜ[P₀.left] (1 : P₀.left))

/--
The raw weight-zero coordinate equivalence sends the specified tensor to
`1 : ℤ/4ℤ`.
-/
theorem literalZeroTensor_raw_value :
    CommAlgCat.CotangentPushout.zeroCoefficientLevelLinearEquiv ℤ ℤ originalAlgebra
      originalCoefficient canonicalResolution (op ⦋0⦌) literalZeroTensor = (1 : ZMod 4) := by
  simpa only [literalZeroTensor, map_one, mul_one, one_smul] using
    CommAlgCat.CotangentPushout.zeroCoefficientLevelLinearEquiv_tmul ℤ ℤ originalAlgebra
      originalCoefficient canonicalResolution (op ⦋0⦌) 1 1 1

/--
The categorical weight-zero coordinate sends the specified tensor to
`ULift.up (1 : ℤ/4ℤ)` in universe one.
-/
theorem literalZeroTensor_lift_value :
    ((CommAlgCat.CotangentPushout.zeroCoefficientSimplicialIso ℤ ℤ originalAlgebra
      originalCoefficient canonicalResolution).hom.app (op ⦋0⦌)).hom literalZeroTensor =
        (ULift.up (1 : ZMod 4) : ULift.{1, 0} (ZMod 4)) := by
  simpa only [literalZeroTensor, map_one, mul_one, one_smul] using
    CommAlgCat.CotangentPushout.zeroCoefficientSimplicialIso_tmul ℤ ℤ originalAlgebra
      originalCoefficient canonicalResolution (op ⦋0⦌) 1 1 1

/--
The specified degree-zero coefficient tensor is nonzero before taking homology.
-/
theorem literalZeroTensor_ne_zero : literalZeroTensor ≠ 0 := by
  intro h
  have hc := congrArg
    (CommAlgCat.CotangentPushout.zeroCoefficientLevelLinearEquiv ℤ ℤ originalAlgebra
      originalCoefficient canonicalResolution (op ⦋0⦌)) h
  rw [literalZeroTensor_raw_value, map_zero] at hc
  exact one_ne_zero hc

/--
The linear map multiplying by four in the scalar-change target ring.
-/
def targetFourMap : ActualTarget →ₗ[ActualTarget] ActualTarget :=
  LinearMap.lsmul ActualTarget ActualTarget (4 : ActualTarget)

/--
Multiplication by four is injective in the target ring identified with `ℤ`.
-/
theorem targetFourMap_injective : Function.Injective targetFourMap := by
  intro x y h
  change (4 : ActualTarget) * x = 4 * y at h
  apply targetIntegerEquiv.injective
  have hi := congrArg targetIntegerEquiv h
  have h4 : (4 : ℤ) * targetIntegerEquiv x = 4 * targetIntegerEquiv y := by
    simpa only [map_mul, map_ofNat] using hi
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

/--
Tensoring target-ring multiplication by four with the coefficient `ℤ/4ℤ`
sends the unit tensor to zero.
-/
theorem targetFourMap_unit_kernel :
    targetFourMap.rTensor (ZMod 4)
      ((1 : ActualTarget) ⊗ₜ[ActualTarget] (1 : ZMod 4)) = 0 := by
  change ((4 : ActualTarget) * 1) ⊗ₜ[ActualTarget] (1 : ZMod 4) = 0
  rw [mul_one]
  have hbalance : (4 : ActualTarget) ⊗ₜ[ActualTarget] (1 : ZMod 4) =
      (1 : ActualTarget) ⊗ₜ[ActualTarget] ((4 : ActualTarget) • (1 : ZMod 4)) := by
    simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h4 : (4 : ActualTarget) • (1 : ZMod 4) = 0 := by
    change coefficientRingMap (4 : ActualTarget) * (1 : ZMod 4) = 0
    rw [map_ofNat]
    decide
  rw [hbalance, h4, TensorProduct.tmul_zero]

/--
The coefficient module `ℤ/4ℤ` is not flat over the target ring.
-/
theorem originalCoefficient_not_flat : ¬ Module.Flat ActualTarget (ZMod 4) := by
  intro h
  letI : Module.Flat ActualTarget (ZMod 4) := h
  have hi := Module.Flat.rTensor_preserves_injective_linearMap
    (M := ZMod 4) targetFourMap targetFourMap_injective
  have ht : ((1 : ActualTarget) ⊗ₜ[ActualTarget] (1 : ZMod 4)) = 0 :=
    hi (by rw [targetFourMap_unit_kernel, map_zero])
  have hv := congrArg (TensorProduct.lid ActualTarget (ZMod 4)) ht
  have h1 : (1 : ZMod 4) = 0 := by
    simpa only [TensorProduct.lid_tmul, one_smul, map_zero] using hv
  exact one_ne_zero h1

/--
For every higher-form weight, the two coefficient models tensoring after
normalization are chain homotopy equivalent with the same lower-universe
coefficient module.
-/
def allWeightTransport (n : ℕ) :
    HomotopyEquiv
      (CommAlgCat.CotangentPushout.sourceCoefficientMappedNormalized ℤ ℤ originalAlgebra
        originalCoefficient n canonicalResolution)
      (CommAlgCat.CotangentPushout.targetCoefficientMappedNormalized ℤ ℤ originalAlgebra
        originalCoefficient n canonicalResolution) :=
  CommAlgCat.CotangentPushout.coefficientMappedNormalizedHomotopyEquiv ℤ ℤ
    originalAlgebra originalCoefficient n canonicalResolution

/--
The weight-zero, degree-zero homology of the coefficient diagram is nontrivial.
-/
theorem originalZeroHomology_nontrivial :
    Nontrivial ((CommAlgCat.CotangentPushout.sourceCoefficientNormalizedDiagram ℤ ℤ
      originalAlgebra originalCoefficient 0 canonicalResolution).homology 0) := by
  let e := CommAlgCat.CotangentPushout.zeroCoefficientHomologyLinearEquiv ℤ ℤ
    originalAlgebra originalCoefficient canonicalResolution
  refine ⟨⟨e.symm 1, e.symm 0, ?_⟩⟩
  intro h
  have hc := congrArg e h
  simp only [LinearEquiv.apply_symm_apply] at hc
  exact one_ne_zero hc

end MathlibExtTest.CotangentPushout.IndependentCoefficient

end
