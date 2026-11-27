/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Coefficients
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.AdditiveNormalization
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Polynomial differentials over flat and nonflat integer extensions

For `A = ℤ[X]` and any nontrivial commutative `ℤ`-algebra `S`, the tensor
`1 ⊗ (1 ⊗ dX)` has coordinate one after differential scalar change to `S[X]`,
and is nonzero before comparison. The examples use the flat extension `ℤ[T]`
and the nonflat extension `ℤ/4ℤ`.

Nonflatness is witnessed by injective integer multiplication by four becoming
noninjective after tensoring with `ℤ/4ℤ`: the unit tensor is nonzero and maps
to zero. The same nonflat extension is also used in the all-weight normalized
comparison of the canonical polynomial model.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe v

namespace MathlibExtTest.CotangentPushout

/--
The one-variable polynomial algebra `ℤ[X]`.
-/
abbrev IntegerPolynomial := MvPolynomial (Fin 1) ℤ
/--
The one-variable polynomial algebra `S[X]` over a commutative ring `S`.
-/
abbrev ChangedPolynomial (S : Type v) [CommRing S] := MvPolynomial (Fin 1) S

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (S : Type v) [CommRing S] [Algebra ℤ S] [Nontrivial S]

/--
For the nontrivial commutative `ℤ`-algebra `S`, the tensor
`1_(S[X]) ⊗ (1_(ℤ[X]) ⊗ dX)` before applying the differential pushout equivalence.
-/
def originalDifferentialTensor :
    ChangedPolynomial S ⊗[IntegerPolynomial]
      KaehlerDifferential.Coefficient ℤ IntegerPolynomial IntegerPolynomial :=
  (1 : ChangedPolynomial S) ⊗ₜ[IntegerPolynomial]
    ((1 : IntegerPolynomial) ⊗ₜ[IntegerPolynomial]
      KaehlerDifferential.D ℤ IntegerPolynomial (MvPolynomial.X (0 : Fin 1)))

/--
The linear coordinate functional on differentials of `S[X]` that reads the
coefficient of the basis differential `dX`.
-/
def differentialCoordinate :
    KaehlerDifferential.Coefficient S (ChangedPolynomial S) (ChangedPolynomial S) →ₗ[
      ChangedPolynomial S] ChangedPolynomial S :=
  (Finsupp.lapply (0 : Fin 1)).comp
    ((KaehlerDifferential.mvPolynomialBasis S (Fin 1)).repr.toLinearMap.comp
      (TensorProduct.lid (ChangedPolynomial S)
        (KaehlerDifferential S (ChangedPolynomial S))).toLinearMap)

/--
The differential pushout sends the specified tensor to an element whose `dX`
coordinate is one.
-/
theorem originalDifferentialTensor_coordinate :
    differentialCoordinate S
        (KaehlerDifferential.coefficientPushoutEquiv ℤ S IntegerPolynomial
          (ChangedPolynomial S) IntegerPolynomial (ChangedPolynomial S)
            (originalDifferentialTensor S)) = 1 := by
  rw [originalDifferentialTensor, KaehlerDifferential.coefficientPushoutEquiv_tmul_D,
    map_one, mul_one]
  change differentialCoordinate S ((1 : ChangedPolynomial S) ⊗ₜ[ChangedPolynomial S]
    KaehlerDifferential.D S (ChangedPolynomial S)
      (MvPolynomial.map (algebraMap ℤ S) (MvPolynomial.X (0 : Fin 1)))) = 1
  rw [MvPolynomial.map_X]
  simp [differentialCoordinate, KaehlerDifferential.mvPolynomialBasis_repr_D_X]

/--
The specified differential tensor is nonzero for every nontrivial commutative
`ℤ`-algebra `S`.
-/
theorem originalDifferentialTensor_ne_zero : originalDifferentialTensor S ≠ 0 := by
  intro h
  have hc : differentialCoordinate S
      (KaehlerDifferential.coefficientPushoutEquiv ℤ S IntegerPolynomial
        (ChangedPolynomial S) IntegerPolynomial (ChangedPolynomial S)
          (originalDifferentialTensor S)) = 0 := by
    rw [h, map_zero, map_zero]
  exact one_ne_zero ((originalDifferentialTensor_coordinate S).symm.trans hc)

/--
The one-variable integer polynomial ring used as a flat ground extension.
-/
abbrev FlatGround := MvPolynomial (Fin 1) ℤ

/--
The integer polynomial ground extension is flat as a `ℤ`-module.
-/
theorem flatGround_flat : Module.Flat ℤ FlatGround := inferInstance

/--
The specified polynomial differential tensor is nonzero over the flat
polynomial ground extension.
-/
theorem flatGround_tensor_ne_zero : originalDifferentialTensor FlatGround ≠ 0 :=
  originalDifferentialTensor_ne_zero FlatGround

/--
The `ℤ`-linear map `z ↦ 4z` on the integers.
-/
def integerFourMap : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ (4 : ℤ)

/--
Multiplication by four is injective on `ℤ`.
-/
theorem integerFourMap_injective : Function.Injective integerFourMap := by
  intro x y h
  change (4 : ℤ) * x = 4 * y at h
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h

/--
The tensor `1_ℤ ⊗[ℤ] 1_(ℤ/4ℤ)` is nonzero.
-/
theorem nonflatUnitTensor_ne_zero :
    ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 4)) ≠ 0 := by
  intro h
  have hc := congrArg (TensorProduct.lid ℤ (ZMod 4)) h
  have h1 : (1 : ZMod 4) = 0 := by
    simpa only [TensorProduct.lid_tmul, one_smul, map_zero] using hc
  exact one_ne_zero h1

/--
Tensoring integer multiplication by four on the right with `ℤ/4ℤ` sends the
specified nonzero unit tensor to zero.
-/
theorem nonflatFourMap_unit_kernel :
    integerFourMap.rTensor (ZMod 4) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 4)) = 0 := by
  change ((4 : ℤ) * 1) ⊗ₜ[ℤ] (1 : ZMod 4) = 0
  rw [mul_one]
  have hbalance : (4 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 4) =
      (1 : ℤ) ⊗ₜ[ℤ] ((4 : ℤ) • (1 : ZMod 4)) := by
    simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hbalance, show (4 : ℤ) • (1 : ZMod 4) = 0 by decide, TensorProduct.tmul_zero]

/--
The `ℤ`-module `ℤ/4ℤ` is not flat, as witnessed by the tensor kernel of the
injective multiplication-by-four map.
-/
theorem nonflatGround_not_flat : ¬ Module.Flat ℤ (ZMod 4) := by
  intro h
  letI : Module.Flat ℤ (ZMod 4) := h
  have hi := Module.Flat.rTensor_preserves_injective_linearMap
    (M := ZMod 4) integerFourMap integerFourMap_injective
  have h0 : ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 4)) = 0 :=
    hi (by rw [nonflatFourMap_unit_kernel, map_zero])
  exact nonflatUnitTensor_ne_zero h0

/--
The specified polynomial differential tensor remains nonzero over `ℤ/4ℤ`.
-/
theorem nonflatGround_tensor_ne_zero : originalDifferentialTensor (ZMod 4) ≠ 0 :=
  originalDifferentialTensor_ne_zero (ZMod 4)

/--
The commutative algebra object representing `ℤ[X]` in universe zero.
-/
def integerPolynomialAlgebra : CommAlgCat.{0} ℤ := CommAlgCat.of ℤ IntegerPolynomial

/--
The canonical augmented polynomial resolution of the integer polynomial algebra.
-/
def originalCanonicalResolution :
    Over ((SimplicialObject.const (CommAlgCat.{0} ℤ)).obj integerPolynomialAlgebra) :=
  (CommAlgCat.polynomialResolutionOverFunctor ℤ integerPolynomialAlgebra).obj
    (Over.mk (𝟙 integerPolynomialAlgebra))

/--
For every higher-form weight, the scalar-extended normalized canonical model is
chain homotopy equivalent to the normalized scalar-changed model over `ℤ/4ℤ`.
-/
def nonflatCanonicalModelTransport (n : ℕ) :
    HomotopyEquiv
      ((CommAlgCat.CotangentPushout.mappedNormalizedFunctor ℤ (ZMod 4)
        integerPolynomialAlgebra n).obj originalCanonicalResolution)
      ((CommAlgCat.CotangentPushout.targetNormalizedFunctor ℤ (ZMod 4)
        integerPolynomialAlgebra n).obj originalCanonicalResolution) :=
  CommAlgCat.CotangentPushout.normalizedHomotopyEquiv ℤ (ZMod 4)
    integerPolynomialAlgebra n originalCanonicalResolution

/--
For every higher-form weight, the scalar-extended normalized canonical model
and the normalized scalar-changed model over `ℤ/4ℤ` are isomorphic.
-/
def nonflatCanonicalModelNormalizationIso (n : ℕ) :
    ((CommAlgCat.CotangentPushout.mappedNormalizedFunctor ℤ (ZMod 4)
      integerPolynomialAlgebra n).obj originalCanonicalResolution) ≅
    ((CommAlgCat.CotangentPushout.targetNormalizedFunctor ℤ (ZMod 4)
      integerPolynomialAlgebra n).obj originalCanonicalResolution) :=
  CommAlgCat.CotangentPushout.normalizedPushoutIso ℤ (ZMod 4)
    integerPolynomialAlgebra n originalCanonicalResolution

end MathlibExtTest.CotangentPushout

end
