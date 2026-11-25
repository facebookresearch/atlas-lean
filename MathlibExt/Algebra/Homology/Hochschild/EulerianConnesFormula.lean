/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.NormalizedConnesFormula
public import MathlibExt.Algebra.Homology.Hochschild.NormalizedEulerianOperators
public import MathlibExt.LinearAlgebra.TensorPower.EulerianCyclicNormActions

/-!
# The dyadic convolution relation for normalized Connes B

Over a rational ground algebra, the signed norm and head-unit
insertion define regular
normalized Connes B. Cyclic descent-fiber counts intertwine
bar-lambda at parameter two with B by the scalar two.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]

local notation "Q" => ModuleCat.Algebra.Hochschild.quotientCarrier k A
local notation "q" => Submodule.mkQ (ModuleCat.Algebra.Hochschild.unitSubmodule k A)

/-- The regular normalized B and the convolution at two satisfy the scalar-two identity in every degree. -/
theorem normalizedConvolutionTwo_connesBoundary (n : ℕ) :
    (normalizedConvolutionOperator k A A (n + 1) 2).comp (NonUnital.normalizedBoundary k A n).hom =
      (2 : k) • (NonUnital.normalizedBoundary k A n).hom.comp
        (normalizedConvolutionOperator k A A n 2) := by
  rw [normalizedConnesBoundary_eq_formula]
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  change normalizedConvolutionOperator k A A (n + 1) 2
      (normalizedConnesFormula k A n (m ⊗ₜ[k] x)) =
    (2 : k) • normalizedConnesFormula k A n
      (normalizedConvolutionOperator k A A n 2 (m ⊗ₜ[k] x))
  simp only [normalizedConvolutionOperator, TensorPower.coefficientRationalPermutationAction_eq_map,
    normalizedConnesFormula, LinearMap.comp_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  have h := DFunLike.congr_fun
    (TensorPower.rationalEulerianLambda_two_cyclicNorm (k := k) (V := Q) n)
      (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] x))
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at h
  have hh := DFunLike.congr_fun
    (TensorPower.rationalPermutationAction_headFixing_cons (k := k) (V := Q) n
      (Equiv.Perm.eulerianLambda n 2)) (q m ⊗ₜ[k] x)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply] at hh
  change TensorPower.rationalPermutationAction (k := k) (V := Q) (n + 1)
      (Equiv.Perm.headFixingGroupRingMap ℚ n (Equiv.Perm.eulerianLambda n 2))
      (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] x)) =
    TensorPower.consEquiv k Q n (q m ⊗ₜ[k]
      TensorPower.rationalPermutationAction (k := k) (V := Q) n (Equiv.Perm.eulerianLambda n 2) x) at hh
  change TensorProduct.map LinearMap.id
      (TensorPower.rationalPermutationAction (k := k) (V := Q) (n + 1)
        (Equiv.Perm.eulerianLambda (n + 1) 2))
      ((1 : A) ⊗ₜ[k] TensorPower.norm k Q n (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] x))) =
    (2 : k) • ((1 : A) ⊗ₜ[k] TensorPower.norm k Q n
      (TensorPower.consEquiv k Q n (q m ⊗ₜ[k]
        TensorPower.rationalPermutationAction (k := k) (V := Q) n (Equiv.Perm.eulerianLambda n 2) x)))
  rw [TensorProduct.map_tmul, LinearMap.id_apply, h, hh]
  exact map_smul (TensorProduct.mk k A (TensorPower k (n + 1) Q) 1) (2 : k) _

end ModuleCat.Algebra.Hochschild.Symmetric
