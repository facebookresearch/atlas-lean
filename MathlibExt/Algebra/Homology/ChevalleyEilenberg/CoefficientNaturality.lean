/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientBoundary

/-!
# Coefficient naturality of the Chevalley–Eilenberg boundary

A Lie-module homomorphism induces the tensor map that is the identity on the
exterior factor. It commutes with the diagonal action, exterior insertion,
and the coefficient boundary. Exterior insertion also commutes with arbitrary
linear coefficient maps, independently of any Lie actions.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w w'

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]
variable {N : Type w'} [AddCommGroup N] [Module R N]

local notation "E" => ExteriorAlgebra R L

section LieCoefficients

variable [LieRingModule L M] [LieModule R L M]
variable [LieRingModule L N] [LieModule R L N]

/-- The canonical diagonal actions commute with a morphism of coefficient
Lie modules. -/
theorem coefficientDiagonalAction_naturality
    (f : M →ₗ⁅R,L⁆ N) (x : L) :
    (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap).comp
        (coefficientDiagonalAction R L M x) =
      (coefficientDiagonalAction R L N x).comp
        (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientDiagonalAction_tmul, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply, LieModuleHom.coe_toLinearMap,
    LieModuleHom.map_lie]

/-- Pointwise coefficient naturality of the canonical diagonal action. -/
theorem coefficientDiagonalAction_naturality_apply
    (f : M →ₗ⁅R,L⁆ N) (x : L) (p : E ⊗[R] M) :
    TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap
        (coefficientDiagonalAction R L M x p) =
      coefficientDiagonalAction R L N x
        (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap p) :=
  LinearMap.congr_fun (coefficientDiagonalAction_naturality R L M f x) p

end LieCoefficients

/-- Exterior insertion commutes with every linear map on the coefficient modules. -/
theorem coefficientInsertion_naturality
    (f : M →ₗ[R] N) (x : L) :
    (f.lTensor E).comp (coefficientInsertion R L M x) =
      (coefficientInsertion R L N x).comp (f.lTensor E) := by
  let A : Module.End R E := (Algebra.lmul R E) (ExteriorAlgebra.ι R x)
  change (f.lTensor E).comp (A.rTensor M) =
    (A.rTensor N).comp (f.lTensor E)
  exact (LinearMap.lTensor_comp_rTensor E A f).trans
    (LinearMap.rTensor_comp_lTensor E A f).symm

/-- Pointwise naturality of exterior insertion for arbitrary linear coefficient maps. -/
theorem coefficientInsertion_naturality_apply
    (f : M →ₗ[R] N) (x : L) (p : E ⊗[R] M) :
    f.lTensor E (coefficientInsertion R L M x p) =
      coefficientInsertion R L N x
        (f.lTensor E p) :=
  LinearMap.congr_fun (coefficientInsertion_naturality R L M f x) p

section LieCoefficients

variable [LieRingModule L M] [LieModule R L M]
variable [LieRingModule L N] [LieModule R L N]

/-- The ambient Chevalley--Eilenberg boundary is natural in its native left
Lie-module coefficients. -/
theorem coefficientBoundary_naturality (f : M →ₗ⁅R,L⁆ N) :
    (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap).comp
        (coefficientBoundary R L M) =
      (coefficientBoundary R L N).comp
        (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [coefficientBoundary_algebraMap_tmul, map_zero,
        coefficientBoundary_algebraMap_tmul]
  | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | ι_mul a x ha =>
      rw [coefficientBoundary_ι_mul_tmul, map_sub, map_neg,
        coefficientDiagonalAction_naturality_apply]
      simp only [← LinearMap.lTensor_def] at ha ⊢
      rw [coefficientInsertion_naturality_apply R L M f.toLinearMap, ha,
        LinearMap.lTensor_tmul,
        coefficientBoundary_ι_mul_tmul]

/-- Pointwise naturality of the ambient boundary in its coefficients. -/
theorem coefficientBoundary_naturality_apply
    (f : M →ₗ⁅R,L⁆ N) (p : E ⊗[R] M) :
    TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap
        (coefficientBoundary R L M p) =
      coefficientBoundary R L N
        (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap p) :=
  LinearMap.congr_fun (coefficientBoundary_naturality R L M f) p

end LieCoefficients

end ChevalleyEilenberg
