/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientBoundary

/-!
# Naturality of the coefficient boundary and exterior insertion

Let R be commutative, L an R-Lie algebra and f : M → N a coefficient Lie-module morphism. The
tensor map F = id_(ExteriorAlgebra R L) ⊗ f intertwines the diagonal actions and the CE
coefficient boundaries. The diagonal action on a ⊗ m is ad_x(a) ⊗ m + a ⊗ ⁅x,m⁆.

Exterior insertion I_x(a ⊗ m) = (ι(x) * a) ⊗ m commutes with every R-linear coefficient map,
without requiring a Lie action on M or N. Both the operator equalities and their pointwise
forms are recorded; the coefficient carriers may have different universes.
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

/-- Let R be a commutative ring, L an R-Lie algebra and M and N R-modules. Put E = ExteriorAlgebra
R L. Assume M and N are left Lie modules over L and f : M →ₗ⁅R,L⁆ N is a Lie-module morphism.
Write F = id_E ⊗ f. For x : L, F ∘ coefficientDiagonalAction_M(x) =
coefficientDiagonalAction_N(x) ∘ F as R-linear maps E ⊗[R] M → E ⊗[R] N. Each diagonal action
combines the exterior adjoint action with the coefficient Lie action. -/
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

/-- Let R be a commutative ring, L an R-Lie algebra and M and N R-modules. Put E = ExteriorAlgebra
R L. Assume M and N are left Lie modules over L and f : M →ₗ⁅R,L⁆ N is a Lie-module morphism.
Write F = id_E ⊗ f. For x : L and p : E ⊗[R] M, F(coefficientDiagonalAction_M(x)(p)) =
coefficientDiagonalAction_N(x)(F(p)). -/
theorem coefficientDiagonalAction_naturality_apply
    (f : M →ₗ⁅R,L⁆ N) (x : L) (p : E ⊗[R] M) :
    TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap
        (coefficientDiagonalAction R L M x p) =
      coefficientDiagonalAction R L N x
        (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap p) :=
  LinearMap.congr_fun (coefficientDiagonalAction_naturality R L M f x) p

end LieCoefficients

/-- Let R be a commutative ring, L an R-Lie algebra and M and N R-modules. Put E = ExteriorAlgebra
R L. For any f : M →ₗ[R] N and x : L, F = id_E ⊗ f satisfies F ∘ coefficientInsertion_M(x) =
coefficientInsertion_N(x) ∘ F. Insertion is left multiplication by ι(x) on the exterior
factor; no Lie action on the coefficient modules is required. -/
theorem coefficientInsertion_naturality
    (f : M →ₗ[R] N) (x : L) :
    (f.lTensor E).comp (coefficientInsertion R L M x) =
      (coefficientInsertion R L N x).comp (f.lTensor E) := by
  let A : Module.End R E := (Algebra.lmul R E) (ExteriorAlgebra.ι R x)
  change (f.lTensor E).comp (A.rTensor M) =
    (A.rTensor N).comp (f.lTensor E)
  exact (LinearMap.lTensor_comp_rTensor E A f).trans
    (LinearMap.rTensor_comp_lTensor E A f).symm

/-- Let R be a commutative ring, L an R-Lie algebra and M and N R-modules. Put E = ExteriorAlgebra
R L. For an R-linear f : M →ₗ[R] N, x : L and p : E ⊗[R] M, (id_E ⊗
f)(coefficientInsertion_M(x)(p)) = coefficientInsertion_N(x)((id_E ⊗ f)(p)). -/
theorem coefficientInsertion_naturality_apply
    (f : M →ₗ[R] N) (x : L) (p : E ⊗[R] M) :
    f.lTensor E (coefficientInsertion R L M x p) =
      coefficientInsertion R L N x
        (f.lTensor E p) :=
  LinearMap.congr_fun (coefficientInsertion_naturality R L M f x) p

section LieCoefficients

variable [LieRingModule L M] [LieModule R L M]
variable [LieRingModule L N] [LieModule R L N]

/-- Let R be a commutative ring, L an R-Lie algebra and M and N R-modules. Put E = ExteriorAlgebra
R L. Assume M and N are left Lie modules over L and f : M →ₗ⁅R,L⁆ N is a Lie-module morphism.
Write F = id_E ⊗ f. The ambient coefficient boundaries satisfy F ∘ coefficientBoundary R L M =
coefficientBoundary R L N ∘ F on E ⊗[R] M. -/
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

/-- Let R be a commutative ring, L an R-Lie algebra and M and N R-modules. Put E = ExteriorAlgebra
R L. Assume M and N are left Lie modules over L and f : M →ₗ⁅R,L⁆ N is a Lie-module morphism.
Write F = id_E ⊗ f. For every p : E ⊗[R] M, F(coefficientBoundary R L M p) =
coefficientBoundary R L N (F(p)). -/
theorem coefficientBoundary_naturality_apply
    (f : M →ₗ⁅R,L⁆ N) (p : E ⊗[R] M) :
    TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap
        (coefficientBoundary R L M p) =
      coefficientBoundary R L N
        (TensorProduct.map (LinearMap.id : E →ₗ[R] E) f.toLinearMap p) :=
  LinearMap.congr_fun (coefficientBoundary_naturality R L M f) p

end LieCoefficients

end ChevalleyEilenberg
