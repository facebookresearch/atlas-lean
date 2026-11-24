/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Basic

/-!
# Degeneracies in coefficient Hochschild coordinates

The monadic coefficient bar induces degeneracy maps on the
coefficient tensor levels. Each map inserts the algebra unit at
its specified tensor position, with independent carrier universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial ModuleCat.Algebra

universe u v w

namespace ModuleCat.Algebra.Hochschild

attribute [local instance] uliftSMulCommClass

variable (k : Type u) (A : Type v) (M : Type w)
  [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M]
  [Module A M] [Module Aᵐᵒᵖ M] [Module k M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- The unit degeneracy transported to the literal tensor levels. -/
def degeneracy (n : ℕ) (i : Fin (n + 1)) :
    chainLevel k A M n ⟶ chainLevel k A M (n + 1) :=
  (coefficientBarObjIso k A M n).inv ≫ (coefficientBar k A M).σ i ≫
    (coefficientBarObjIso k A M (n + 1)).hom

/-- Native degeneracy inserts the unit into the tensor tuple and leaves
the coefficient unchanged. -/
theorem degeneracy_tprod (n : ℕ) (i : Fin (n + 1)) (m : M) (a : Fin n → A) :
    (degeneracy k A M n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildInsertOne i a) := by
  change TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k (n + 1) A))
      ((barObjIso k A (ULift.{max u v w} M) (n + 1)).hom.hom
        (((barK k A (ULift.{max u v w} M)).σ i).hom
          ((barObjIso k A (ULift.{max u v w} M) n).inv.hom
            (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)))) = _
  exact (congrArg
    (TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k (n + 1) A)))
    (bar_degen_insert k A (ULift.{max u v w} M) n i (ULift.up m) a)).trans (by rfl)

/-- Primitive components of the comparison to the native bar complex. -/
theorem chainComplexIso_hom_f (n : ℕ) :
    (chainComplexIso k A M).hom.f n = (coefficientBarObjIso k A M n).inv := rfl

/-- Primitive inverse components of the native bar-complex comparison. -/
theorem chainComplexIso_inv_f (n : ℕ) :
    (chainComplexIso k A M).inv.f n = (coefficientBarObjIso k A M n).hom := rfl

end ModuleCat.Algebra.Hochschild
