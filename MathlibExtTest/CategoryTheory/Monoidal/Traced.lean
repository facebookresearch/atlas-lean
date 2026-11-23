/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.Traced
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe v u
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [RightRigidCategory C]

-- Right duals suffice; no left-dual or additional trace assumptions are needed.
example : SymmetricTrace C := symmetricTraceOfRigid C

example (X : C) : (symmetricTraceOfRigid C).trace (β_ X X).hom = 𝟙 X :=
  (symmetricTraceOfRigid C).yanking X

-- Inserting and then tracing a unit wire recovers the original morphism.
example {X Y : C} (f : X ⟶ Y) :
    (symmetricTraceOfRigid C).trace ((ρ_ X).hom ≫ f ≫ (ρ_ Y).inv) = f := by
  rw [(symmetricTraceOfRigid C).vanishing_unit]
  simp

-- A separately supplied dual/pairing gives the same feedback operation.
example {X Y U D : C} [ExactPairing U D] (f : X ⊗ U ⟶ Y ⊗ U) :
    (symmetricTraceOfRigid C).trace f = SymmetricTrace.traceOfPairing D f :=
  SymmetricTrace.traceOfPairing_independent f

-- The construction works in a concrete nontrivial linear category.
example : SymmetricTrace (FGModuleCat ℚ) := symmetricTraceOfRigid (FGModuleCat ℚ)

-- Zero linear maps have zero partial trace, directly from the constructed operation.
example (X Y U : FGModuleCat ℚ) :
    SymmetricTrace.traceOfPairing (Uᘁ) (0 : X ⊗ U ⟶ Y ⊗ U) = 0 := by
  simp [SymmetricTrace.traceOfPairing]

-- For finite-dimensional vector spaces, the trace of identity is dimension.
example (U : FGModuleCat ℚ) :
    (SymmetricTrace.traceOfPairing (Uᘁ)
      (𝟙 (𝟙_ (FGModuleCat ℚ) ⊗ U))).hom.hom (1 : ℚ) = (Module.finrank ℚ U : ℚ) := by
  have h : SymmetricTrace.traceOfPairing (Uᘁ)
      (𝟙 (𝟙_ (FGModuleCat ℚ) ⊗ U)) =
      η_ U (Uᘁ) ≫ (β_ U (Uᘁ)).hom ≫ ε_ U (Uᘁ) := by
    unfold SymmetricTrace.traceOfPairing
    monoidal
  rw [h]
  change (contractLeft ℚ U)
    ((TensorProduct.comm ℚ U (Module.Dual ℚ U)) (coevaluation ℚ U 1)) = _
  classical
  rw [coevaluation_apply_one]
  simp only [map_sum, TensorProduct.comm_tmul, contractLeft_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast (Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℚ U)).symm

#print axioms CategoryTheory.symmetricTraceOfRigid
