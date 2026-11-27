/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.FactorArrowFunctors
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# The entire original functorial factorization as two composable arrows

The supplied original Z/i/p and caller factorization determine a full functor
on all Arrows and all squares. Its three objects and two factor maps are the
original source, selected middle and target, with the exact caller composite.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty C}

/-- The complete original caller factorization is functorial as two composable arrows. -/
def originalFactorizationFunctor (data : FunctorialFactorizationData W₁ W₂) :
    Arrow C ⥤ ComposableArrows C 2 where
  obj a := mk₂ (data.i.app a) (data.p.app a)
  map φ := homMk₂ φ.left (data.Z.map φ) φ.right
    (data.i.naturality φ).symm (data.p.naturality φ).symm
  map_id a := by
    apply hom_ext₂
    · rfl
    · exact data.Z.map_id a
    · rfl
  map_comp φ ψ := by
    apply hom_ext₂
    · rfl
    · exact data.Z.map_comp φ ψ
    · rfl

/-- All three object fields retain the caller source, original selected middle and target. -/
theorem originalFactorizationFunctor_objects
    (data : FunctorialFactorizationData W₁ W₂) (a : Arrow C) :
    (data.originalFactorizationFunctor.obj a).obj' 0 = a.left ∧
      (data.originalFactorizationFunctor.obj a).obj' 1 = data.Z.obj a ∧
      (data.originalFactorizationFunctor.obj a).obj' 2 = a.right := ⟨rfl, rfl, rfl⟩

/-- Both maps of the complete factorization are exactly the supplied original i and p. -/
theorem originalFactorizationFunctor_factors
    (data : FunctorialFactorizationData W₁ W₂) (a : Arrow C) :
    (data.originalFactorizationFunctor.obj a).map' 0 1 = data.i.app a ∧
      (data.originalFactorizationFunctor.obj a).map' 1 2 = data.p.app a := ⟨rfl, rfl⟩

/-- The complete factorization has the exact same original caller composite. -/
theorem originalFactorizationFunctor_fac
    (data : FunctorialFactorizationData W₁ W₂) (a : Arrow C) :
    (data.originalFactorizationFunctor.obj a).hom = a.hom := data.fac_app

/-- Every arbitrary caller square retains its full source, selected middle and target maps. -/
theorem originalFactorizationFunctor_map_fields
    (data : FunctorialFactorizationData W₁ W₂) {a b : Arrow C} (φ : a ⟶ b) :
    (data.originalFactorizationFunctor.map φ).app 0 = φ.left ∧
      (data.originalFactorizationFunctor.map φ).app 1 = data.Z.map φ ∧
      (data.originalFactorizationFunctor.map φ).app 2 = φ.right := ⟨rfl, rfl, rfl⟩

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
