/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.UnderFunctorialFactorization

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory.MorphismProperty.UnderFunctorialFactorizationTests

variable {C : Type u} [Category.{v} C]
variable (S : C) {W₁ W₂ : MorphismProperty C}
variable (data : FunctorialFactorizationData W₁ W₂)

#check FunctorialFactorizationData.under

example : FunctorialFactorizationData
    (W₁.under (X := S)) (W₂.under (X := S)) :=
  data.under S

section Objects

variable {X Y : Under S} (f : X ⟶ Y)

example : ((data.under S).factorizationData f).Z.right =
    (data.factorizationData f.right).Z := rfl

example : ((data.under S).factorizationData f).Z.hom =
    X.hom ≫ (data.factorizationData f.right).i := rfl

example : ((data.under S).factorizationData f).i.right =
    (data.factorizationData f.right).i := rfl

example : ((data.under S).factorizationData f).p.right =
    (data.factorizationData f.right).p := rfl

example : ((data.under S).factorizationData f).i ≫
    ((data.under S).factorizationData f).p = f :=
  (data.under S).fac_app

example : W₁ ((data.under S).factorizationData f).i.right :=
  (data.under S).hi _

example : W₂ ((data.under S).factorizationData f).p.right :=
  (data.under S).hp _

end Objects

section Maps

variable {X Y X' Y' X'' Y'' : Under S}
variable {f : X ⟶ Y} {g : X' ⟶ Y'} {h : X'' ⟶ Y''}
variable (φ : CategoryTheory.Arrow.mk f ⟶ CategoryTheory.Arrow.mk g)
variable (ψ : CategoryTheory.Arrow.mk g ⟶ CategoryTheory.Arrow.mk h)

example : ((data.under S).mapZ φ).right =
    data.mapZ (CategoryTheory.Arrow.homMk φ.left.right φ.right.right
      (congrArg CommaMorphism.right φ.w)) := rfl

example : ((data.under S).factorizationData f).Z.hom ≫
    ((data.under S).mapZ φ).right =
      ((data.under S).factorizationData g).Z.hom :=
  CategoryTheory.Under.w ((data.under S).mapZ φ)

example : (data.under S).mapZ (𝟙 (CategoryTheory.Arrow.mk f)) = 𝟙 _ :=
  (data.under S).mapZ_id f

example : (data.under S).mapZ (φ ≫ ψ) =
    (data.under S).mapZ φ ≫ (data.under S).mapZ ψ :=
  (data.under S).mapZ_comp φ ψ

example : φ.left ≫ (data.under S).i.app (CategoryTheory.Arrow.mk g) =
    (data.under S).i.app (CategoryTheory.Arrow.mk f) ≫
      (data.under S).mapZ φ :=
  (data.under S).i.naturality φ

example : (data.under S).mapZ φ ≫
    (data.under S).p.app (CategoryTheory.Arrow.mk g) =
      (data.under S).p.app (CategoryTheory.Arrow.mk f) ≫ φ.right :=
  (data.under S).p.naturality φ

end Maps

section ConditionalInstance

variable [HasFunctorialFactorization W₁ W₂]

#synth HasFunctorialFactorization
  (W₁.under (X := S)) (W₂.under (X := S))

example : FunctorialFactorizationData
    (W₁.under (X := S)) (W₂.under (X := S)) :=
  functorialFactorizationData _ _

end ConditionalInstance

section ExistingDictionaries

variable [HomotopicalAlgebra.ModelCategory C]

example : (inferInstance : HomotopicalAlgebra.ModelCategory (Under S)) =
    HomotopicalAlgebra.ModelCategory.under S := rfl

end ExistingDictionaries

section ExistingPerMapFactorization

variable [W₁.HasFactorization W₂]

#synth (W₁.under (X := S)).HasFactorization (W₂.under (X := S))

end ExistingPerMapFactorization

/-! The new instance is conditional on a base functorial factorization. -/

example (_W₁ _W₂ : MorphismProperty C) : True := by
  fail_if_success
    let _ : HasFunctorialFactorization
      (_W₁.under (X := S)) (_W₂.under (X := S)) := inferInstance
  trivial

/-! Explicit concrete universe clients. -/

section UniverseOne

variable {C₁ : Type 1} [Category.{0} C₁] (S₁ : C₁)
variable {P₁ P₂ : MorphismProperty C₁}

example (d : FunctorialFactorizationData P₁ P₂) :
    FunctorialFactorizationData
      (P₁.under (X := S₁)) (P₂.under (X := S₁)) :=
  d.under S₁

end UniverseOne

section UniverseZero

variable {C₀ : Type} [Category.{0} C₀] (S₀ : C₀)
variable {P₁ P₂ : MorphismProperty C₀}

example (d : FunctorialFactorizationData P₁ P₂) :
    FunctorialFactorizationData
      (P₁.under (X := S₀)) (P₂.under (X := S₀)) :=
  d.under S₀

end UniverseZero

/-! No second, pointed replacement construction is introduced. -/

example : True := by
  fail_if_success
    exact FunctorialFactorizationData.pointed
  fail_if_success
    exact HomotopicalAlgebra.pointedFunctorialFactorizationData
  trivial

#print axioms FunctorialFactorizationData.under
#print axioms CategoryTheory.MorphismProperty.instHasFunctorialFactorizationUnderUnder_mathlibExt

end CategoryTheory.MorphismProperty.UnderFunctorialFactorizationTests
