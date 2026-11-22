/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorHom
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
The full parametrized adjunction for the existing noncommutative module
tensor, and its existing Leibniz pushout/pullback adjunction. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

omit [HasColimitsOfSize.{0, 0} C] in
/-- The actual ordinary internal-Hom precomposition retains the original right coefficient map. -/
theorem homPre_evaluation {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    (N.X ◁ (MonoidalClosed.pre f.hom).app X) ≫ baseEvaluation N X =
      (f.hom ▷ ((ihom N'.X).obj X)) ≫ baseEvaluation N' X :=
  MonoidalClosed.id_tensor_pre_app_comp_ev f.hom X

omit [HasColimitsOfSize.{0, 0} C] in
/-- Right coefficient linearity gives left scalar linearity of the same internal-Hom pre-map. -/
theorem homPre_linear {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    (A ◁ (MonoidalClosed.pre f.hom).app X) ≫ (homObject N X).mod.smul =
      (homObject N' X).mod.smul ≫ (MonoidalClosed.pre f.hom).app X := by
  apply MonoidalClosed.uncurry_injective (A := N.X)
  change MonoidalClosed.uncurry
      ((A ◁ (MonoidalClosed.pre f.hom).app X) ≫ homAction N X) =
    MonoidalClosed.uncurry (homAction N' X ≫ (MonoidalClosed.pre f.hom).app X)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  change (N.X ◁ (A ◁ (MonoidalClosed.pre f.hom).app X)) ≫
      (N.X ◁ homAction N X) ≫ baseEvaluation N X =
    (f.hom ▷ (A ⊗ ((ihom N'.X).obj X))) ≫
      ((N'.X ◁ homAction N' X) ≫ baseEvaluation N' X)
  simp only [homAction_evaluation]
  unfold homActionPairing
  rw [← Category.assoc,
    monadicAction_naturality N ((MonoidalClosed.pre f.hom).app X), Category.assoc,
    homPre_evaluation]
  rw [← Category.assoc (f.hom ▷ (A ⊗ ((ihom N'.X).obj X)))
      (monadicAction N' ((ihom N'.X).obj X)), monadicAction_map]
  simp only [monadicAction, Category.assoc]

/-- Precomposition is an actual left A-module map, with the unmodified carrier map. -/
def homPre {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    homObject N' X ⟶ homObject N X :=
  Mod.Hom.mk' ((MonoidalClosed.pre f.hom).app X) (homPre_linear f X).symm

omit [HasColimitsOfSize.{0, 0} C] in
theorem homPre_carrier {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    (homPre f X).hom = (MonoidalClosed.pre f.hom).app X := rfl

/-- Naturality of coefficient precomposition in the original internal Hom. -/
def homPreNatural {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    homFunctor N' ⟶ homFunctor N where
  app := homPre f
  naturality X Y g := by
    apply Mod.hom_ext
    change (ihom N'.X).map g ≫ (MonoidalClosed.pre f.hom).app Y =
      (MonoidalClosed.pre f.hom).app X ≫ (ihom N.X).map g
    exact (MonoidalClosed.pre f.hom).naturality g

/-- The original right coefficient category acts contravariantly on the actual Hom modules. -/
def homContravariant : (RightModuleFree.Carrier A)ᵒᵖ ⥤ C ⥤ Mod C A where
  obj N := homFunctor N.unop
  map f := homPreNatural f.unop
  map_id N := by
    ext X
    change (MonoidalClosed.pre (𝟙 N.unop.X)).app X = 𝟙 _
    rw [MonoidalClosed.pre_id]
    rfl
  map_comp f g := by
    ext X
    change (MonoidalClosed.pre (g.unop.hom ≫ f.unop.hom)).app X =
      (MonoidalClosed.pre f.unop.hom).app X ≫ (MonoidalClosed.pre g.unop.hom).app X
    rw [MonoidalClosed.pre_map]
    rfl

/-- The existing two-variable tensor maps form their entire ordinary curried functor. -/
def tensorCurried : RightModuleFree.Carrier A ⥤ Mod C A ⥤ C where
  obj := leftTensorFunctor
  map := leftTensorNatural
  map_id N := by
    ext M
    exact tensorMap_id N M
  map_comp f g := by
    ext M
    change tensorMap (f ≫ g) (𝟙 M) = tensorMap f (𝟙 M) ≫ tensorMap g (𝟙 M)
    simpa only [Category.id_comp] using tensorMap_comp f g (𝟙 M) (𝟙 M)

/-- Currying the original quotient naturality gives the full coefficient naturality of the adjunct. -/
def tensorHomParametrized : tensorCurried (A := A) ⊣₂ homContravariant (A := A) :=
  ParametrizedAdjunction.mk' tensorHomAdjunction (by
    intro N N' f M X g
    let g₀ : tensorObject N' M ⟶ X := g
    apply Mod.hom_ext
    change (((tensorHomAdjunction N).homEquiv M X) (tensorMap f (𝟙 M) ≫ g₀)).hom =
      (((tensorHomAdjunction N').homEquiv M X) g₀).hom ≫ (MonoidalClosed.pre f.hom).app X
    rw [tensorHomAdjunction_forward, tensorHomAdjunction_forward]
    change MonoidalClosed.curry (projection N M ≫ (tensorMap f (𝟙 M) ≫ g₀)) =
      MonoidalClosed.curry (projection N' M ≫ g₀) ≫ (MonoidalClosed.pre f.hom).app X
    have h : projection N M ≫ tensorMap f (𝟙 M) = (f.hom ▷ M.X) ≫ projection N' M :=
      rightTensorFunctor_projection M f
    rw [MonoidalClosed.curry_pre_app, ← Category.assoc, h, Category.assoc])

/-- Relative Leibniz pushouts use the existing generic pushout construction on the actual tensor. -/
abbrev relativePushoutProduct :
    Arrow (RightModuleFree.Carrier A) ⥤ Arrow (Mod C A) ⥤ Arrow C :=
  (tensorCurried (A := A)).leibnizPushout

section Pullbacks

variable [HasPullbacks (Mod C A)]

/-- The original two-variable adjunction gives the complete relative Leibniz adjunction. -/
def relativePushoutAdjunction (f : Arrow (RightModuleFree.Carrier A)) :
    (relativePushoutProduct (A := A)).obj f ⊣
      (homContravariant (A := A)).leibnizPullback.obj (op f) :=
  Functor.LeibnizAdjunction.adj (tensorCurried (A := A)) (homContravariant (A := A))
    tensorHomParametrized f

/-- All original source colimits are preserved by this actual relative corner functor. -/
theorem relativePushoutProduct_preservesColimits (f : Arrow (RightModuleFree.Carrier A)) :
    PreservesColimitsOfSize.{w', w} ((relativePushoutProduct (A := A)).obj f) :=
  (relativePushoutAdjunction f).leftAdjoint_preservesColimits

end Pullbacks
end CategoryTheory.Mod.RightLeftTensor
