/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorUniversal
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Relative tensor–Hom adjunction for modules

For a monoid object A in a monoidal closed category, the internal Hom from a right A-module
N carries a left A-action induced by the right action on N and evaluation. When C has the
required small colimits, the balanced tensor functor N ⊗[A] (-) is left adjoint to this
internal-Hom module functor and therefore preserves colimits. The adjunct maps are expressed
by the tensor quotient projection and ambient currying or uncurrying.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {A : C} [MonObj A]

/-- The monadic form of the original internal-Hom module action. -/
abbrev monadicAction (N : RightModuleFree.Carrier A) (X : C) :
    N.X ⊗ (A ⊗ X) ⟶ N.X ⊗ X := (α_ N.X A X).inv ≫ (rightAction N ▷ X)

omit [MonoidalClosed C] in
theorem monadicAction_unit (N : RightModuleFree.Carrier A) (X : C) :
    (N.X ◁ (Monad.tensorMonad A).η.app X) ≫ monadicAction N X = 𝟙 (N.X ⊗ X) :=
  Monad.RightModule.unit_app (rightMonad N) X

omit [MonoidalClosed C] in
theorem monadicAction_assoc (N : RightModuleFree.Carrier A) (X : C) :
    (N.X ◁ (Monad.tensorMonad A).μ.app X) ≫ monadicAction N X =
      monadicAction N (A ⊗ X) ≫ monadicAction N X :=
  Monad.RightModule.assoc_app (rightMonad N) X

omit [MonoidalClosed C] in
theorem monadicAction_naturality (N : RightModuleFree.Carrier A) {X Y : C} (f : X ⟶ Y) :
    (N.X ◁ (A ◁ f)) ≫ monadicAction N Y = monadicAction N X ≫ (N.X ◁ f) :=
  (rightMonad N).action.naturality f

omit [MonoidalClosed C] in
theorem monadicAction_map {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    (f.hom ▷ (A ⊗ X)) ≫ monadicAction N' X = monadicAction N X ≫ (f.hom ▷ X) :=
  Monad.RightModule.hom_condition_app (rightMonadMap f) X

/-- Evaluation of the original ambient internal Hom. -/
abbrev baseEvaluation (N : RightModuleFree.Carrier A) (X : C) :
    N.X ⊗ ((ihom N.X).obj X) ⟶ X := (ihom.ev N.X).app X

theorem baseEvaluation_naturality (N : RightModuleFree.Carrier A) {X Y : C} (f : X ⟶ Y) :
    (N.X ◁ (ihom N.X).map f) ≫ baseEvaluation N Y = baseEvaluation N X ≫ f :=
  ihom.ev_naturality N.X f

/-- The original right-action/evaluation pairing, before taking its adjunct. -/
def homActionPairing (N : RightModuleFree.Carrier A) (X : C) :
    N.X ⊗ ((Monad.tensorMonad A).obj ((ihom N.X).obj X)) ⟶ X :=
  monadicAction N ((ihom N.X).obj X) ≫ baseEvaluation N X

/-- The actual left scalar action on the ambient internal Hom. -/
def homAction (N : RightModuleFree.Carrier A) (X : C) :
    A ⊗ ((ihom N.X).obj X) ⟶ (ihom N.X).obj X :=
  MonoidalClosed.curry (homActionPairing N X)

theorem homAction_evaluation (N : RightModuleFree.Carrier A) (X : C) :
    (N.X ◁ homAction N X) ≫ baseEvaluation N X = homActionPairing N X :=
  MonoidalClosed.uncurry_curry _

theorem homAction_unit (N : RightModuleFree.Carrier A) (X : C) :
    (Monad.tensorMonad A).η.app ((ihom N.X).obj X) ≫ homAction N X =
      𝟙 ((ihom N.X).obj X) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_id_eq_ev]
  change (N.X ◁ (Monad.tensorMonad A).η.app ((ihom N.X).obj X)) ≫
    (N.X ◁ homAction N X) ≫ baseEvaluation N X = _
  rw [homAction_evaluation]
  unfold homActionPairing
  rw [← Category.assoc, monadicAction_unit]
  exact Category.id_comp (baseEvaluation N X)

theorem homAction_assoc (N : RightModuleFree.Carrier A) (X : C) :
    (Monad.tensorMonad A).μ.app ((ihom N.X).obj X) ≫ homAction N X =
      (Monad.tensorMonad A).map (homAction N X) ≫ homAction N X := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left]
  change (N.X ◁ (Monad.tensorMonad A).μ.app ((ihom N.X).obj X)) ≫
      (N.X ◁ homAction N X) ≫ baseEvaluation N X =
    (N.X ◁ (A ◁ homAction N X)) ≫
      (N.X ◁ homAction N X) ≫ baseEvaluation N X
  simp only [homAction_evaluation]
  unfold homActionPairing
  rw [← Category.assoc,
    monadicAction_assoc N ((ihom N.X).obj X)]
  rw [← Category.assoc (N.X ◁ (A ◁ homAction N X))
      (monadicAction N ((ihom N.X).obj X)),
    monadicAction_naturality N (homAction N X)]
  change (monadicAction N (A ⊗ ((ihom N.X).obj X)) ≫
    monadicAction N ((ihom N.X).obj X)) ≫ baseEvaluation N X =
      (monadicAction N (A ⊗ ((ihom N.X).obj X)) ≫ (N.X ◁ homAction N X)) ≫ baseEvaluation N X
  simp only [Category.assoc, homAction_evaluation]
  simp only [homActionPairing, monadicAction, Category.assoc]

/-- The same action is a genuine algebra over the original tensor monad. -/
def homAlgebra (N : RightModuleFree.Carrier A) (X : C) : (Monad.tensorMonad A).Algebra where
  A := (ihom N.X).obj X
  a := homAction N X
  unit := homAction_unit N X
  assoc := homAction_assoc N X

/-- The monad laws give the original left module laws on this actual action. -/
def homObject (N : RightModuleFree.Carrier A) (X : C) : Mod C A where
  X := (ihom N.X).obj X
  mod :=
    { smul := homAction N X
      one_smul := by
        apply (cancel_epi (λ_ ((ihom N.X).obj X)).inv).mp
        change (λ_ ((ihom N.X).obj X)).inv ≫ (η[A] ▷ ((ihom N.X).obj X)) ≫
          homAction N X = (λ_ ((ihom N.X).obj X)).inv ≫ (λ_ ((ihom N.X).obj X)).hom
        rw [Iso.inv_hom_id]
        have h := homAction_unit N X
        change ((λ_ ((ihom N.X).obj X)).inv ≫ (η[A] ▷ ((ihom N.X).obj X))) ≫
          homAction N X = 𝟙 ((ihom N.X).obj X) at h
        simpa only [Category.assoc] using h
      mul_smul := by
        apply (cancel_epi (α_ A A ((ihom N.X).obj X)).inv).mp
        change (α_ A A ((ihom N.X).obj X)).inv ≫ (μ[A] ▷ ((ihom N.X).obj X)) ≫
          homAction N X = (α_ A A ((ihom N.X).obj X)).inv ≫
            (α_ A A ((ihom N.X).obj X)).hom ≫ (A ◁ homAction N X) ≫ homAction N X
        rw [Iso.inv_hom_id_assoc]
        have h := homAction_assoc N X
        change ((α_ A A ((ihom N.X).obj X)).inv ≫ (μ[A] ▷ ((ihom N.X).obj X))) ≫
          homAction N X = (A ◁ homAction N X) ≫ homAction N X at h
        simpa only [Category.assoc] using h }

theorem homObject_carrier (N : RightModuleFree.Carrier A) (X : C) :
    (homObject N X).X = (ihom N.X).obj X := rfl

theorem homObject_action (N : RightModuleFree.Carrier A) (X : C) :
    (homObject N X).mod.smul = MonoidalClosed.curry
      ((α_ N.X A ((ihom N.X).obj X)).inv ≫
        (rightAction N ▷ ((ihom N.X).obj X)) ≫ baseEvaluation N X) := by
  change homAction N X = _
  unfold homAction homActionPairing monadicAction
  rw [Category.assoc]

/-- Postcomposition respects the actual scalar action through the evaluation naturality. -/
def homAlgebraMap (N : RightModuleFree.Carrier A) {X Y : C} (f : X ⟶ Y) :
    homAlgebra N X ⟶ homAlgebra N Y where
  f := (ihom N.X).map f
  h := by
    apply MonoidalClosed.uncurry_injective
    change MonoidalClosed.uncurry
        ((Monad.tensorMonad A).map ((ihom N.X).map f) ≫ homAction N Y) =
      MonoidalClosed.uncurry (homAction N X ≫ (ihom N.X).map f)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
    change (N.X ◁ (A ◁ (ihom N.X).map f)) ≫
      (N.X ◁ homAction N Y) ≫ baseEvaluation N Y =
        ((N.X ◁ homAction N X) ≫ baseEvaluation N X) ≫ f
    simp only [homAction_evaluation]
    unfold homActionPairing
    rw [← Category.assoc,
      monadicAction_naturality N ((ihom N.X).map f), Category.assoc,
      baseEvaluation_naturality]
    simp only [monadicAction, Category.assoc]

/-- The internal-Hom map induced by the actual coefficient morphism. -/
def homMap (N : RightModuleFree.Carrier A) {X Y : C} (f : X ⟶ Y) :
    homObject N X ⟶ homObject N Y :=
  Mod.Hom.mk' ((ihom N.X).map f) (homAlgebraMap N f).h.symm

theorem homMap_carrier (N : RightModuleFree.Carrier A) {X Y : C} (f : X ⟶ Y) :
    (homMap N f).hom = (ihom N.X).map f := rfl

/-- The genuine right adjoint retains the entire internal Hom on underlying maps. -/
def homFunctor (N : RightModuleFree.Carrier A) : C ⥤ Mod C A where
  obj := homObject N
  map := homMap N
  map_id X := by
    apply Mod.hom_ext
    change (ihom N.X).map (𝟙 X) = 𝟙 ((ihom N.X).obj X)
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    apply Mod.hom_ext
    change (ihom N.X).map (f ≫ g) = (ihom N.X).map f ≫ (ihom N.X).map g
    exact CategoryTheory.Functor.map_comp _ _ _

section Balanced

variable [HasColimitsOfSize.{0, 0} C]

omit [HasColimitsOfSize.{0, 0} C] in
/-- Currying the full balanced equation is exactly actual left-module linearity. -/
theorem curry_linear_iff (N : RightModuleFree.Carrier A) (M : Mod C A) {X : C}
    (k : N.X ⊗ M.X ⟶ X) :
    M.mod.smul ≫ MonoidalClosed.curry k =
        (A ◁ MonoidalClosed.curry k) ≫ (homObject N X).mod.smul ↔
      pointFst N M ≫ k = pointSnd N M ≫ k := by
  have hright : MonoidalClosed.uncurry
      ((A ◁ MonoidalClosed.curry k) ≫ (homObject N X).mod.smul) = pointFst N M ≫ k := by
    rw [MonoidalClosed.uncurry_natural_left]
    change (N.X ◁ (A ◁ MonoidalClosed.curry k)) ≫
      (N.X ◁ homAction N X) ≫ baseEvaluation N X = _
    rw [homAction_evaluation]
    unfold homActionPairing
    rw [← Category.assoc, monadicAction_naturality N (MonoidalClosed.curry k),
      Category.assoc, MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rfl
  have hleft : MonoidalClosed.uncurry (M.mod.smul ≫ MonoidalClosed.curry k) =
      pointSnd N M ≫ k := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    rfl
  constructor
  · intro h
    have hh := congrArg MonoidalClosed.uncurry h
    rw [hleft, hright] at hh
    exact hh.symm
  · intro h
    apply MonoidalClosed.uncurry_injective
    rw [hleft, hright, h]

/-- The full balanced tensor–Hom equivalence on the original module carriers. -/
def tensorHomEquivModule (N : RightModuleFree.Carrier A) (M : Mod C A) (X : C) :
    (tensorObject N M ⟶ X) ≃ (M ⟶ homObject N X) where
  toFun f := Mod.Hom.mk' (MonoidalClosed.curry (projection N M ≫ f))
    ((curry_linear_iff N M _).mpr (by
      rw [← Category.assoc, projection_balance, Category.assoc]))
  invFun g := tensorDesc N M (MonoidalClosed.uncurry g.hom) (by
    have h := IsModHom.smul_hom (A := A) (f := g.hom)
    change M.mod.smul ≫ g.hom = (A ◁ g.hom) ≫ (homObject N X).mod.smul at h
    have hc := (curry_linear_iff N M (MonoidalClosed.uncurry g.hom)).mp
      (by simpa only [MonoidalClosed.curry_uncurry] using h)
    exact hc)
  left_inv f := by
    apply tensor_hom_ext N M
    rw [projection_tensorDesc]
    change MonoidalClosed.uncurry (MonoidalClosed.curry (projection N M ≫ f)) = _
    exact MonoidalClosed.uncurry_curry _
  right_inv g := by
    apply Mod.hom_ext
    change MonoidalClosed.curry (projection N M ≫ tensorDesc N M _ _) = g.hom
    rw [projection_tensorDesc, MonoidalClosed.curry_uncurry]

/-- The original balanced tensor is left adjoint to the constructed actual internal Hom module. -/
def tensorHomAdjunction (N : RightModuleFree.Carrier A) :
    leftTensorFunctor N ⊣ homFunctor N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquivModule N
      homEquiv_naturality_left_symm := by
        intro M' M X f g
        apply tensor_hom_ext N M'
        change projection N M' ≫ tensorDesc N M' (MonoidalClosed.uncurry (f ≫ g).hom) _ =
          projection N M' ≫ (leftTensorFunctor N).map f ≫
            tensorDesc N M (MonoidalClosed.uncurry g.hom) _
        rw [projection_tensorDesc, ← Category.assoc,
          leftTensorFunctor_projection, Category.assoc, projection_tensorDesc]
        change MonoidalClosed.uncurry (f.hom ≫ g.hom) =
          (N.X ◁ f.hom) ≫ MonoidalClosed.uncurry g.hom
        exact MonoidalClosed.uncurry_natural_left _ _
      homEquiv_naturality_right := by
        intro M X Y f g
        apply Mod.hom_ext
        change MonoidalClosed.curry (projection N M ≫ (f ≫ g)) =
          MonoidalClosed.curry (projection N M ≫ f) ≫ (ihom N.X).map g
        rw [← Category.assoc, MonoidalClosed.curry_natural_right] }

theorem tensorHomAdjunction_forward (N : RightModuleFree.Carrier A) (M : Mod C A) (X : C)
    (f : tensorObject N M ⟶ X) :
    ((tensorHomAdjunction N).homEquiv M X f).hom =
      MonoidalClosed.curry (projection N M ≫ f) := by
  unfold tensorHomAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem tensorHomAdjunction_reverse_projection
    (N : RightModuleFree.Carrier A) (M : Mod C A) (X : C)
    (g : M ⟶ homObject N X) :
    projection N M ≫ ((tensorHomAdjunction N).homEquiv M X).symm g =
      MonoidalClosed.uncurry g.hom := by
  unfold tensorHomAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact projection_tensorDesc N M _ _

/-- All chosen source colimits, in their original independent universes, are preserved. -/
theorem leftTensorFunctor_preservesColimits (N : RightModuleFree.Carrier A) :
    PreservesColimitsOfSize.{w', w} (leftTensorFunctor N) :=
  (tensorHomAdjunction N).leftAdjoint_preservesColimits

end Balanced
end CategoryTheory.Mod.RightLeftTensor
