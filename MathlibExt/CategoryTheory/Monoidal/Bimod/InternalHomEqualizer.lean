/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.InternalHomLinearArrows
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The actual relative mapping bimodule

The equalizer of the two proved bimodule arrows imposes the original
right `D` linearity condition. Its inclusion preserves both outer actions,
and the original right evaluation is balanced over the source scalar and
linear over the target right scalar.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj
open CategoryTheory.HomogeneousLocalization
open scoped MonoidalCategory

namespace Bimod.InternalHom

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] {A B D : Mon C}

/-- The two actual mapping arrows equalize exactly when the original right evaluation is D-linear. -/
theorem rightLinearity_underlying_iff (N : Bimod B D) (P : Bimod A D)
    {X : C} (f : X ⟶ (ihom N.X).obj P.X) :
    f ≫ (rightLinearityPre N P).hom = f ≫ (rightLinearityPost N P).hom ↔
      (X ◁ N.actRight) ≫ (f ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X =
        (α_ X N.X D.X).inv ≫
          (((f ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X) ▷ D.X) ≫ P.actRight := by
  let H := (ihom N.X).obj P.X
  let a := originalRightTensorAdjunction (N.X ⊗ D.X)
  let e := (originalRightTensorAdjunction N.X).counit.app P.X
  rw [rightLinearityPre_hom, rightLinearityPost_hom]
  have hp : f ≫ (MonoidalClosed.pre N.actRight).app P.X =
      a.homEquiv X P.X ((f ▷ (N.X ⊗ D.X)) ≫ (H ◁ N.actRight) ≫ e) := by
    rw [← originalRightTensorAdjunction_pre N.actRight P.X]
    exact (a.homEquiv_naturality_left f ((H ◁ N.actRight) ≫ e)).symm
  have hq : f ≫ a.homEquiv H P.X ((α_ H N.X D.X).inv ≫ (e ▷ D.X) ≫ P.actRight) =
      a.homEquiv X P.X
        ((f ▷ (N.X ⊗ D.X)) ≫ (α_ H N.X D.X).inv ≫ (e ▷ D.X) ≫ P.actRight) :=
    (a.homEquiv_naturality_left f ((α_ H N.X D.X).inv ≫ (e ▷ D.X) ≫ P.actRight)).symm
  rw [hp, hq]
  constructor
  · intro h
    have hh := (a.homEquiv X P.X).injective h
    rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc] at hh
    exact hh
  · intro h
    have hh : (f ▷ (N.X ⊗ D.X)) ≫ (H ◁ N.actRight) ≫ e =
        (f ▷ (N.X ⊗ D.X)) ≫ (α_ H N.X D.X).inv ≫ (e ▷ D.X) ≫ P.actRight := by
      rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
      exact h
    exact congrArg (a.homEquiv X P.X) hh

variable [HasLimitsOfSize.{0, 0} C]

local instance mappingLimits (A B : Mon C) : HasLimitsOfSize.{0, 0} (Bimod A B) := Bimod.hasLimits A B

/-- The original relative Hom is the actual equalizer in the existing bimodule category. -/
def homObject (N : Bimod B D) (P : Bimod A D) : Bimod A B :=
  equalizer (rightLinearityPre N P) (rightLinearityPost N P)

/-- The actual equalizer leg retains both original outer actions. -/
def inclusion (N : Bimod B D) (P : Bimod A D) : homObject N P ⟶ unbalanced N P :=
  equalizer.ι (rightLinearityPre N P) (rightLinearityPost N P)

/-- The complete original equalizer equation is an equation of actual bimodule morphisms. -/
theorem inclusion_condition (N : Bimod B D) (P : Bimod A D) :
    inclusion N P ≫ rightLinearityPre N P = inclusion N P ≫ rightLinearityPost N P :=
  equalizer.condition _ _

/-- The uncurried evaluator keeps the literal equalizer inclusion and original right counit. -/
def underlyingEvaluation (N : Bimod B D) (P : Bimod A D) :
    (homObject N P).X ⊗ N.X ⟶ P.X :=
  ((inclusion N P).hom ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X

/-- The original evaluation is an actual A-module map on the ambient right tensor. -/
def evaluationLeftMap (N : Bimod B D) (P : Bimod A D) :
    Mod.AmbientTensor.rightModule A.X N.X (toLeftModule (homObject N P)) ⟶ toLeftModule P :=
  Mod.AmbientTensor.rightMap A.X (𝟙 N.X) ((leftModuleFunctor A B).map (inclusion N P)) ≫
    (ambientRightAdjunction A N.X).counit.app (toLeftModule P)

/-- The complete A-linear evaluator is the same original inclusion/evaluation word. -/
theorem evaluationLeftMap_hom (N : Bimod B D) (P : Bimod A D) :
    (evaluationLeftMap N P).hom = underlyingEvaluation N P := by
  rw [evaluationLeftMap, Mod.comp_hom', Mod.AmbientTensor.rightMap_hom, tensorHom_id,
    ambientRightAdjunction_counit_hom]
  rfl

/-- The actual equalizer inclusion and original Hom balancing law prove source B balancing. -/
theorem underlyingEvaluation_balance (N : Bimod B D) (P : Bimod A D) :
    ((homObject N P).actRight ▷ N.X) ≫ underlyingEvaluation N P =
      (α_ (homObject N P).X B.X N.X).hom ≫
        ((homObject N P).X ◁ N.actLeft) ≫ underlyingEvaluation N P := by
  let i := inclusion N P
  have hi : (homObject N P).actRight ≫ i.hom = (i.hom ▷ B.X) ≫ (unbalanced N P).actRight :=
    i.right_act_hom
  have he : ((unbalanced N P).actRight ▷ N.X) ≫
      (originalRightTensorAdjunction N.X).counit.app P.X =
    (α_ (unbalanced N P).X B.X N.X).hom ≫ ((unbalanced N P).X ◁ N.actLeft) ≫
      (originalRightTensorAdjunction N.X).counit.app P.X :=
    Mod.RightLeftTensor.rightEvaluation_balance (toLeftModule N) P.X
  simp only [underlyingEvaluation]
  rw [← comp_whiskerRight_assoc, hi, comp_whiskerRight]
  rw [Category.assoc, he]
  erw [associator_naturality_left_assoc, ← whisker_exchange_assoc]

/-- The complete equalizer equation proves the original target D-linearity of evaluation. -/
theorem underlyingEvaluation_right_linear (N : Bimod B D) (P : Bimod A D) :
    ((homObject N P).X ◁ N.actRight) ≫ underlyingEvaluation N P =
      (α_ (homObject N P).X N.X D.X).inv ≫ (underlyingEvaluation N P ▷ D.X) ≫ P.actRight := by
  have h := congrArg Bimod.Hom.hom (inclusion_condition N P)
  change (inclusion N P).hom ≫ (rightLinearityPre N P).hom =
    (inclusion N P).hom ≫ (rightLinearityPost N P).hom at h
  exact (rightLinearity_underlying_iff N P (inclusion N P).hom).mp h

/-- Every actual equalizing bimodule map lifts through the original relative Hom inclusion. -/
def lift {M : Bimod A B} (N : Bimod B D) (P : Bimod A D) (f : M ⟶ unbalanced N P)
    (h : f ≫ rightLinearityPre N P = f ≫ rightLinearityPost N P) : M ⟶ homObject N P :=
  equalizer.lift f h

/-- The complete equalizer factorization retains the original source bimodule map. -/
theorem lift_inclusion {M : Bimod A B} (N : Bimod B D) (P : Bimod A D)
    (f : M ⟶ unbalanced N P) (h : f ≫ rightLinearityPre N P = f ≫ rightLinearityPost N P) :
    lift N P f h ≫ inclusion N P = f := equalizer.lift_ι _ _

/-- The actual relative Hom is determined by its original equalizer inclusion. -/
theorem hom_ext {M : Bimod A B} (N : Bimod B D) (P : Bimod A D)
    {f g : M ⟶ homObject N P} (h : f ≫ inclusion N P = g ≫ inclusion N P) : f = g :=
  equalizer.hom_ext h

end Bimod.InternalHom
