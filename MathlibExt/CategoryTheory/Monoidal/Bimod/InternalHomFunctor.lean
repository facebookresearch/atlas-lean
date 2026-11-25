/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.InternalHomEqualizer
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightTensorHomPreMap

/-!
# Functoriality of the actual relative mapping bimodule

The actual source and target bimodule maps preserve the equalizer because
they preserve the original right actions. Both maps are lifted from the
proved unbalanced pre/post maps, and all source and target naturalities
retain the original equalizer inclusion and evaluation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj Opposite
open scoped MonoidalCategory

namespace Bimod.InternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] {A B D : Mon C}

/-- Every original target map acts on right evaluation by its actual underlying map. -/
theorem unbalancedPost_evaluation (N : Bimod B D) {P P' : Bimod A D} (g : P ⟶ P')
    {X : C} (f : X ⟶ (ihom N.X).obj P.X) :
    ((f ≫ (unbalancedPost N g).hom) ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P'.X =
      ((f ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X) ≫ g.hom := by
  have h := (originalRightTensorAdjunction N.X).counit.naturality g.hom
  change ((ihom N.X).map g.hom ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P'.X =
    (originalRightTensorAdjunction N.X).counit.app P.X ≫ g.hom at h
  rw [unbalancedPost_hom, comp_whiskerRight, Category.assoc]
  erw [h]
  rw [← Category.assoc]

/-- Every original source map acts on right evaluation by its original tensor-coordinate map. -/
theorem unbalancedPre_evaluation {N N' : Bimod B D} (g : N ⟶ N') (P : Bimod A D)
    {X : C} (f : X ⟶ (ihom N'.X).obj P.X) :
    ((f ≫ (unbalancedPre g P).hom) ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X =
      (X ◁ g.hom) ≫ ((f ▷ N'.X) ≫ (originalRightTensorAdjunction N'.X).counit.app P.X) := by
  rw [unbalancedPre_hom, comp_whiskerRight, Category.assoc,
    originalRightTensorAdjunction_pre_evaluation, ← whisker_exchange_assoc]

variable [HasLimitsOfSize.{0, 0} C]

/-- The original target map preserves the complete D-linearity equalizer equation. -/
theorem unbalancedPost_equalizes (N : Bimod B D) {P P' : Bimod A D} (g : P ⟶ P') :
    (inclusion N P ≫ unbalancedPost N g) ≫ rightLinearityPre N P' =
      (inclusion N P ≫ unbalancedPost N g) ≫ rightLinearityPost N P' := by
  apply Bimod.hom_ext
  change ((inclusion N P).hom ≫ (unbalancedPost N g).hom) ≫ (rightLinearityPre N P').hom =
    ((inclusion N P).hom ≫ (unbalancedPost N g).hom) ≫ (rightLinearityPost N P').hom
  apply (rightLinearity_underlying_iff N P' _).mpr
  rw [unbalancedPost_evaluation]
  change ((homObject N P).X ◁ N.actRight) ≫ (underlyingEvaluation N P ≫ g.hom) =
    (α_ (homObject N P).X N.X D.X).inv ≫ ((underlyingEvaluation N P ≫ g.hom) ▷ D.X) ≫ P'.actRight
  rw [← Category.assoc, underlyingEvaluation_right_linear]
  simp only [comp_whiskerRight, Category.assoc]
  rw [g.right_act_hom]

/-- The actual target Hom map is the lift of the original postcomposition through the equalizer. -/
def homMap (N : Bimod B D) {P P' : Bimod A D} (g : P ⟶ P') : homObject N P ⟶ homObject N P' :=
  lift N P' (inclusion N P ≫ unbalancedPost N g) (unbalancedPost_equalizes N g)

/-- The complete target-map square retains the original postcomposition and equalizer leg. -/
theorem homMap_inclusion (N : Bimod B D) {P P' : Bimod A D} (g : P ⟶ P') :
    homMap N g ≫ inclusion N P' = inclusion N P ≫ unbalancedPost N g := lift_inclusion _ _ _ _

/-- Every actual target identity remains the identity of the original relative Hom. -/
theorem homMap_id (N : Bimod B D) (P : Bimod A D) : homMap N (𝟙 P) = 𝟙 (homObject N P) := by
  apply hom_ext N P
  rw [homMap_inclusion, Category.id_comp]
  apply Bimod.hom_ext
  simp only [Bimod.comp_hom', unbalancedPost_hom, Bimod.id_hom', CategoryTheory.Functor.map_id]
  exact Category.comp_id (inclusion N P).hom

/-- Every actual target composition retains its original order. -/
theorem homMap_comp (N : Bimod B D) {P P' P'' : Bimod A D} (g : P ⟶ P') (h : P' ⟶ P'') :
    homMap N (g ≫ h) = homMap N g ≫ homMap N h := by
  apply hom_ext N P''
  rw [homMap_inclusion, Category.assoc, homMap_inclusion, ← Category.assoc, homMap_inclusion]
  apply Bimod.hom_ext
  simp only [Bimod.comp_hom', unbalancedPost_hom, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The original relative mapping bimodule is an actual functor on target bimodules. -/
def homFunctor (N : Bimod B D) : Bimod A D ⥤ Bimod A B where
  obj := homObject N
  map := homMap N
  map_id := homMap_id N
  map_comp := homMap_comp N

/-- The original source map preserves the complete D-linearity equalizer equation. -/
theorem unbalancedPre_equalizes {N N' : Bimod B D} (g : N ⟶ N') (P : Bimod A D) :
    (inclusion N' P ≫ unbalancedPre g P) ≫ rightLinearityPre N P =
      (inclusion N' P ≫ unbalancedPre g P) ≫ rightLinearityPost N P := by
  apply Bimod.hom_ext
  change ((inclusion N' P).hom ≫ (unbalancedPre g P).hom) ≫ (rightLinearityPre N P).hom =
    ((inclusion N' P).hom ≫ (unbalancedPre g P).hom) ≫ (rightLinearityPost N P).hom
  apply (rightLinearity_underlying_iff N P _).mpr
  rw [unbalancedPre_evaluation]
  change ((homObject N' P).X ◁ N.actRight) ≫
      ((homObject N' P).X ◁ g.hom) ≫ underlyingEvaluation N' P =
    (α_ (homObject N' P).X N.X D.X).inv ≫
      ((((homObject N' P).X ◁ g.hom) ≫ underlyingEvaluation N' P) ▷ D.X) ≫ P.actRight
  rw [← whiskerLeft_comp_assoc, g.right_act_hom, whiskerLeft_comp, Category.assoc,
    underlyingEvaluation_right_linear, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc]

/-- The actual contravariant source map is the lift of the original ambient precomposition. -/
def homPre {N N' : Bimod B D} (g : N ⟶ N') (P : Bimod A D) : homObject N' P ⟶ homObject N P :=
  lift N P (inclusion N' P ≫ unbalancedPre g P) (unbalancedPre_equalizes g P)

/-- The complete source-map square keeps the original precomposition and equalizer leg. -/
theorem homPre_inclusion {N N' : Bimod B D} (g : N ⟶ N') (P : Bimod A D) :
    homPre g P ≫ inclusion N P = inclusion N' P ≫ unbalancedPre g P := lift_inclusion _ _ _ _

/-- Original source identities remain identities of the actual relative Hom. -/
theorem homPre_id (N : Bimod B D) (P : Bimod A D) : homPre (𝟙 N) P = 𝟙 (homObject N P) := by
  apply hom_ext N P
  rw [homPre_inclusion, Category.id_comp]
  apply Bimod.hom_ext
  simp only [Bimod.comp_hom', unbalancedPre_hom, Bimod.id_hom', MonoidalClosed.pre_id, NatTrans.id_app]
  exact Category.comp_id (inclusion N P).hom

/-- Original source compositions act in their complete contravariant order. -/
theorem homPre_comp {N N' N'' : Bimod B D} (g : N ⟶ N') (h : N' ⟶ N'') (P : Bimod A D) :
    homPre (g ≫ h) P = homPre h P ≫ homPre g P := by
  apply hom_ext N P
  rw [homPre_inclusion, Category.assoc, homPre_inclusion, ← Category.assoc, homPre_inclusion]
  apply Bimod.hom_ext
  simp only [Bimod.comp_hom', unbalancedPre_hom, MonoidalClosed.pre_map, NatTrans.comp_app, Category.assoc]

/-- Both original source and target maps commute on the entire relative Hom. -/
theorem homPre_homMap {N N' : Bimod B D} (f : N ⟶ N') {P P' : Bimod A D} (g : P ⟶ P') :
    homMap N' g ≫ homPre f P' = homPre f P ≫ homMap N g := by
  apply hom_ext N P'
  rw [Category.assoc, homPre_inclusion, ← Category.assoc, homMap_inclusion]
  rw [Category.assoc (homPre f P) (homMap N g) (inclusion N P'), homMap_inclusion,
    ← Category.assoc (homPre f P) (inclusion N P) (unbalancedPost N g), homPre_inclusion]
  apply Bimod.hom_ext
  simp only [Bimod.comp_hom', unbalancedPost_hom, unbalancedPre_hom, Category.assoc]
  rw [(MonoidalClosed.pre f.hom).naturality g.hom]

/-- Every original source arrow is natural on all original target bimodules. -/
def homPreNatural {N N' : Bimod B D} (f : N ⟶ N') : homFunctor (A := A) N' ⟶ homFunctor N where
  app := homPre f
  naturality _ _ g := homPre_homMap f g

/-- The complete relative Hom retains contravariant source maps and actual target maps. -/
def homContravariant : (Bimod B D)ᵒᵖ ⥤ Bimod A D ⥤ Bimod A B where
  obj N := homFunctor N.unop
  map f := homPreNatural f.unop
  map_id N := by
    ext P
    exact congrArg Bimod.Hom.hom (homPre_id N.unop P)
  map_comp f g := by
    ext P
    exact congrArg Bimod.Hom.hom (homPre_comp g.unop f.unop P)

end Bimod.InternalHom
