/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monad.CartesianClassifyingBar
public import MathlibExt.CategoryTheory.Monad.TensorMonadNaturality
public import MathlibExt.CategoryTheory.Monad.BarChange
public import MathlibExt.CategoryTheory.Monad.BarRegularContraction
import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedWhiskering

/-!
# Functoriality of cartesian classifying bars

The canonical cartesian specializations of `classifyingBar` and `universalBar` are functorial in
the internal monoid. An internal-monoid morphism acts through `tensorMonadHom`, module restriction,
and the generic two-sided-bar change map. Degreewise formulas identify the resulting maps with
`monadPowHom`; these formulas prove identity and composition without dependent transport through
restriction isomorphisms.

The universal-bundle maps form a natural transformation from `universalBarFunctor` to
`classifyingBarFunctor`. The regular augmentation forms a natural transformation to the constant
simplicial tensor unit. No realization or homotopical claim is made here.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.Monad.ClassifyingBar

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {M N P : Mon C}

attribute [local instance] pointModObj

private noncomputable abbrev pointRightModule (M : Mon C) :=
  rightModuleOfRightAction (𝟙_ C) M.X (pointRightAction M)
    (pointRightAction_one M) (pointRightAction_assoc M)

private noncomputable abbrev pointLeftModule (M : Mon C) :=
  leftPointModule M.X (𝟙_ C)

private noncomputable def pointRightModuleHom (f : M ⟶ N) :
    pointRightModule M ⟶
      (rightModuleRestrictAlongHom (tensorMonadHom f)).obj (pointRightModule N) where
  f := 𝟙 _
  h := by
    apply NatTrans.ext
    funext X
    rw [Functor.map_id]
    unfold pointRightModule
    simp only [Category.id_comp, Category.comp_id,
      RightModule.restrictAlongHom_obj_action_app,
      rightModuleOfRightAction_action_app, tensorMonadHom_app]
    let map : ((𝟙_ C) ⊗ (M.X ⊗ X)) ⟶ ((𝟙_ C) ⊗ (N.X ⊗ X)) :=
      (pointRightModule N).functor.map (f.hom ▷ X)
    have hMap : map = (𝟙_ C) ◁ (f.hom ▷ X) := rfl
    have hActN : (pointRightModule N).action.app X =
        (α_ (𝟙_ C) N.X X).inv ≫ (pointRightAction N ▷ X) :=
      rightModuleOfRightAction_action_app _ _ _ _ _ _
    have hActM : (pointRightModule M).action.app X =
        (α_ (𝟙_ C) M.X X).inv ≫ (pointRightAction M ▷ X) :=
      rightModuleOfRightAction_action_app _ _ _ _ _ _
    apply CartesianMonoidalCategory.hom_ext
    · exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    · calc
        (map ≫ (pointRightModule N).action.app X) ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X =
          (((𝟙_ C) ◁ (f.hom ▷ X)) ≫
            ((α_ (𝟙_ C) N.X X).inv ≫ (pointRightAction N ▷ X))) ≫
              CartesianMonoidalCategory.snd (𝟙_ C) X := by
            exact congrArg (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X)
              (congrArg₂ (· ≫ ·) hMap hActN)
        _ = ((α_ (𝟙_ C) M.X X).inv ≫ (pointRightAction M ▷ X)) ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X := by
          simp only [pointRightAction, Category.assoc,
            CartesianMonoidalCategory.whiskerRight_snd,
            CartesianMonoidalCategory.associator_inv_snd]
          rw [CartesianMonoidalCategory.whiskerLeft_snd_assoc,
            CartesianMonoidalCategory.whiskerRight_snd]
        _ = (pointRightModule M).action.app X ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X :=
          congrArg (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X) hActM.symm

private noncomputable def pointLeftModuleHom (f : M ⟶ N) :
    pointLeftModule M ⟶
      (leftModuleRestrictAlongHom (tensorMonadHom f)).obj (pointLeftModule N) where
  f := 𝟙 _
  h := by
    apply NatTrans.ext
    funext a
    rw [Functor.map_id]
    simp only [Category.id_comp, Category.comp_id,
      LeftModule.restrictAlongHom_obj_action_app]
    unfold pointLeftModule
    change (tensorMonadHom f).app (𝟙_ C) ≫
        (pointLeftModule N).action.app a =
      (pointLeftModule M).action.app a
    exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

private noncomputable def classifyingBarRawMap (f : M ⟶ N) :
    classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) ⟶
      classifyingBar N.X (𝟙_ C) (pointRightAction N)
        (pointRightAction_one N) (pointRightAction_assoc N) :=
  twoSidedBarHom (pointRightModuleHom f) (pointLeftModuleHom f) ≫
    barChangeHom (tensorMonadHom f) (pointRightModule N) (pointLeftModule N)

private noncomputable def universalRightModuleHom (f : M ⟶ N) :
    rightModuleOfRightAction M.X M.X MonObj.mul (MonObj.mul_one M.X)
        ((MonObj.mul_assoc M.X).symm) ⟶
      (rightModuleRestrictAlongHom (tensorMonadHom f)).obj
        (rightModuleOfRightAction N.X N.X MonObj.mul (MonObj.mul_one N.X)
          ((MonObj.mul_assoc N.X).symm)) where
  f := (tensorMonadHom f).toNatTrans
  h := by
    apply NatTrans.ext
    funext X
    change (tensorMonadHom f).app ((tensorMonad M.X).obj X) ≫
        ((tensorMonad N.X).map ((tensorMonadHom f).app X) ≫
          (tensorMonad N.X).μ.app X) =
      (tensorMonad M.X).μ.app X ≫ (tensorMonadHom f).app X
    rw [← Category.assoc, ← (tensorMonadHom f).naturality]
    exact ((tensorMonadHom f).app_μ X).symm

private noncomputable def universalBarRawMap (f : M ⟶ N) :
    universalBar (M := M.X) (Pt := 𝟙_ C) ⟶
      universalBar (M := N.X) (Pt := 𝟙_ C) :=
  twoSidedBarHom (universalRightModuleHom f) (pointLeftModuleHom f) ≫
    barChangeHom (tensorMonadHom f)
      (rightModuleOfRightAction N.X N.X MonObj.mul (MonObj.mul_one N.X)
        ((MonObj.mul_assoc N.X).symm)) (pointLeftModule N)

/-- The evaluated classifying-bar map induced by an internal-monoid morphism. -/
noncomputable def classifyingBarMap (f : M ⟶ N) :
    (classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) ⋙ pointEvaluation C) ⟶
      (classifyingBar N.X (𝟙_ C) (pointRightAction N)
        (pointRightAction_one N) (pointRightAction_assoc N) ⋙ pointEvaluation C) :=
  Functor.whiskerRight (classifyingBarRawMap f) (pointEvaluation C)

/-- The evaluated universal-bar map induced by an internal-monoid morphism. -/
noncomputable def universalBarMap (f : M ⟶ N) :
    (universalBar (M := M.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C) ⟶
      (universalBar (M := N.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C) :=
  Functor.whiskerRight (universalBarRawMap f) (pointEvaluation C)

/-- Degreewise formula for the evaluated classifying-bar map. -/
theorem classifyingBarMap_app_op_mk (f : M ⟶ N) (n : ℕ) :
    (classifyingBarMap f).app (op (SimplexCategory.mk n)) =
      (tensorLeft (𝟙_ C)).map
        ((monadPowHom (tensorMonadHom f) n).app (𝟙_ C)) := by
  change (((classifyingBarRawMap f).app (op (SimplexCategory.mk n))).app index) = _
  unfold classifyingBarRawMap
  simp only [NatTrans.comp_app]
  rw [twoSidedBarHom_app_app_op_mk, barChangeHom_app_app_op_mk]
  simp only [pointLeftModuleHom, NatTrans.id_app, Functor.map_id,
    pointRightModuleHom, Category.id_comp]
  change 𝟙 _ ≫ (tensorLeft (𝟙_ C)).map
      ((monadPowHom (tensorMonadHom f) n).app (𝟙_ C)) = _
  rw [Category.id_comp]

/-- Degreewise formula for the evaluated universal-bar map. -/
theorem universalBarMap_app_op_mk (f : M ⟶ N) (n : ℕ) :
    (universalBarMap f).app (op (SimplexCategory.mk n)) =
      (tensorMonadHom f).app
          ((monadPow (tensorMonad M.X) n).obj (𝟙_ C)) ≫
        (tensorMonad N.X).map
          ((monadPowHom (tensorMonadHom f) n).app (𝟙_ C)) := by
  change (((universalBarRawMap f).app (op (SimplexCategory.mk n))).app index) = _
  unfold universalBarRawMap
  simp only [NatTrans.comp_app]
  rw [twoSidedBarHom_app_app_op_mk, barChangeHom_app_app_op_mk]
  simp only [pointLeftModuleHom, NatTrans.id_app, Functor.map_id,
    universalRightModuleHom, Category.id_comp]
  rfl

/-- The identity internal-monoid morphism induces the identity classifying-bar map. -/
@[simp]
theorem classifyingBarMap_id (M : Mon C) :
    classifyingBarMap (𝟙 M) = 𝟙 _ := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  change (classifyingBarMap (𝟙 M)).app (op (SimplexCategory.mk n)) =
    𝟙 ((tensorLeft (𝟙_ C)).obj
      ((monadPow (tensorMonad M.X) n).obj (𝟙_ C)))
  rw [classifyingBarMap_app_op_mk, tensorMonadHom_id, monadPowHom_id]
  simp only [NatTrans.id_app, Functor.map_id]

/-- Classifying-bar maps compose with internal-monoid morphisms. -/
@[simp]
theorem classifyingBarMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    classifyingBarMap (f ≫ g) = classifyingBarMap f ≫ classifyingBarMap g := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  rw [classifyingBarMap_app_op_mk, NatTrans.comp_app,
    classifyingBarMap_app_op_mk, classifyingBarMap_app_op_mk,
    tensorMonadHom_comp, monadPowHom_comp_app]
  exact Functor.map_comp _ _ _

/-- The identity internal-monoid morphism induces the identity universal-bar map. -/
@[simp]
theorem universalBarMap_id (M : Mon C) :
    universalBarMap (𝟙 M) = 𝟙 _ := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  change (universalBarMap (𝟙 M)).app (op (SimplexCategory.mk n)) =
    𝟙 ((tensorMonad M.X).obj
      ((monadPow (tensorMonad M.X) n).obj (𝟙_ C)))
  rw [universalBarMap_app_op_mk, tensorMonadHom_id, monadPowHom_id]
  simp only [NatTrans.id_app, Functor.map_id, Category.comp_id]
  rfl

/-- Universal-bar maps compose with internal-monoid morphisms. -/
@[simp]
theorem universalBarMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    universalBarMap (f ≫ g) = universalBarMap f ≫ universalBarMap g := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  rw [universalBarMap_app_op_mk, NatTrans.comp_app,
    universalBarMap_app_op_mk, universalBarMap_app_op_mk,
    tensorMonadHom_comp, monadPowHom_comp_app, Functor.map_comp]
  simp only [MonadHom.comp_toNatTrans, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, ← (tensorMonadHom g).naturality_assoc]

/-- The cartesian classifying bar as a functor of the internal monoid. -/
noncomputable def classifyingBarFunctor (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] : Mon C ⥤ SimplicialObject C where
  obj M := classifyingBar M.X (𝟙_ C) (pointRightAction M)
      (pointRightAction_one M) (pointRightAction_assoc M) ⋙ pointEvaluation C
  map f := classifyingBarMap f
  map_id M := classifyingBarMap_id M
  map_comp f g := classifyingBarMap_comp f g

/-- The cartesian universal bar as a functor of the internal monoid. -/
noncomputable def universalBarFunctor (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] : Mon C ⥤ SimplicialObject C where
  obj M := universalBar (M := M.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C
  map f := universalBarMap f
  map_id M := universalBarMap_id M
  map_comp f g := universalBarMap_comp f g

@[simp]
theorem classifyingBarFunctor_obj (M : Mon C) :
    (classifyingBarFunctor C).obj M =
      classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) ⋙ pointEvaluation C :=
  rfl

@[simp]
theorem classifyingBarFunctor_map (f : M ⟶ N) :
    (classifyingBarFunctor C).map f = classifyingBarMap f :=
  rfl

@[simp]
theorem universalBarFunctor_obj (M : Mon C) :
    (universalBarFunctor C).obj M =
      universalBar (M := M.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C :=
  rfl

@[simp]
theorem universalBarFunctor_map (f : M ⟶ N) :
    (universalBarFunctor C).map f = universalBarMap f :=
  rfl

private noncomputable def bundleRightModuleHom (M : Mon C) :
    rightModuleOfRightAction M.X M.X MonObj.mul (MonObj.mul_one M.X)
        ((MonObj.mul_assoc M.X).symm) ⟶
      pointRightModule M :=
  rightModuleHomOfRightComp (augmentation M) (augmentation_compat M)
    (h_one := MonObj.mul_one M.X)
    (h_assoc := (MonObj.mul_assoc M.X).symm)
    (h_one' := pointRightAction_one M)
    (h_assoc' := pointRightAction_assoc M)

private noncomputable def bundleLeftModuleHom (M : Mon C) :
    pointLeftModule M ⟶ pointLeftModule M :=
  leftPointModuleHomOfIsModHom (M := M.X) (𝟙 (𝟙_ C))

private noncomputable def universalBundleRawMap (M : Mon C) :
    universalBar (M := M.X) (Pt := 𝟙_ C) ⟶
      classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) :=
  twoSidedBarHom (bundleRightModuleHom M) (bundleLeftModuleHom M)

private theorem universalBundleRawMap_eq (M : Mon C) :
    universalBundleRawMap M =
      universalBundle M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M)
        (augmentation M) (augmentation_compat M) :=
  rfl

/-- The evaluated universal-bundle component. -/
noncomputable def universalBundleMap (M : Mon C) :
    (universalBarFunctor C).obj M ⟶ (classifyingBarFunctor C).obj M :=
  Functor.whiskerRight (universalBundleRawMap M) (pointEvaluation C)

/-- Formula for the evaluated universal-bundle component. -/
theorem universalBundleMap_eq (M : Mon C) :
    universalBundleMap M =
      Functor.whiskerRight
        (universalBundle M.X (𝟙_ C) (pointRightAction M)
          (pointRightAction_one M) (pointRightAction_assoc M)
          (augmentation M) (augmentation_compat M))
        (pointEvaluation C) :=
  rfl

private theorem universalBundleRightModuleHom_naturality (f : M ⟶ N) :
    universalRightModuleHom f ≫
        (rightModuleRestrictAlongHom (tensorMonadHom f)).map
          (bundleRightModuleHom N) =
      bundleRightModuleHom M ≫ pointRightModuleHom f := by
  ext X
  have hReg : (universalRightModuleHom f).f.app X =
      (tensorMonadHom f).app X := rfl
  have hAugN : (bundleRightModuleHom N).f.app X = augmentation N ▷ X := rfl
  have hAugM : (bundleRightModuleHom M).f.app X = augmentation M ▷ X := rfl
  have hPoint : (pointRightModuleHom f).f.app X = 𝟙 ((𝟙_ C) ⊗ X) := rfl
  have hDropN : (augmentation N ▷ X) ≫
      CartesianMonoidalCategory.snd (𝟙_ C) X =
        CartesianMonoidalCategory.snd N.X X := by
    unfold augmentation
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    exact CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom N.X X
  have hDropM : (augmentation M ▷ X) ≫
      CartesianMonoidalCategory.snd (𝟙_ C) X =
        CartesianMonoidalCategory.snd M.X X := by
    unfold augmentation
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    exact CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom M.X X
  apply CartesianMonoidalCategory.hom_ext
  · exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  · calc
      (((universalRightModuleHom f).f.app X ≫
            (bundleRightModuleHom N).f.app X) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X) =
        ((tensorMonadHom f).app X ≫ (augmentation N ▷ X)) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X := by
            rw [hReg, hAugN]
      _ = (f.hom ▷ X) ≫
          ((augmentation N ▷ X) ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X) := by
            rw [tensorMonadHom_app, Category.assoc]
      _ = (f.hom ▷ X) ≫ CartesianMonoidalCategory.snd N.X X := by
            rw [hDropN]
      _ = CartesianMonoidalCategory.snd M.X X :=
        CartesianMonoidalCategory.whiskerRight_snd f.hom X
      _ = (augmentation M ▷ X) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X := hDropM.symm
      _ = (((bundleRightModuleHom M).f.app X ≫
            (pointRightModuleHom f).f.app X) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X) := by
            have hId : augmentation M ▷ X =
                (augmentation M ▷ X) ≫ 𝟙 ((𝟙_ C) ⊗ X) :=
              (Category.comp_id _).symm
            have hPost := congrArg
              (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X)
              (congrArg₂ (· ≫ ·) hAugM hPoint)
            exact (congrArg
              (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X) hId).trans hPost.symm

private theorem universalBundleLeftModuleHom_naturality (f : M ⟶ N) :
    pointLeftModuleHom f ≫
        (leftModuleRestrictAlongHom (tensorMonadHom f)).map
          (bundleLeftModuleHom N) =
      bundleLeftModuleHom M ≫ pointLeftModuleHom f := by
  ext a
  rfl

private theorem universalBundlePreChange_naturality (f : M ⟶ N) :
    twoSidedBarHom (universalRightModuleHom f) (pointLeftModuleHom f) ≫
        twoSidedBarHom
          ((rightModuleRestrictAlongHom (tensorMonadHom f)).map
            (bundleRightModuleHom N))
          ((leftModuleRestrictAlongHom (tensorMonadHom f)).map
            (bundleLeftModuleHom N)) =
      twoSidedBarHom (bundleRightModuleHom M)
          (bundleLeftModuleHom M) ≫
        twoSidedBarHom (pointRightModuleHom f) (pointLeftModuleHom f) := by
  rw [twoSidedBarHom_comp, twoSidedBarHom_comp,
    universalBundleRightModuleHom_naturality,
    universalBundleLeftModuleHom_naturality]

private theorem universalBundleRaw_naturality (f : M ⟶ N) :
    universalBarRawMap f ≫ universalBundleRawMap N =
      universalBundleRawMap M ≫ classifyingBarRawMap f := by
  let h := tensorMonadHom f
  let preE := twoSidedBarHom (universalRightModuleHom f) (pointLeftModuleHom f)
  let changeE := barChangeHom h
    (rightModuleOfRightAction N.X N.X MonObj.mul (MonObj.mul_one N.X)
      ((MonObj.mul_assoc N.X).symm)) (pointLeftModule N)
  let augN := twoSidedBarHom (bundleRightModuleHom N)
    (bundleLeftModuleHom N)
  let augM := twoSidedBarHom (bundleRightModuleHom M)
    (bundleLeftModuleHom M)
  let augN' := twoSidedBarHom
    ((rightModuleRestrictAlongHom h).map (bundleRightModuleHom N))
    ((leftModuleRestrictAlongHom h).map (bundleLeftModuleHom N))
  let changeB := barChangeHom h (pointRightModule N) (pointLeftModule N)
  let preB := twoSidedBarHom (pointRightModuleHom f) (pointLeftModuleHom f)
  have hMixed : changeE ≫ augN = augN' ≫ changeB :=
    (barChangeHom_naturality h (bundleRightModuleHom N)
      (bundleLeftModuleHom N)).symm
  have hPre : preE ≫ augN' = augM ≫ preB :=
    universalBundlePreChange_naturality f
  unfold universalBarRawMap classifyingBarRawMap universalBundleRawMap
  change (preE ≫ changeE) ≫ augN = augM ≫ (preB ≫ changeB)
  calc
    _ = preE ≫ (changeE ≫ augN) := Category.assoc _ _ _
    _ = preE ≫ (augN' ≫ changeB) := congrArg (preE ≫ ·) hMixed
    _ = (preE ≫ augN') ≫ changeB := (Category.assoc _ _ _).symm
    _ = (augM ≫ preB) ≫ changeB := congrArg (· ≫ changeB) hPre
    _ = augM ≫ (preB ≫ changeB) := Category.assoc _ _ _

/-- Naturality of the cartesian universal-bundle map. -/
theorem universalBundle_naturality (f : M ⟶ N) :
    universalBarMap f ≫ universalBundleMap N =
      universalBundleMap M ≫ classifyingBarMap f := by
  unfold universalBarMap classifyingBarMap universalBundleMap
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp]
  exact congrArg (fun q => Functor.whiskerRight q (pointEvaluation C))
    (universalBundleRaw_naturality f)

/-- The universal-bundle maps as a natural transformation of internal-monoid functors. -/
noncomputable def universalBundleNatTrans (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] :
    universalBarFunctor C ⟶ classifyingBarFunctor C where
  app M := universalBundleMap M
  naturality _ _ f := universalBundle_naturality f

@[simp]
theorem universalBundleNatTrans_app (M : Mon C) :
    (universalBundleNatTrans C).app M = universalBundleMap M :=
  rfl

/-- The regular augmented universal bar associated to an internal monoid. -/
noncomputable def universalBarAugmented (M : Mon C) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (pointEvaluation C)).obj
    (BalancedPairing.toSimplicialAugmented
      (BarRegularContraction.regularBalancedPairing (pointLeftModule M)))

@[simp]
theorem universalBarAugmented_left (M : Mon C) :
    (universalBarAugmented M).left = (universalBarFunctor C).obj M :=
  by
    unfold universalBarAugmented universalBarFunctor
    rfl

@[simp]
theorem universalBarAugmented_right (M : Mon C) :
    (universalBarAugmented M).right = 𝟙_ C :=
  by
    unfold universalBarAugmented
    rfl

/-- The evaluated regular universal-bar augmentation. -/
noncomputable def universalBarAugmentationMap (M : Mon C) :
    (universalBarFunctor C).obj M ⟶
      (SimplicialObject.const C).obj (𝟙_ C) :=
  by
    change (universalBarAugmented M).left ⟶
      (SimplicialObject.const C).obj (universalBarAugmented M).right
    exact (universalBarAugmented M).hom

/-- The constant internal-monoid functor at the simplicial tensor unit. -/
noncomputable def tensorUnitSimplicialFunctor
    (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] :
    Mon C ⥤ SimplicialObject C :=
  (Functor.const (Mon C)).obj ((SimplicialObject.const C).obj (𝟙_ C))

/-- Naturality of the regular universal-bar augmentation. -/
theorem universalBarAugmentation_naturality (f : M ⟶ N) :
    universalBarMap f ≫ universalBarAugmentationMap N =
      universalBarAugmentationMap M := by
  apply NatTrans.ext
  funext Δ
  exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- The regular augmentations as a natural transformation to the constant simplicial tensor
unit. -/
noncomputable def universalBarAugmentationNatTrans
    (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] :
    universalBarFunctor C ⟶ tensorUnitSimplicialFunctor C where
  app M := universalBarAugmentationMap M
  naturality _ _ f := by
    change universalBarMap f ≫ universalBarAugmentationMap _ =
      universalBarAugmentationMap _ ≫ 𝟙 _
    rw [universalBarAugmentation_naturality, Category.comp_id]

@[simp]
theorem universalBarAugmentationNatTrans_app (M : Mon C) :
    (universalBarAugmentationNatTrans C).app M =
      universalBarAugmentationMap M :=
  rfl

/-- The canonical degree-zero point of the universal bar. -/
noncomputable def universalBarSection (M : Mon C) :
    (𝟙_ C) ⟶ ((universalBarFunctor C).obj M).obj
      (op (SimplexCategory.mk 0)) :=
  (BarRegularContraction.s' (pointLeftModule M)).app index

/-- Internal-monoid morphisms preserve the canonical degree-zero universal-bar point. -/
theorem universalBarSection_naturality (f : M ⟶ N) :
    universalBarSection M ≫
        ((universalBarFunctor C).map f).app (op (SimplexCategory.mk 0)) =
      universalBarSection N := by
  unfold universalBarSection
  rw [universalBarFunctor_map]
  change (BarRegularContraction.s' (pointLeftModule M)).app index ≫
      (universalBarMap f).app (op (SimplexCategory.mk 0)) =
    (BarRegularContraction.s' (pointLeftModule N)).app index
  rw [universalBarMap_app_op_mk]
  simp only [BarRegularContraction.s'_app, Functor.id_obj,
    monadPowHom_zero_app, Functor.map_id, Category.comp_id]
  exact tensorMonadHom_η f (𝟙_ C)

end CategoryTheory.Monad.ClassifyingBar

end
