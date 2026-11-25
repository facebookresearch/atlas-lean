/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensorClosed
public import MathlibExt.CategoryTheory.Monoidal.RightModulePresentation
public import MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction

/-!
# The source mapping equalizer of right internal modules

For actual right modules `M` and `N`, this construction is the equalizer of
precomposition by `M.action` and the transpose of evaluation followed by
`N.action`. The scalar monoid need not be commutative. The full action arrows,
all parameter families, and both source and target variances are retained.

When the scalar is commutative, the equalizer is compared with the existing
left-module internal Hom by the actual braiding of the action argument. The
comparison proves the source presentation, transfers the original right action,
and identifies the balanced tensor adjunction including its unit and counit.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEnd

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]
  (R : C) [MonObj R]

/-- The original ambient internal Hom of both actual module carriers. -/
abbrev ambient (M N : RightModule R) : C := (ihom M.X).obj N.X

/-- The entire right-action argument of the two source equalizer arrows. -/
abbrev actionTarget (M N : RightModule R) : C := (ihom (M.X ⊗ R)).obj N.X

/-- The source arrow is literal precomposition by the original right action. -/
def sourceActionMap (M N : RightModule R) : ambient R M N ⟶ actionTarget R M N :=
  (MonoidalClosed.pre M.action).app N.X

/-- The target arrow is the transpose of the original coefficient/evaluation/target-action
composite. Both braidings are the actual ambient symmetry maps. -/
def targetActionMap (M N : RightModule R) : ambient R M N ⟶ actionTarget R M N :=
  MonoidalClosed.curry
    (((β_ M.X R).hom ▷ ambient R M N) ≫
      (α_ R M.X (ambient R M N)).hom ≫
      (R ◁ (ihom.ev M.X).app N.X) ≫ (β_ R N.X).hom ≫ N.action)

omit [SymmetricCategory C] in
/-- Uncurrying the complete source action arrow gives its literal action/evaluation map. -/
theorem sourceActionMap_uncurry (M N : RightModule R) :
    MonoidalClosed.uncurry (sourceActionMap R M N) =
      (M.action ▷ ambient R M N) ≫ (ihom.ev M.X).app N.X := by
  exact MonoidalClosed.id_tensor_pre_app_comp_ev M.action N.X

/-- Uncurrying the complete target action arrow keeps every original shuffle and action. -/
theorem targetActionMap_uncurry (M N : RightModule R) :
    MonoidalClosed.uncurry (targetActionMap R M N) =
      ((β_ M.X R).hom ▷ ambient R M N) ≫
        (α_ R M.X (ambient R M N)).hom ≫
        (R ◁ (ihom.ev M.X).app N.X) ≫ (β_ R N.X).hom ≫ N.action :=
  MonoidalClosed.uncurry_curry _

variable [HasEqualizers C]

/-- The actual source mapping object, with no commutativity hypothesis on the scalar. -/
def Hom (M N : RightModule R) : C :=
  equalizer (sourceActionMap R M N) (targetActionMap R M N)

/-- Its literal inclusion into the complete original ambient internal Hom. -/
def ι (M N : RightModule R) : Hom R M N ⟶ ambient R M N :=
  equalizer.ι (sourceActionMap R M N) (targetActionMap R M N)

/-- The mapping object has precisely the original complete action equalizer presentation. -/
theorem Hom_eq (M N : RightModule R) : Hom R M N =
    equalizer (sourceActionMap R M N) (targetActionMap R M N) := rfl

/-- Both entire original action arrows agree after the actual equalizer inclusion. -/
@[reassoc]
theorem condition (M N : RightModule R) :
    ι R M N ≫ sourceActionMap R M N = ι R M N ≫ targetActionMap R M N :=
  equalizer.condition _ _

/-- The limiting fork retains the two actual source action arrows. -/
def fork (M N : RightModule R) : Fork (sourceActionMap R M N) (targetActionMap R M N) :=
  Fork.ofι (ι R M N) (condition R M N)

/-- The source fork has the full equalizer universal property. -/
def forkIsLimit (M N : RightModule R) : IsLimit (fork R M N) :=
  equalizerIsEqualizer (sourceActionMap R M N) (targetActionMap R M N)

/-- All complete compatible parameter families, without an assumed mapping value. -/
@[ext]
structure Family (M N : RightModule R) (P : C) where
  /-- The complete original parameter map into the ambient internal Hom. -/
  app : P ⟶ ambient R M N
  condition : app ≫ sourceActionMap R M N = app ≫ targetActionMap R M N

/-- The actual complete family carried by a map into the source equalizer. -/
def toFamily (M N : RightModule R) {P : C} (f : P ⟶ Hom R M N) : Family R M N P where
  app := f ≫ ι R M N
  condition := by simp only [Category.assoc, condition]

/-- The equalizer lift of every complete original compatible family. -/
def lift (M N : RightModule R) {P : C} (q : Family R M N P) : P ⟶ Hom R M N :=
  equalizer.lift q.app q.condition

/-- The lift preserves the whole original ambient family. -/
@[reassoc]
theorem lift_ι (M N : RightModule R) {P : C} (q : Family R M N P) :
    lift R M N q ≫ ι R M N = q.app := equalizer.lift_ι _ _

/-- All full maps into the original source equalizer are detected by their ambient family. -/
@[ext]
theorem hom_ext (M N : RightModule R) {P : C} {f g : P ⟶ Hom R M N}
    (h : f ≫ ι R M N = g ≫ ι R M N) : f = g := equalizer.hom_ext h

/-- Every complete compatible family is recovered after lifting. -/
theorem toFamily_lift (M N : RightModule R) {P : C} (q : Family R M N P) :
    toFamily R M N (lift R M N q) = q := by
  apply Family.ext
  exact lift_ι R M N q

/-- Every entire map into the source equalizer is recovered after taking its family. -/
theorem lift_toFamily (M N : RightModule R) {P : C} (f : P ⟶ Hom R M N) :
    lift R M N (toFamily R M N f) = f := by
  apply hom_ext R M N
  exact lift_ι R M N (toFamily R M N f)

/-- The source equalizer represents exactly all full compatible parameter families. -/
def parameterEquiv (M N : RightModule R) (P : C) :
    (P ⟶ Hom R M N) ≃ Family R M N P where
  toFun := toFamily R M N
  invFun := lift R M N
  left_inv := lift_toFamily R M N
  right_inv := toFamily_lift R M N

/-- Every actual parameter map acts by whole-family precomposition. -/
def reparameterize (M N : RightModule R) {P Q : C} (f : P ⟶ Q)
    (q : Family R M N Q) : Family R M N P where
  app := f ≫ q.app
  condition := by simpa only [Category.assoc] using congrArg (fun z => f ≫ z) q.condition

/-- Lifting is natural for every original parameter morphism. -/
@[reassoc]
theorem lift_reparameterize (M N : RightModule R) {P Q : C} (f : P ⟶ Q)
    (q : Family R M N Q) :
    lift R M N (reparameterize R M N f q) = f ≫ lift R M N q := by
  apply hom_ext R M N
  simp only [lift_ι, reparameterize, Category.assoc]

/-- The original evaluation uses the whole equalizer inclusion. -/
def evaluation (M N : RightModule R) : M.X ⊗ Hom R M N ⟶ N.X :=
  MonoidalClosed.uncurry (ι R M N)

/-- Every lifted compatible parameter family evaluates by its whole given component. -/
@[reassoc]
theorem lift_evaluation (M N : RightModule R) {P : C} (q : Family R M N P) :
    (M.X ◁ lift R M N q) ≫ evaluation R M N = MonoidalClosed.uncurry q.app := by
  rw [evaluation, ← MonoidalClosed.uncurry_natural_left, lift_ι]

/-- The full action equation is equality of the literal original action/evaluation maps. -/
theorem evaluation_action (M N : RightModule R) :
    (M.action ▷ Hom R M N) ≫ evaluation R M N =
      ((β_ M.X R).hom ▷ Hom R M N) ≫
        (α_ R M.X (Hom R M N)).hom ≫
        (R ◁ evaluation R M N) ≫ (β_ R N.X).hom ≫ N.action := by
  have h := congrArg MonoidalClosed.uncurry (condition R M N)
  rw [sourceActionMap, MonoidalClosed.uncurry_pre_app] at h
  rw [targetActionMap, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry] at h
  change (M.action ▷ Hom R M N) ≫ evaluation R M N = _ at h
  rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc] at h
  exact h

omit [HasEqualizers C] [SymmetricCategory C] in
/-- Every entire target carrier map commutes with source-action precomposition. -/
theorem sourceActionMap_post (M : RightModule R) {N N' : RightModule R}
    (f : N ⟶ N') :
    (ihom M.X).map f.hom ≫ sourceActionMap R M N' =
      sourceActionMap R M N ≫ (ihom (M.X ⊗ R)).map f.hom :=
  (MonoidalClosed.pre M.action).naturality f.hom

omit [HasEqualizers C] in
/-- A whole target module morphism commutes with the original full target-action arrow. -/
theorem targetActionMap_post (M : RightModule R) {N N' : RightModule R}
    (f : N ⟶ N') :
    (ihom M.X).map f.hom ≫ targetActionMap R M N' =
      targetActionMap R M N ≫ (ihom (M.X ⊗ R)).map f.hom := by
  have hEv := (ihom.ev M.X).naturality f.hom
  change (M.X ◁ (ihom M.X).map f.hom) ≫ (ihom.ev M.X).app N'.X =
    (ihom.ev M.X).app N.X ≫ f.hom at hEv
  apply MonoidalClosed.uncurry_injective
  rw [targetActionMap, targetActionMap, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_curry]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, hEv,
    whiskerLeft_comp]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [braiding_naturality_right R f.hom]
  simp only [Category.assoc, ← CommutativeModuleConversion.RightModule.comm f]

/-- Target variance lifts the whole original internal-Hom postcomposition family. -/
def post (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    Hom R M N ⟶ Hom R M N' :=
  lift R M N' {
    app := ι R M N ≫ (ihom M.X).map f.hom
    condition := by
      rw [Category.assoc, sourceActionMap_post, ← Category.assoc,
        condition, Category.assoc, ← targetActionMap_post, ← Category.assoc] }

/-- Every full target-variance family is literal internal-Hom postcomposition. -/
@[reassoc]
theorem post_ι (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    post R M f ≫ ι R M N' = ι R M N ≫ (ihom M.X).map f.hom := lift_ι R M N' _

/-- The whole original identity is retained by target variance, without scalar commutativity. -/
@[simp]
theorem post_id (M N : RightModule R) : post R M (𝟙 N) = 𝟙 (Hom R M N) := by
  apply hom_ext R M N
  rw [post_ι]
  simp only [Mod.id_hom', Functor.map_id, Category.comp_id, Category.id_comp]

/-- The entire source-first order is retained by target variance. -/
theorem post_comp (M : RightModule R) {N N' N'' : RightModule R}
    (f : N ⟶ N') (g : N' ⟶ N'') :
    post R M (f ≫ g) = post R M f ≫ post R M g := by
  apply hom_ext R M N''
  rw [post_ι, Category.assoc, post_ι, ← Category.assoc, post_ι]
  simp only [Mod.comp_hom', Functor.map_comp, Category.assoc]

omit [HasEqualizers C] [SymmetricCategory C] in
/-- The complete source-module square gives the original source-action naturality. -/
theorem sourceActionMap_pre {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (MonoidalClosed.pre f.hom).app N.X ≫ sourceActionMap R M' N =
      sourceActionMap R M N ≫ (MonoidalClosed.pre (f.hom ▷ R)).app N.X := by
  dsimp only [sourceActionMap]
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
    ← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  exact congrArg (fun z => (MonoidalClosed.pre z).app N.X)
    (CommutativeModuleConversion.RightModule.comm f)

omit [HasEqualizers C] in
/-- The original full target-action map is contravariantly natural in the source carrier. -/
theorem targetActionMap_pre {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (MonoidalClosed.pre f.hom).app N.X ≫ targetActionMap R M' N =
      targetActionMap R M N ≫ (MonoidalClosed.pre (f.hom ▷ R)).app N.X := by
  apply MonoidalClosed.uncurry_injective
  rw [targetActionMap, targetActionMap, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_curry]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, MonoidalClosed.id_tensor_pre_app_comp_ev,
    whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    ← braiding_naturality_left]
  simp only [Category.assoc, comp_whiskerRight]

/-- Source variance lifts the whole original internal-Hom precomposition family. -/
def pre {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    Hom R M N ⟶ Hom R M' N :=
  lift R M' N {
    app := ι R M N ≫ (MonoidalClosed.pre f.hom).app N.X
    condition := by
      rw [Category.assoc, sourceActionMap_pre, ← Category.assoc,
        condition, Category.assoc, ← targetActionMap_pre, ← Category.assoc] }

/-- Every full source-variance family is literal internal-Hom precomposition. -/
@[reassoc]
theorem pre_ι {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    pre R f N ≫ ι R M' N = ι R M N ≫ (MonoidalClosed.pre f.hom).app N.X :=
  lift_ι R M' N _

/-- The whole source identity is retained without scalar commutativity. -/
@[simp]
theorem pre_id (M N : RightModule R) : pre R (𝟙 M) N = 𝟙 (Hom R M N) := by
  apply hom_ext R M N
  rw [pre_ι]
  simp only [Mod.id_hom', MonoidalClosed.pre_id, NatTrans.id_app,
    Category.comp_id, Category.id_comp]

/-- The complete original contravariant source order is retained. -/
theorem pre_comp {M M' M'' : RightModule R} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : RightModule R) : pre R (g ≫ f) N = pre R f N ≫ pre R g N := by
  apply hom_ext R M'' N
  rw [pre_ι, Category.assoc, pre_ι, ← Category.assoc, pre_ι]
  simp only [Mod.comp_hom', MonoidalClosed.pre_map, NatTrans.comp_app, Category.assoc]

/-- Both entire original variances commute on the source equalizer. -/
theorem pre_post {M M' N N' : RightModule R} (f : M' ⟶ M) (g : N ⟶ N') :
    pre R f N ≫ post R M' g = post R M g ≫ pre R f N' := by
  apply hom_ext R M' N'
  conv_lhs => rw [Category.assoc, post_ι, ← Category.assoc, pre_ι]
  conv_rhs => rw [Category.assoc, pre_ι, ← Category.assoc, post_ι]
  simpa only [Category.assoc] using congrArg (fun z => ι R M N ≫ z)
    ((MonoidalClosed.pre f.hom).naturality g.hom).symm

section Commutative

variable [IsCommMonObj R]

/-- The unchanged left modules are obtained by the actual source braiding. -/
abbrev leftModule (M : RightModule R) : Mod C R := toLeft R M

/-- The original coefficient object and multiplication define the commutative scalar. -/
abbrev scalar : CommMon C := { X := R }

/-- The original stock left-module internal Hom has its complete existing carrier. -/
abbrev stockHom (M N : RightModule R) : Mod C R :=
  (Mod.internalHomOfEqualizer (scalar R) (leftModule R M)).obj (leftModule R N)

/-- The actual stock equalizer inclusion lands in the unchanged original ambient object. -/
abbrev stockι (M N : RightModule R) : (stockHom R M N).X ⟶ ambient R M N :=
  Mod.internalHomι (scalar R) (leftModule R M) (leftModule R N)

/-- The full argument braid compares the original coefficient-first and coefficient-right
action-Hom targets. -/
def actionTargetComparison (M N : RightModule R) :
    (ihom (R ⊗ M.X)).obj N.X ≅ actionTarget R M N where
  hom := (MonoidalClosed.pre (β_ M.X R).hom).app N.X
  inv := (MonoidalClosed.pre (β_ M.X R).inv).app N.X
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.hom_inv_id,
      MonoidalClosed.pre_id, NatTrans.id_app]

omit [HasEqualizers C] in
/-- The actual argument braid identifies the whole source-action arrow. -/
@[reassoc]
theorem stock_source_to_right (M N : RightModule R) :
    Mod.internalHomPre (scalar R) (leftModule R M) (leftModule R N) ≫
        (actionTargetComparison R M N).hom = sourceActionMap R M N := by
  change (MonoidalClosed.pre ((β_ R M.X).hom ≫ M.action)).app N.X ≫
    (MonoidalClosed.pre (β_ M.X R).hom).app N.X =
      (MonoidalClosed.pre M.action).app N.X
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  simp only [SymmetricCategory.symmetry_assoc]

omit [HasEqualizers C] in
/-- The same actual argument braid identifies the complete target-action arrow. -/
@[reassoc]
theorem stock_target_to_right (M N : RightModule R) :
    Mod.internalHomPost (scalar R) (leftModule R M) (leftModule R N) ≫
        (actionTargetComparison R M N).hom = targetActionMap R M N := by
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry
    (Mod.internalHomPost (scalar R) (leftModule R M) (leftModule R N) ≫
      (MonoidalClosed.pre (β_ M.X R).hom).app N.X) = _
  rw [MonoidalClosed.uncurry_pre_app]
  dsimp only [Mod.internalHomPost, leftModule, toLeft, leftModObj, leftAction,
    targetActionMap, scalar]
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  rfl

/-- The original stock inclusion equalizes both complete source right-action arrows. -/
@[reassoc]
theorem stock_condition (M N : RightModule R) :
    stockι R M N ≫ sourceActionMap R M N = stockι R M N ≫ targetActionMap R M N := by
  rw [← stock_source_to_right R M N, ← stock_target_to_right R M N,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun z => z ≫ (actionTargetComparison R M N).hom)
    (Mod.internalHom_condition (scalar R) (leftModule R M) (leftModule R N))

/-- The stock original object is a limit of the actual full source right-action fork. -/
def stockForkIsLimit (M N : RightModule R) :
    IsLimit (Fork.ofι (stockι R M N) (stock_condition R M N)) := by
  let h := Mod.internalHomIsLimit (scalar R) (leftModule R M) (leftModule R N)
  refine Fork.IsLimit.mk' _ (fun q => ?_)
  have hq : q.ι ≫ Mod.internalHomPre (scalar R) (leftModule R M) (leftModule R N) =
      q.ι ≫ Mod.internalHomPost (scalar R) (leftModule R M) (leftModule R N) := by
    apply (cancel_mono (actionTargetComparison R M N).hom).1
    rw [Category.assoc, stock_source_to_right, Category.assoc, stock_target_to_right]
    exact q.condition
  let l := Fork.IsLimit.lift' h q.ι hq
  exact ⟨l.1, l.2, fun hm => Fork.IsLimit.hom_ext h (hm.trans l.2.symm)⟩

/-- The source presentation and original stock internal Hom are compared by their complete
limiting forks, rather than assuming an internal-Hom identification. -/
def stockComparison (M N : RightModule R) : Hom R M N ≅ (stockHom R M N).X :=
  (forkIsLimit R M N).conePointUniqueUpToIso (stockForkIsLimit R M N)

/-- The forward comparison preserves the entire original ambient family. -/
@[reassoc]
theorem stockComparison_hom_ι (M N : RightModule R) :
    (stockComparison R M N).hom ≫ stockι R M N = ι R M N :=
  (forkIsLimit R M N).conePointUniqueUpToIso_hom_comp (stockForkIsLimit R M N)
    WalkingParallelPair.zero

/-- The inverse comparison preserves the entire original ambient family. -/
@[reassoc]
theorem stockComparison_inv_ι (M N : RightModule R) :
    (stockComparison R M N).inv ≫ ι R M N = stockι R M N :=
  (forkIsLimit R M N).conePointUniqueUpToIso_inv_comp (stockForkIsLimit R M N)
    WalkingParallelPair.zero

/-- The right stock object has the original complete action derived by the lawful conversion. -/
abbrev stockRightHom (M N : RightModule R) : RightModule R :=
  toRight R (stockHom R M N)

/-- The complete source equalizer inherits the original right action through its proved
whole-object comparison. -/
def moduleObject (M N : RightModule R) : RightModule R := by
  let H := stockRightHom R M N
  letI : ModObj (mop R) H.X := H.mod
  letI : IsMonHom (Iso.refl (mop R)).hom := by
    change IsMonHom (𝟙 (mop R))
    infer_instance
  exact {
    X := Hom R M N
    mod := ModObj.ofIso (Iso.refl (mop R)) (stockComparison R M N).symm }

/-- The source module object retains literally the complete action equalizer carrier. -/
@[simp]
theorem moduleObject_X (M N : RightModule R) : (moduleObject R M N).X = Hom R M N := rfl

/-- Its actual source right action has both whole comparison maps and the original action. -/
theorem moduleObject_action (M N : RightModule R) :
    (moduleObject R M N).action =
      ((stockComparison R M N).hom ▷ R) ≫
        (stockRightHom R M N).action ≫ (stockComparison R M N).inv := by
  change ((stockComparison R M N).hom ⊗ₘ 𝟙 R) ≫
      (stockRightHom R M N).action ≫ (stockComparison R M N).inv = _
  rw [tensorHom_id]

/-- The forward source/stock comparison is a genuine right-module morphism. -/
def comparisonHom (M N : RightModule R) : moduleObject R M N ⟶ stockRightHom R M N :=
  Mod.Hom.mk' (stockComparison R M N).hom (by
    change (moduleObject R M N).action ≫ (stockComparison R M N).hom =
      ((stockComparison R M N).hom ▷ R) ≫ (stockRightHom R M N).action
    rw [moduleObject_action]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The inverse source/stock comparison is a genuine right-module morphism. -/
def comparisonInv (M N : RightModule R) : stockRightHom R M N ⟶ moduleObject R M N :=
  Mod.Hom.mk' (stockComparison R M N).inv (by
    change (stockRightHom R M N).action ≫ (stockComparison R M N).inv =
      ((stockComparison R M N).inv ▷ R) ≫ (moduleObject R M N).action
    rw [moduleObject_action]
    calc
      _ = (𝟙 ((stockRightHom R M N).X ⊗ R)) ≫
          (stockRightHom R M N).action ≫ (stockComparison R M N).inv := by
        rw [Category.id_comp]
      _ = (((stockComparison R M N).inv ≫ (stockComparison R M N).hom) ▷ R) ≫
          (stockRightHom R M N).action ≫ (stockComparison R M N).inv := by
        rw [Iso.inv_hom_id, id_whiskerRight]
        rfl
      _ = _ := by rw [comp_whiskerRight, Category.assoc])

/-- The complete source/stock isomorphism includes the original right action. -/
def moduleComparison (M N : RightModule R) : moduleObject R M N ≅ stockRightHom R M N where
  hom := comparisonHom R M N
  inv := comparisonInv R M N
  hom_inv_id := by
    apply Mod.hom_ext
    exact (stockComparison R M N).hom_inv_id
  inv_hom_id := by
    apply Mod.hom_ext
    exact (stockComparison R M N).inv_hom_id

/-- The full original converted stock internal-Hom functor, used only after proving its source
equalizer presentation. -/
abbrev stockFunctor (M : RightModule R) : RightModule R ⥤ RightModule R :=
  rightToLeft R ⋙ Mod.internalHomOfEqualizer (scalar R) (leftModule R M) ⋙ leftToRight R

/-- Every target module arrow acts on the original source equalizer through the proved
complete module comparisons. -/
def map (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    moduleObject R M N ⟶ moduleObject R M N' :=
  (moduleComparison R M N).hom ≫ (stockFunctor R M).map f ≫
    (moduleComparison R M N').inv

/-- The source equalizer values and the actual target maps form a lawful functor. -/
def functor (M : RightModule R) : RightModule R ⥤ RightModule R where
  obj := moduleObject R M
  map := map R M
  map_id N := by
    change (moduleComparison R M N).hom ≫
      (stockFunctor R M).map (𝟙 N) ≫ (moduleComparison R M N).inv = _
    rw [Functor.map_id]
    change (moduleComparison R M N).hom ≫
      𝟙 (stockRightHom R M N) ≫ (moduleComparison R M N).inv = _
    rw [Category.id_comp]
    exact (moduleComparison R M N).hom_inv_id
  map_comp f g := by
    simp only [map, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- The original module comparison is natural for all target module arrows. -/
def comparisonNatIso (M : RightModule R) : functor R M ≅ stockFunctor R M :=
  NatIso.ofComponents (moduleComparison R M) (by
    intro N N' f
    simp only [functor, map, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Every original target arrow acts by literal postcomposition on the whole ambient Hom. -/
@[reassoc]
theorem map_ι (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    ((functor R M).map f).hom ≫ ι R M N' =
      ι R M N ≫ (ihom M.X).map f.hom := by
  change ((stockComparison R M N).hom ≫ ((stockFunctor R M).map f).hom ≫
    (stockComparison R M N').inv) ≫ ι R M N' = _
  simp only [Category.assoc]
  rw [stockComparison_inv_ι]
  have hmap : (stockFunctor R M).map f = toRightMap R
      ((Mod.internalHomOfEqualizer (scalar R) (leftModule R M)).map (toLeftMap R f)) := rfl
  rw [hmap, toRightMap_hom]
  rw [Mod.internalHomMap, ← Category.assoc, stockComparison_hom_ι]
  rw [toLeftMap_hom]
  rfl

section Balanced

variable [HasCoequalizers C]

/-- Use the original relative-tensor monoidal structure on right modules. -/
local instance moduleMonoidal : MonoidalCategory (RightModule R) :=
  RightModuleFree.tensorMonoidal R

/-- Use the same original relative-tensor symmetry on right modules. -/
local instance moduleSymmetric : SymmetricCategory (RightModule R) :=
  RightModuleFree.tensorSymmetric R

/-- The original balanced left tensor adjunction, retaining both complete conversion
adjunctions and the existing relative tensor unit and counit. -/
def stockAdjunction (M : RightModule R) : tensorLeft M ⊣ stockFunctor R M :=
  ((moduleEquivalence R).symm.toAdjunction.comp
    (Mod.relativeTensorInternalHomAdjunction (scalar R) (leftModule R M))).comp
      (moduleEquivalence R).toAdjunction

/-- Balanced tensoring on the left is adjoint to the actual source right-action equalizer. -/
def leftAdjunction (M : RightModule R) : tensorLeft M ⊣ functor R M :=
  (stockAdjunction R M).ofNatIsoRight (comparisonNatIso R M).symm

/-- The whole original source unit is the stock unit followed by the proved inverse source
comparison. -/
theorem leftAdjunction_unit (M N : RightModule R) :
    (leftAdjunction R M).unit.app N =
      (stockAdjunction R M).unit.app N ≫ (moduleComparison R M (M ⊗ N)).inv := rfl

/-- The whole original source counit is the proved forward source comparison followed by
the stock balanced evaluation. -/
theorem leftAdjunction_counit (M N : RightModule R) :
    (leftAdjunction R M).counit.app N =
      (tensorLeft M).map (moduleComparison R M N).hom ≫
        (stockAdjunction R M).counit.app N := rfl

/-- The actual source unit and counit satisfy the complete left triangle. -/
theorem leftAdjunction_left_triangle (M N : RightModule R) :
    (tensorLeft M).map ((leftAdjunction R M).unit.app N) ≫
      (leftAdjunction R M).counit.app (M ⊗ N) = 𝟙 (M ⊗ N) :=
  (leftAdjunction R M).left_triangle_components N

/-- The actual source unit and counit satisfy the complete right triangle. -/
theorem leftAdjunction_right_triangle (M N : RightModule R) :
    (leftAdjunction R M).unit.app ((functor R M).obj N) ≫
      (functor R M).map ((leftAdjunction R M).counit.app N) =
        𝟙 ((functor R M).obj N) :=
  (leftAdjunction R M).right_triangle_components N

/-- The MMSS source orientation tensors the variable module on the right by its fixed source. -/
def adjunction (M : RightModule R) : tensorRight M ⊣ functor R M :=
  (leftAdjunction R M).ofNatIsoLeft (tensorLeftIsoTensorRight M)

/-- The actual source-oriented unit keeps the whole original relative tensor braid. -/
theorem adjunction_unit (M N : RightModule R) :
    (adjunction R M).unit.app N =
      (leftAdjunction R M).unit.app N ≫ (functor R M).map (β_ M N).hom := rfl

/-- The actual source-oriented counit keeps the whole inverse relative tensor braid. -/
theorem adjunction_counit (M N : RightModule R) :
    (adjunction R M).counit.app N =
      (β_ M ((functor R M).obj N)).inv ≫ (leftAdjunction R M).counit.app N := rfl

/-- The original source-oriented unit and evaluation satisfy the whole left triangle. -/
theorem adjunction_left_triangle (M N : RightModule R) :
    (tensorRight M).map ((adjunction R M).unit.app N) ≫
      (adjunction R M).counit.app (N ⊗ M) = 𝟙 (N ⊗ M) :=
  (adjunction R M).left_triangle_components N

/-- The original source-oriented unit and evaluation satisfy the whole right triangle. -/
theorem adjunction_right_triangle (M N : RightModule R) :
    (adjunction R M).unit.app ((functor R M).obj N) ≫
      (functor R M).map ((adjunction R M).counit.app N) =
        𝟙 ((functor R M).obj N) :=
  (adjunction R M).right_triangle_components N

end Balanced
end Commutative

end CategoryTheory.RightModuleMappingEnd
