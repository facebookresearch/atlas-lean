/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRVariance
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRBalancing
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedColimits
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndAction

/-!
# Full original right action and adjunction on the translated mapping end

The raw diagram is functorial in both complete original right-module arrows
without commutative coefficients. A braided lax coefficient functor supplies
commutativity of its actual Day monoid. In that case the same original
equalizer carries its original right action and the relative tensor
adjunction. The selected Day structure, its constructed closed adjunction,
and the actual scalar and right-module actions are retained throughout.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

private theorem auxiliary_right_uncurry
    {C : Type uV} [Category.{vV} C] [MonoidalCategory C]
    [SymmetricCategory C] [MonoidalClosed C]
    (R : C) [MonObj R] [IsCommMonObj R]
    (M N : CommutativeModuleConversion.RightModule R) :
    MonoidalClosed.uncurry (RightModuleMappingEnd.auxiliaryRightAction R M N) =
      (α_ M.X (RightModuleMappingEnd.ambient R M N) R).inv ≫
        ((ihom.ev M.X).app N.X ▷ R) ≫ N.action := by
  rw [RightModuleMappingEnd.auxiliaryRightAction_eq,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  let H := RightModuleMappingEnd.ambient R M N
  let ev : M.X ⊗ H ⟶ N.X := (ihom.ev M.X).app N.X
  change (M.X ◁ (β_ H R).hom) ≫ (α_ M.X R H).inv ≫
    ((β_ M.X R).hom ▷ H) ≫ (α_ R M.X H).hom ≫
    (R ◁ ev) ≫ (β_ R N.X).hom ≫ N.action =
      (α_ M.X H R).inv ≫ (ev ▷ R) ≫ N.action
  have hb : (R ◁ ev) ≫ (β_ R N.X).hom ≫ N.action =
      (β_ R (M.X ⊗ H)).hom ≫ (ev ▷ R) ≫ N.action :=
    braiding_naturality_right_assoc R ev N.action
  rw [hb, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
    Category.id_comp]
  simp only [Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id,
    Category.id_comp]

@[reassoc]
private theorem coefficient_swap_natural
    {C : Type uV} [Category.{vV} C] [MonoidalCategory C] [SymmetricCategory C]
    (A B : C) {P Q : C} (h : P ⟶ Q) :
    ((A ⊗ B) ◁ h) ≫ coefficientSwap A B Q =
      coefficientSwap A B P ≫ ((A ◁ h) ▷ B) := by
  dsimp only [coefficientSwap]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    braiding_naturality_right, whiskerLeft_comp_assoc,
    associator_inv_naturality_middle]
  simp only [Category.assoc]

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original inserted-identity generator is the same actual binary Day point. -/
theorem unitGenerator_eq_point (F G : EnrichedFunctor V I V) (p : I × I) :
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G p =
      Generators.point d.tensorEnrichedFunctor F G p := Category.assoc _ _ _

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original full triple identity summand is exactly the two unchanged nested Day points. -/
theorem leftAt_identityInsert (F G H : EnrichedFunctor V I V) (j a c : I) :
    AssociatorUnit.identityInsert ((j ⊗ a) ⊗ c) ((F.obj j ⊗ G.obj a) ⊗ H.obj c) ≫
        BraidingTriple.leftAt d F G H ((j ⊗ a) ⊗ c) j a c =
      (Generators.point d.tensorEnrichedFunctor F G (j, a) ▷ H.obj c) ≫
        Generators.point d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
          H (j ⊗ a, c) := by
  let y := (j ⊗ a) ⊗ c
  let Q := (F.obj j ⊗ G.obj a) ⊗ H.obj c
  let Q' := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G (j ⊗ a) ⊗ H.obj c
  let u : Q ⟶ Q' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G (j, a) ▷ H.obj c
  let g := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H y (j ⊗ a, c)
  have hf : BraidingTriple.leftAt d F G H y j a c = (𝟙 (y ⟶[V] y) ⊗ₘ u) ≫ g :=
    (AssociatorFlattening.leftGenerator_flatToNested d F G H y ((j, a), c)).trans
      (congrArg (fun z => (𝟙 (y ⟶[V] y) ⊗ₘ z) ≫ g)
        (tensorHom_id (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G (j, a))
          (H.obj c)))
  have hi : AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ u) =
      u ≫ AssociatorUnit.identityInsert y Q' :=
    (congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z)
      (id_tensorHom (y ⟶[V] y) u)).trans (AssociatorUnit.identityInsert_naturality y u)
  calc
    _ = AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ u) ≫ g :=
      congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z) hf
    _ = (u ≫ AssociatorUnit.identityInsert y Q') ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ g) hi)
    _ = u ≫ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F G) H (j ⊗ a, c) := Category.assoc _ _ _
    _ = _ := congrArg₂ (fun p q => (p ▷ H.obj c) ≫ q)
      (unitGenerator_eq_point d F G (j, a))
      (unitGenerator_eq_point d (Output.functor d.tensorEnrichedFunctor F G) H (j ⊗ a, c))

omit [MonoidalCategory I] [SymmetricCategory I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original full enriched output action evaluates its identity summand
at every coefficient. -/
theorem targetAction_identityInsert (F : EnrichedFunctor V I V) (y : I) {Q : V}
    (v : Q ⟶ F.obj y) :
    AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ v) ≫
        ActionFromTransformation.targetAction F y y = v := by
  have hp : AssociatorUnit.identityInsert y (F.obj y) ≫
      ActionFromTransformation.targetAction F y y = 𝟙 (F.obj y) := by
    have h := LaxMonoid.targetAction_point F (𝟙 y)
    rw [eHomEquiv_id, Functor.map_id] at h
    exact (Category.assoc _ _ _).trans h
  have hn := AssociatorUnit.identityInsert_naturality y v
  calc
    _ = AssociatorUnit.identityInsert y Q ≫ (y ⟶[V] y) ◁ v ≫
        ActionFromTransformation.targetAction F y y :=
      congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z ≫
        ActionFromTransformation.targetAction F y y) (id_tensorHom _ v)
    _ = (AssociatorUnit.identityInsert y Q ≫ (y ⟶[V] y) ◁ v) ≫
        ActionFromTransformation.targetAction F y y := (Category.assoc _ _ _).symm
    _ = (v ≫ AssociatorUnit.identityInsert y (F.obj y)) ≫
        ActionFromTransformation.targetAction F y y :=
      congrArg (fun z => z ≫ ActionFromTransformation.targetAction F y y) hn
    _ = v ≫ (AssociatorUnit.identityInsert y (F.obj y) ≫
        ActionFromTransformation.targetAction F y y) := Category.assoc _ _ _
    _ = v := (congrArg (fun z => v ≫ z) hp).trans (Category.comp_id v)

/-- The complete target descent on its original binary source point uses
the literal σ_N κ action. -/
theorem targetDescent_source_point (M N : Module d S L) (j a c : I) :
    (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷
        (ambient d S L M N).toEnrichedFunctor.obj c) ≫
      Generators.point d.tensorEnrichedFunctor (sourceTensor d S L M).toEnrichedFunctor
        (ambient d S L M N).toEnrichedFunctor (j ⊗ a, c) ≫
      component (targetDescent d b S L M N) ((j ⊗ a) ⊗ c) =
    coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
        (S.obj a) ((ambient d S L M N).toEnrichedFunctor.obj c) ≫
      (MonoidalClosed.uncurry (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
      translatedAction d S L N c j a := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let y := (j ⊗ a) ⊗ c
  let Q := (F.toEnrichedFunctor.obj j ⊗ S.obj a) ⊗ H.toEnrichedFunctor.obj c
  let v := coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) (H.toEnrichedFunctor.obj c) ≫
    (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫
    translatedAction d S L N c j a
  change (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S (j, a) ▷
    H.toEnrichedFunctor.obj c) ≫
    Generators.point d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor
      F.toEnrichedFunctor S) H.toEnrichedFunctor (j ⊗ a, c) ≫
    component (targetDescent d b S L M N) y = v
  have hi := leftAt_identityInsert d F.toEnrichedFunctor S H.toEnrichedFunctor j a c
  have hg := targetDescent_generator_translated d b S L M N y j a c
  calc
    _ = AssociatorUnit.identityInsert y Q ≫
        BraidingTriple.leftAt d F.toEnrichedFunctor S H.toEnrichedFunctor y j a c ≫
        component (targetDescent d b S L M N) y := by
      simpa only [Category.assoc] using
        (congrArg (fun z => z ≫ component (targetDescent d b S L M N) y) hi).symm
    _ = AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ v) ≫
        ActionFromTransformation.targetAction Y.toEnrichedFunctor y y :=
      congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z) hg
    _ = v := targetAction_identityInsert Y.toEnrichedFunctor y v

/-- The original target parallel arrow evaluates each actual binary source point by σ_N κ. -/
theorem targetActionMap_source_point (M N : Module d S L) (j a c : I) :
    (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷
        (ambient d S L M N).toEnrichedFunctor.obj c) ≫
      MonoidalClosed.uncurry (component (targetActionMap d b S L M N) c ≫
        Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N) c (j ⊗ a)) =
    coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
        (S.obj a) ((ambient d S L M N).toEnrichedFunctor.obj c) ≫
      (MonoidalClosed.uncurry (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
      translatedAction d S L N c j a := by
  rw [targetActionMap_eq_transpose, Closed.transpose_component_π, MonoidalClosed.uncurry_curry]
  exact targetDescent_source_point d b S L M N j a c

omit [SymmetricCategory I] in
/-- At every whole parameter object the source pair is the unchanged source-module action. -/
theorem sourcePairComponent (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (j a : I) :
    (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
        MonoidalClosed.uncurry (sourceFamilyComponent d S L M N c t (j ⊗ a)) =
      (ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.action d S L M) j a ▷ P) ≫
        MonoidalClosed.uncurry (t.app (j ⊗ a)) := by
  rw [sourceFamilyComponent, sourceActionMap_component_π]
  have hp : ambientFamily d S L M N c t ≫
      Closed.π d (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.diagram d S L N) c (j ⊗ a) = t.app (j ⊗ a) :=
    GradingConvention.endFromPositive_symmetric_π _ _ _ (j ⊗ a)
  rw [← Category.assoc, hp]
  have hu := MonoidalClosed.uncurry_pre_app
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj ((j ⊗ a) ⊗ c))
    (t.app (j ⊗ a))
    (component (SphereModuleMappingEnd.action d S L M) (j ⊗ a))
  exact (congrArg (fun z => (Generators.point d.tensorEnrichedFunctor
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫ z) hu).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ MonoidalClosed.uncurry (t.app (j ⊗ a)))
        (comp_whiskerRight
          (Generators.point d.tensorEnrichedFunctor
            (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a))
          (component (SphereModuleMappingEnd.action d S L M) (j ⊗ a)) P).symm))

/-- The target pair at every whole parameter is its original σ_N κ action, with the actual
parameter/coefficient braid. No commutativity of the sphere coefficient is used. -/
theorem targetPairComponent (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (j a : I) :
    (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
        MonoidalClosed.uncurry (targetFamilyComponent d b S L M N c t (j ⊗ a)) =
      coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          (S.obj a) P ≫
        (MonoidalClosed.uncurry (t.app j) ▷ S.obj a) ≫ translatedAction d S L N c j a := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let Y := SphereModuleMappingEnd.diagram d S L N
  let H := ambient d S L M N
  let h := ambientFamily d S L M N c t
  let Q := F.toEnrichedFunctor.obj j ⊗ S.obj a
  let w := Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S (j, a)
  let v := component (targetActionMap d b S L M N) c ≫
    Closed.π d (sourceTensor d S L M) Y c (j ⊗ a)
  have hu : MonoidalClosed.uncurry (targetFamilyComponent d b S L M N c t (j ⊗ a)) =
      ((sourceTensor d S L M).toEnrichedFunctor.obj (j ⊗ a) ◁ h) ≫
        MonoidalClosed.uncurry v := MonoidalClosed.uncurry_natural_left h v
  have ht : (w ▷ P) ≫ ((sourceTensor d S L M).toEnrichedFunctor.obj (j ⊗ a) ◁ h) =
      (Q ◁ h) ≫ (w ▷ H.toEnrichedFunctor.obj c) :=
    (tensorHom_def w h).symm.trans (tensorHom_def' w h)
  have hp : h ≫ Closed.π d F Y c j = t.app j :=
    GradingConvention.endFromPositive_symmetric_π _ _ _ j
  have he : (F.toEnrichedFunctor.obj j ◁ h) ≫
      MonoidalClosed.uncurry (Closed.π d F Y c j) = MonoidalClosed.uncurry (t.app j) :=
    (MonoidalClosed.uncurry_natural_left h (Closed.π d F Y c j)).symm.trans
      (congrArg MonoidalClosed.uncurry hp)
  have hr : (Q ◁ h) ≫ coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a)
        (H.toEnrichedFunctor.obj c) ≫
      (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫
      translatedAction d S L N c j a =
    coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) P ≫
      (MonoidalClosed.uncurry (t.app j) ▷ S.obj a) ≫ translatedAction d S L N c j a := by
    rw [coefficient_swap_natural_assoc, ← comp_whiskerRight_assoc]
    exact congrArg (fun z => coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) P ≫
      (z ▷ S.obj a) ≫ translatedAction d S L N c j a) he
  calc
    _ = (w ▷ P) ≫ ((sourceTensor d S L M).toEnrichedFunctor.obj (j ⊗ a) ◁ h) ≫
        MonoidalClosed.uncurry v := congrArg (fun z => (w ▷ P) ≫ z) hu
    _ = (Q ◁ h) ≫ (w ▷ H.toEnrichedFunctor.obj c) ≫ MonoidalClosed.uncurry v := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ MonoidalClosed.uncurry v) ht
    _ = _ := (congrArg (fun z => (Q ◁ h) ≫ z)
      (targetActionMap_source_point d b S L M N j a c)).trans hr

/-- The full original action-end condition is exactly the literal σ_M/σ_N κ balance at every
source/coefficient pair and every whole V-parameter object. -/
theorem condition_iff_actionBalance (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) :
    (ambientFamily d S L M N c t ≫ component (sourceActionMap d S L M N) c =
      ambientFamily d S L M N c t ≫ component (targetActionMap d b S L M N) c) ↔
    (∀ j a,
      (ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.action d S L M) j a ▷ P) ≫
          MonoidalClosed.uncurry (t.app (j ⊗ a)) =
      coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          (S.obj a) P ≫
        (MonoidalClosed.uncurry (t.app j) ▷ S.obj a) ≫ translatedAction d S L N c j a) := by
  constructor
  · intro h j a
    have hp := congrArg (fun z =>
      (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
      MonoidalClosed.uncurry (z ≫ Closed.π d (sourceTensor d S L M)
        (SphereModuleMappingEnd.diagram d S L N) c (j ⊗ a))) h
    have hpair :
        (Generators.point d.tensorEnrichedFunctor
          (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
          MonoidalClosed.uncurry (sourceFamilyComponent d S L M N c t (j ⊗ a)) =
        (Generators.point d.tensorEnrichedFunctor
          (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
          MonoidalClosed.uncurry (targetFamilyComponent d b S L M N c t (j ⊗ a)) := by
      simpa only [sourceFamilyComponent, targetFamilyComponent, Category.assoc] using hp
    exact (sourcePairComponent d S L M N c t j a).symm.trans
      (hpair.trans (targetPairComponent d b S L M N c t j a))
  · intro h
    apply actionPair_hom_ext d S L M N c
    intro j a
    simpa only [sourceFamilyComponent, targetFamilyComponent, Category.assoc] using
      (sourcePairComponent d S L M N c t j a).trans
        ((h j a).trans (targetPairComponent d b S L M N c t j a).symm)

/-- Every represented original Mapping_R family has its literal full σ_N κ balance. -/
theorem Family.action_balance {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (j a : I) :
    (ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.action d S L M) j a ▷ P) ≫
        MonoidalClosed.uncurry (q.transformation.app (j ⊗ a)) =
    coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
        (S.obj a) P ≫
      (MonoidalClosed.uncurry (q.transformation.app j) ▷ S.obj a) ≫
      translatedAction d S L N c j a :=
  (condition_iff_actionBalance d b S L M N c q.transformation).1 q.condition j a

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original right triple identity summand is exactly its two unchanged nested Day points. -/
theorem rightAt_identityInsert (F G H : EnrichedFunctor V I V) (j c a : I) :
    AssociatorUnit.identityInsert (j ⊗ (c ⊗ a)) (F.obj j ⊗ (G.obj c ⊗ H.obj a)) ≫
        BraidingTriple.rightAt d F G H (j ⊗ (c ⊗ a)) j c a =
      (F.obj j ◁ Generators.point d.tensorEnrichedFunctor G H (c, a)) ≫
        Generators.point d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
          (j, c ⊗ a) := by
  let y := j ⊗ (c ⊗ a)
  let Q := F.obj j ⊗ (G.obj c ⊗ H.obj a)
  let Q' := F.obj j ⊗ EnrichedDayKernel.obj d.tensorEnrichedFunctor G H (c ⊗ a)
  let u : Q ⟶ Q' := F.obj j ◁ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (c, a)
  let g := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) y (j, c ⊗ a)
  have hf : BraidingTriple.rightAt d F G H y j c a = (𝟙 (y ⟶[V] y) ⊗ₘ u) ≫ g :=
    (AssociatorRightFlattening.rightGenerator_flatToNested d F G H y ((j, c), a)).trans
      (congrArg (fun z => (𝟙 (y ⟶[V] y) ⊗ₘ z) ≫ g)
        (id_tensorHom (F.obj j)
          (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (c, a))))
  have hi : AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ u) =
      u ≫ AssociatorUnit.identityInsert y Q' :=
    (congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z)
      (id_tensorHom (y ⟶[V] y) u)).trans (AssociatorUnit.identityInsert_naturality y u)
  calc
    _ = AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ u) ≫ g :=
      congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z) hf
    _ = (u ≫ AssociatorUnit.identityInsert y Q') ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ g) hi)
    _ = u ≫ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F
        (Output.functor d.tensorEnrichedFunctor G H) (j, c ⊗ a) := Category.assoc _ _ _
    _ = _ := congrArg₂ (fun p q => (F.obj j ◁ p) ≫ q)
      (unitGenerator_eq_point d G H (c, a))
      (unitGenerator_eq_point d F (Output.functor d.tensorEnrichedFunctor G H) (j, c ⊗ a))

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The selected Day inverse associator and arbitrary tensor maps retain their full components. -/
private theorem reassociate_component
    (F G R Y Z : EnrichedFunctorCat V I)
    (f : Closed.tensorObject d F G ⟶ Y) (g : Closed.tensorObject d Y R ⟶ Z) (k : I) :
    letI := ColimitMonoidal.monoidalCategory d
    component ((α_ F G R).inv ≫ (f ▷ R) ≫ g) k =
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor G.toEnrichedFunctor
        R.toEnrichedFunctor k).inv ≫
      Input.mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId R.toEnrichedFunctor) k ≫
      component g k := by
  let := ColimitMonoidal.monoidalCategory d
  have ha : component (α_ F G R).inv k =
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor G.toEnrichedFunctor
        R.toEnrichedFunctor k).inv :=
    (congrArg (fun e => component e.inv k) (ColimitMonoidal.associator_eq d F G R)).trans
      (AssociatorConstruction.functorIso_inv_component d F.toEnrichedFunctor G.toEnrichedFunctor
        R.toEnrichedFunctor k)
  have ht : component (f ▷ R) k =
      Input.mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId R.toEnrichedFunctor) k := by
    rw [← tensorHom_id, ColimitMonoidal.tensorHom_eq]
    exact Input.bifunctor_map_component d.tensorEnrichedFunctor f (𝟙 R) k
  rw [component_comp, component_comp]
  exact congrArg₂ (fun p q => p ≫ q) ha (congrArg (fun p => p ≫ component g k) ht)

omit [SymmetricCategory I] in
/-- The whole original output evaluation descent, before asserting invariance of the
source-action equalizer. It uses the unchanged target right action. -/
def outputDescent (M N : Module d S L) :
    Closed.tensorObject d (SphereModuleMappingEnd.diagram d S L M)
      (Closed.tensorObject d (ambient d S L M N) ⟨S⟩) ⟶
        SphereModuleMappingEnd.diagram d S L N := by
  letI := ColimitMonoidal.monoidalCategory d
  exact (α_ (SphereModuleMappingEnd.diagram d S L M) (ambient d S L M N)
    (⟨S⟩ : EnrichedFunctorCat V I)).inv ≫
    (Closed.evaluation d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N) ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫
    SphereModuleMappingEnd.action d S L N

omit [SymmetricCategory I] in
/-- The original output descent keeps the actual inverse Day associator and every target map. -/
theorem outputDescent_component (M N : Module d S L) (k : I) :
    component (outputDescent d S L M N) k =
      (AssociatorConstruction.componentIso d
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
        (ambient d S L M N).toEnrichedFunctor S k).inv ≫
      Input.mapAt d.tensorEnrichedFunctor
        (Closed.evaluation d (SphereModuleMappingEnd.diagram d S L M)
          (SphereModuleMappingEnd.diagram d S L N)) (GradedNatTrans.unitId S) k ≫
      component (SphereModuleMappingEnd.action d S L N) k := by
  let := ColimitMonoidal.monoidalCategory d
  exact reassociate_component d (SphereModuleMappingEnd.diagram d S L M)
    (ambient d S L M N) ⟨S⟩ (SphereModuleMappingEnd.diagram d S L N)
    (SphereModuleMappingEnd.diagram d S L N)
    (Closed.evaluation d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N)) (SphereModuleMappingEnd.action d S L N) k

omit [SymmetricCategory I] in
/-- Every full output generator retains the original index associator weight and coefficient
reassociation before the complete original end evaluation and target right action. -/
theorem outputDescent_generator (M N : Module d S L) (k j c a : I) :
    BraidingTriple.rightAt d (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
        (ambient d S L M N).toEnrichedFunctor S k j c a ≫
        component (outputDescent d S L M N) k =
      (eHomWhiskerRight V (α_ j c a).hom k ⊗ₘ
        (α_ ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          ((ambient d S L M N).toEnrichedFunctor.obj c) (S.obj a)).inv) ≫
      (𝟙 (((j ⊗ c) ⊗ a) ⟶[V] k) ⊗ₘ
        ((MonoidalClosed.uncurry (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
          (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
          ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
            (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a)) ≫
        ActionFromTransformation.targetAction
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor ((j ⊗ c) ⊗ a) k := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let ev := Closed.evaluation d F Y
  have ha : BraidingTriple.rightAt d F.toEnrichedFunctor H.toEnrichedFunctor S k j c a ≫
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor H.toEnrichedFunctor S k).inv =
      (eHomWhiskerRight V (α_ j c a).hom k ⊗ₘ
        (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv) ≫
        BraidingTriple.leftAt d F.toEnrichedFunctor H.toEnrichedFunctor S k j c a :=
    (Category.assoc _ _ _).trans
      (AssociatorConstruction.tripleGenerator_inv d F.toEnrichedFunctor H.toEnrichedFunctor S
        k ((j, c), a))
  have he := evaluatedTriple_action d S L F H N ev k j c a
  have hp := Closed.evaluation_point d F Y j c
  rw [outputDescent_component]
  calc
    _ = (eHomWhiskerRight V (α_ j c a).hom k ⊗ₘ
          (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv) ≫
        BraidingTriple.leftAt d F.toEnrichedFunctor H.toEnrichedFunctor S k j c a ≫
        Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k) ha
    _ = _ := (congrArg (fun z =>
      (eHomWhiskerRight V (α_ j c a).hom k ⊗ₘ
        (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv) ≫ z) he).trans
      (congrArg (fun z =>
        (eHomWhiskerRight V (α_ j c a).hom k ⊗ₘ
          (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv) ≫
        (𝟙 (((j ⊗ c) ⊗ a) ⟶[V] k) ⊗ₘ
          ((z ▷ S.obj a) ≫ ExternalRightModule.sigma d S Y
            (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a)) ≫
        ActionFromTransformation.targetAction Y.toEnrichedFunctor ((j ⊗ c) ⊗ a) k) hp)

omit [SymmetricCategory I] in
/-- The full output generator applies the original σ_N and the actual index associator,
with no loss of the output Hom weight or any coefficient object. -/
@[reassoc]
theorem outputDescent_generator_associated (M N : Module d S L) (k j c a : I) :
    BraidingTriple.rightAt d (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
        (ambient d S L M N).toEnrichedFunctor S k j c a ≫
        component (outputDescent d S L M N) k =
      (𝟙 ((j ⊗ (c ⊗ a)) ⟶[V] k) ⊗ₘ
        ((α_ ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          ((ambient d S L M N).toEnrichedFunctor.obj c) (S.obj a)).inv ≫
        (MonoidalClosed.uncurry (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
          (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
        ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
          (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
        (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
          (α_ j c a).hom)) ≫
        ActionFromTransformation.targetAction
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor (j ⊗ (c ⊗ a)) k := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let W : V := ((j ⊗ c) ⊗ a) ⟶[V] k
  let W' : V := (j ⊗ (c ⊗ a)) ⟶[V] k
  let q := (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv
  let u := (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫
    ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a
  let p := eHomWhiskerRight V (α_ j c a).hom k
  let z := ActionFromTransformation.targetAction Y.toEnrichedFunctor ((j ⊗ c) ⊗ a) k
  let z' := ActionFromTransformation.targetAction Y.toEnrichedFunctor (j ⊗ (c ⊗ a)) k
  have hg : BraidingTriple.rightAt d F.toEnrichedFunctor H.toEnrichedFunctor S k j c a ≫
      component (outputDescent d S L M N) k = (p ⊗ₘ q) ≫ (𝟙 W ⊗ₘ u) ≫ z :=
    outputDescent_generator d S L M N k j c a
  have ht : (p ⊗ₘ q) ≫ (𝟙 W ⊗ₘ u) = p ⊗ₘ (q ≫ u) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hh : p ≫ eHomWhiskerRight V (α_ j c a).inv k = 𝟙 W' :=
    (eHomWhiskerRightIso V I (α_ j c a) (Y := k)).hom_inv_id
  have hn : (p ⊗ₘ (q ≫ u)) ≫ z =
      (𝟙 W' ⊗ₘ ((q ≫ u) ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ j c a).hom)) ≫ z' := by
    have h := LaxMonoid.targetAction_sourceIso Y.toEnrichedFunctor (α_ j c a) k (q ≫ u) p
    exact h.trans (congrArg (fun w =>
      (w ⊗ₘ ((q ≫ u) ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ j c a).hom)) ≫ z') hh)
  exact hg.trans (((Category.assoc (p ⊗ₘ q) (𝟙 W ⊗ₘ u) z).symm.trans
    (congrArg (fun v => v ≫ z) ht)).trans (hn.trans
      (by simp only [F, H, Y, W', z', q, u, Category.assoc])))

omit [SymmetricCategory I] in
/-- The original output descent evaluates every actual source point with its whole parameter. -/
theorem outputDescent_source_point (M N : Module d S L) (j c a : I) :
    ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j ◁
      Generators.point d.tensorEnrichedFunctor (ambient d S L M N).toEnrichedFunctor S (c, a)) ≫
    Generators.point d.tensorEnrichedFunctor
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.tensorObject d (ambient d S L M N) ⟨S⟩).toEnrichedFunctor (j, c ⊗ a) ≫
    component (outputDescent d S L M N) (j ⊗ (c ⊗ a)) =
    (α_ ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      ((ambient d S L M N).toEnrichedFunctor.obj c) (S.obj a)).inv ≫
    (MonoidalClosed.uncurry (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
    ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
      (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
      (α_ j c a).hom := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let y := j ⊗ (c ⊗ a)
  let Q := F.toEnrichedFunctor.obj j ⊗ (H.toEnrichedFunctor.obj c ⊗ S.obj a)
  let v := (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv ≫
    (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫
    ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
    Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ j c a).hom
  change (F.toEnrichedFunctor.obj j ◁ Generators.point d.tensorEnrichedFunctor
    H.toEnrichedFunctor S (c, a)) ≫ Generators.point d.tensorEnrichedFunctor
    F.toEnrichedFunctor (Output.functor d.tensorEnrichedFunctor H.toEnrichedFunctor S)
    (j, c ⊗ a) ≫ component (outputDescent d S L M N) y = v
  have hi := rightAt_identityInsert d F.toEnrichedFunctor H.toEnrichedFunctor S j c a
  have hg := outputDescent_generator_associated d S L M N y j c a
  calc
    _ = AssociatorUnit.identityInsert y Q ≫
        BraidingTriple.rightAt d F.toEnrichedFunctor H.toEnrichedFunctor S y j c a ≫
        component (outputDescent d S L M N) y := by
      simpa only [Category.assoc] using
        (congrArg (fun z => z ≫ component (outputDescent d S L M N) y) hi).symm
    _ = AssociatorUnit.identityInsert y Q ≫ (𝟙 (y ⟶[V] y) ⊗ₘ v) ≫
        ActionFromTransformation.targetAction Y.toEnrichedFunctor y y :=
      congrArg (fun z => AssociatorUnit.identityInsert y Q ≫ z) hg
    _ = v := targetAction_identityInsert Y.toEnrichedFunctor y v

omit [SymmetricCategory I] in
/-- The original output-arrow candidate is the actual Day transpose of full evaluation descent. -/
def outputArrow (M N : Module d S L) :
    Closed.tensorObject d (ambient d S L M N) ⟨S⟩ ⟶ ambient d S L M N :=
  Closed.transpose d (SphereModuleMappingEnd.diagram d S L M)
    (Closed.tensorObject d (ambient d S L M N) ⟨S⟩)
    (SphereModuleMappingEnd.diagram d S L N) (outputDescent d S L M N)

omit [SymmetricCategory I] in
/-- Every original output-source point evaluates to the original σ_N and index associator. -/
theorem outputArrow_source_point (M N : Module d S L) (c a j : I) :
    MonoidalClosed.uncurry
      (Generators.point d.tensorEnrichedFunctor (ambient d S L M N).toEnrichedFunctor S (c, a) ≫
        component (outputArrow d S L M N) (c ⊗ a) ≫
        Closed.π d (SphereModuleMappingEnd.diagram d S L M)
          (SphereModuleMappingEnd.diagram d S L N) (c ⊗ a) j) =
    (α_ ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      ((ambient d S L M N).toEnrichedFunctor.obj c) (S.obj a)).inv ≫
    (MonoidalClosed.uncurry (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
    ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
      (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
      (α_ j c a).hom := by
  rw [outputArrow, Closed.transpose_component_π,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  exact outputDescent_source_point d S L M N j c a

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- An original whole action-linear arrow preserves every actual binary action component. -/
private theorem pair_linear {F G : EnrichedFunctorCat V I}
    (A : ExternalRightModule.Action d S F) (A' : ExternalRightModule.Action d S G)
    (i : F ⟶ G)
    (h : letI := ColimitMonoidal.monoidalCategory d
      A ≫ i = (i ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ A') (c a : I) :
    ExternalRightModule.sigma d S F A c a ≫ component i (c ⊗ a) =
      (component i c ⊗ₘ 𝟙 (S.obj a)) ≫ ExternalRightModule.sigma d S G A' c a := by
  let := ColimitMonoidal.monoidalCategory d
  have hc := congrArg (fun f => component f (c ⊗ a)) h
  rw [component_comp, component_comp] at hc
  have ht : component (i ▷ (⟨S⟩ : EnrichedFunctorCat V I)) (c ⊗ a) =
      Input.mapAt d.tensorEnrichedFunctor i (GradedNatTrans.unitId S) (c ⊗ a) := by
    rw [← tensorHom_id, ColimitMonoidal.tensorHom_eq]
    exact Input.bifunctor_map_component d.tensorEnrichedFunctor i
      (𝟙 (⟨S⟩ : EnrichedFunctorCat V I)) (c ⊗ a)
  have hp := Generators.point_input_natural d.tensorEnrichedFunctor i
    (𝟙 (⟨S⟩ : EnrichedFunctorCat V I)) (c, a)
  change Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S (c, a) ≫
    Input.mapAt d.tensorEnrichedFunctor i (GradedNatTrans.unitId S) (c ⊗ a) =
    (component i c ⊗ₘ component (𝟙 (⟨S⟩ : EnrichedFunctorCat V I)) a) ≫
      Generators.point d.tensorEnrichedFunctor G.toEnrichedFunctor S (c, a) at hp
  rw [component_id] at hp
  calc
    _ = Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S (c, a) ≫
        component A (c ⊗ a) ≫ component i (c ⊗ a) := Category.assoc _ _ _
    _ = Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S (c, a) ≫
        component (i ▷ (⟨S⟩ : EnrichedFunctorCat V I)) (c ⊗ a) ≫
        component A' (c ⊗ a) :=
      congrArg (fun z => Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S
        (c, a) ≫ z) hc
    _ = Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S (c, a) ≫
        Input.mapAt d.tensorEnrichedFunctor i (GradedNatTrans.unitId S) (c ⊗ a) ≫
        component A' (c ⊗ a) :=
      congrArg (fun z => Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor S
        (c, a) ≫ z ≫ component A' (c ⊗ a)) ht
    _ = (component i c ⊗ₘ 𝟙 (S.obj a)) ≫
        Generators.point d.tensorEnrichedFunctor G.toEnrichedFunctor S (c, a) ≫
        component A' (c ⊗ a) := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ component A' (c ⊗ a)) hp
    _ = _ := rfl

section BraidedCoefficient

variable (B : EnrichedFunctor.LaxBraidedData L)

/-- The same original translated action equalizer has its genuine original right action. -/
def moduleObject (M N : Module d S L) : Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- Its entire genuine enriched carrier is literally the original translated equalizer. -/
@[simp]
theorem moduleObject_diagram (M N : Module d S L) :
    SphereModuleMappingEnd.diagram d S L (moduleObject d b S L B M N) =
      diagram d b S L M N := rfl

/-- The original converted stock right-module Hom, used after the actual source presentation. -/
def stockModule (M N : Module d S L) : Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.stockRightHom (⟨S⟩ : EnrichedFunctorCat V I) M N

section SourceComparison

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true

/-- The proved original source/stock comparison is a whole actual right-module isomorphism. -/
def moduleComparison (M N : Module d S L) :
    moduleObject d b S L B M N ≅ stockModule d b S L B M N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  dsimp only [moduleObject, stockModule]
  exact RightModuleMappingEnd.moduleComparison (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- The original right-module mapping functor uses that same source equalizer at every target. -/
def functor (M : Module d S L) : Module d S L ⥤ Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.functor (⟨S⟩ : EnrichedFunctorCat V I) M

/-- The original converted stock target functor, with its unchanged complete module maps. -/
def stockFunctor (M : Module d S L) : Module d S L ⥤ Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.stockFunctor (⟨S⟩ : EnrichedFunctorCat V I) M

/-- The original whole source/stock module isomorphism is natural at every actual target arrow. -/
def comparisonNatIso (M : Module d S L) :
    functor d b S L B M ≅ stockFunctor d b S L B M := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.comparisonNatIso (⟨S⟩ : EnrichedFunctorCat V I) M

end SourceComparison

/-- Every full target-module arrow retains precisely the original raw source equalizer map. -/
theorem functor_map (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    SphereModuleMappingEnd.moduleMap d S L ((functor d b S L B M).map g) =
      post d b S L M g := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.map_hom (⟨S⟩ : EnrichedFunctorCat V I) M g

section SourceVariance

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true

/-- Every complete source arrow gives an actual right-module arrow on the translated end. -/
def moduleSourceMap {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L) :
    (functor d b S L B M).obj N ⟶ (functor d b S L B M').obj N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.sourceMap (⟨S⟩ : EnrichedFunctorCat V I) f N

/-- The original source identity is the complete mapping-module identity. -/
@[simp]
theorem moduleSourceMap_id (M N : Module d S L) :
    moduleSourceMap d b S L B (𝟙 M) N = 𝟙 ((functor d b S L B M).obj N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.sourceMap_id (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- The entire original source composite retains the actual contravariant module order. -/
theorem moduleSourceMap_comp {M M' M'' : Module d S L} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : Module d S L) :
    moduleSourceMap d b S L B (g ≫ f) N =
      moduleSourceMap d b S L B f N ≫ moduleSourceMap d b S L B g N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.sourceMap_comp (⟨S⟩ : EnrichedFunctorCat V I) f g N

/-- Both complete original variances commute as actual right-module arrows. -/
theorem moduleSourceMap_naturality {M M' N N' : Module d S L} (f : M' ⟶ M) (g : N ⟶ N') :
    (functor d b S L B M).map g ≫ moduleSourceMap d b S L B f N' =
      moduleSourceMap d b S L B f N ≫ (functor d b S L B M').map g := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.sourceMap_naturality (⟨S⟩ : EnrichedFunctorCat V I) f g

/-- Every complete source arrow gives the original target-natural module transformation. -/
def moduleSourceNatTrans {M M' : Module d S L} (f : M' ⟶ M) :
    functor d b S L B M ⟶ functor d b S L B M' := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.sourceNatTrans (⟨S⟩ : EnrichedFunctorCat V I) f

/-- The literal translated mapping end and its actual module maps form the whole bifunctor. -/
def moduleBifunctor : (Module d S L)ᵒᵖ ⥤ (Module d S L ⥤ Module d S L) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.bifunctor (⟨S⟩ : EnrichedFunctorCat V I)

end SourceVariance

/-- The entire original source-module arrow has exactly the original raw end precomposition. -/
theorem moduleSourceMap_hom {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L) :
    SphereModuleMappingEnd.moduleMap d S L (moduleSourceMap d b S L B f N) =
      pre d b S L f N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.sourceMap_hom (⟨S⟩ : EnrichedFunctorCat V I) f N

/-- Every whole source-module arrow retains its literal translated projection at every c and j. -/
@[reassoc]
theorem moduleSourceMap_π {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L)
    (c j : I) :
    component (SphereModuleMappingEnd.moduleMap d S L
        (moduleSourceMap d b S L B f N)) c ≫ π d b S L M' N c j =
      π d b S L M N c j ≫
        (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) := by
  rw [moduleSourceMap_hom]
  exact pre_π d b S L f N c j

/-- The whole original auxiliary right action on the actual translated ambient end. -/
def auxiliaryAction (M N : Module d S L) :
    Closed.tensorObject d (ambient d S L M N) ⟨S⟩ ⟶ ambient d S L M N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.auxiliaryRightAction (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- Uncurrying the actual converted ambient right action is the original whole output descent. -/
theorem rawAuxiliaryAction_uncurry (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    MonoidalClosed.uncurry
      (RightModuleMappingEnd.auxiliaryRightAction (⟨S⟩ : EnrichedFunctorCat V I) M N) =
        outputDescent d S L M N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  have he : (ihom.ev M.X).app N.X =
      Closed.evaluation d (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.diagram d S L N) :=
    selectedEvaluation_eq d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N)
  exact (auxiliary_right_uncurry (⟨S⟩ : EnrichedFunctorCat V I) M N).trans
    (congrArg (fun ev =>
      (α_ M.X (RightModuleMappingEnd.ambient (⟨S⟩ : EnrichedFunctorCat V I) M N)
        (⟨S⟩ : EnrichedFunctorCat V I)).inv ≫
      (ev ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ N.action) he)

/-- The actual original ambient right action is the closed-class curry of its full source
descent. -/
theorem rawAuxiliaryAction_eq_curry (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    RightModuleMappingEnd.auxiliaryRightAction (⟨S⟩ : EnrichedFunctorCat V I) M N =
      MonoidalClosed.curry (outputDescent d S L M N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact (MonoidalClosed.curry_uncurry _).symm.trans
    (congrArg MonoidalClosed.curry (rawAuxiliaryAction_uncurry d b S L B M N))

/-- The actual original ambient action is precisely the constructed whole Day output transpose. -/
theorem auxiliaryAction_eq_outputArrow (M N : Module d S L) :
    auxiliaryAction d b S L B M N = outputArrow d S L M N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  apply EnrichedFunctorCat.hom_ext
  intro c
  apply Closed.hom_ext d (SphereModuleMappingEnd.diagram d S L M)
    (SphereModuleMappingEnd.diagram d S L N) c
  intro j
  have hc := congrArg (fun f => component f c ≫
    Closed.π d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N) c j)
    (rawAuxiliaryAction_eq_curry d b S L B M N)
  exact hc.trans ((Closed.closedCurry_π d (SphereModuleMappingEnd.diagram d S L M)
    (Closed.tensorObject d (ambient d S L M N) ⟨S⟩)
    (SphereModuleMappingEnd.diagram d S L N) (outputDescent d S L M N) c j).trans
      (Closed.transpose_component_π d (SphereModuleMappingEnd.diagram d S L M)
        (Closed.tensorObject d (ambient d S L M N) ⟨S⟩)
        (SphereModuleMappingEnd.diagram d S L N) (outputDescent d S L M N) c j).symm)

/-- The actual original module action, on its proved literal translated-equalizer carrier. -/
def moduleAction (M N : Module d S L) :
    Closed.tensorObject d (diagram d b S L M N) ⟨S⟩ ⟶ diagram d b S L M N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact (RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N).action

/-- The selected raw action is the unchanged original action of the same actual module object. -/
theorem moduleAction_original (M N : Module d S L) :
    moduleAction d b S L B M N =
      SphereModuleMappingEnd.action d S L (moduleObject d b S L B M N) := rfl

/-- The original complete binary right action on the actual translated-equalizer values. -/
def moduleSigma (M N : Module d S L) (c a : I) :
    value d b S L M N c ⊗ S.obj a ⟶ value d b S L M N (c ⊗ a) :=
  ExternalRightModule.sigma d S (diagram d b S L M N) (moduleAction d b S L B M N) c a

omit [SymmetricCategory I] in
/-- The selected closed-class ambient object is the literal original translated end. -/
theorem rawAmbient_eq (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    RightModuleMappingEnd.ambient (⟨S⟩ : EnrichedFunctorCat V I) M N =
      ambient d S L M N := rfl

omit [SymmetricCategory I] in
/-- The selected closed-class action target is the literal original translated source tensor. -/
theorem rawActionTarget_eq (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    RightModuleMappingEnd.actionTarget (⟨S⟩ : EnrichedFunctorCat V I) M N =
      actionTarget d S L M N := rfl

section RawInheritedActionProjection

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true

/-- Every actual raw module action pair preserves the entire original ambient inclusion. -/
theorem rawModuleSigma_ι (M N : Module d S L) (c a : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    ExternalRightModule.sigma d S
        (RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N).X
        (RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N).action c a ≫
        component (RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N) (c ⊗ a) =
      (component (RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N) c ⊗ₘ
        𝟙 (S.obj a)) ≫
        ExternalRightModule.sigma d S
          (RightModuleMappingEnd.ambient (⟨S⟩ : EnrichedFunctorCat V I) M N)
          (RightModuleMappingEnd.auxiliaryRightAction
            (⟨S⟩ : EnrichedFunctorCat V I) M N) c a := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact pair_linear d S
    (RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N).action
    (RightModuleMappingEnd.auxiliaryRightAction (⟨S⟩ : EnrichedFunctorCat V I) M N)
    (RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N)
    (RightModuleMappingEnd.moduleObject_action_ι (⟨S⟩ : EnrichedFunctorCat V I) M N) c a

end RawInheritedActionProjection

section InheritedActionProjection

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true

/-- The whole inherited action intertwines the actual original ambient end inclusion. -/
@[reassoc]
theorem moduleSigma_valueι (M N : Module d S L) (c a : I) :
    moduleSigma d b S L B M N c a ≫ valueι d b S L M N (c ⊗ a) =
      (valueι d b S L M N c ⊗ₘ 𝟙 (S.obj a)) ≫
        Generators.point d.tensorEnrichedFunctor (ambient d S L M N).toEnrichedFunctor S (c, a) ≫
        component (auxiliaryAction d b S L B M N) (c ⊗ a) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  simpa only [moduleSigma, moduleAction, auxiliaryAction, valueι, value, ι, diagram,
    sourceActionMap, targetActionMap, RightModuleMappingEnd.moduleObject_X,
    RightModuleMappingEnd.Hom, RightModuleMappingEnd.ι, rawAmbient_eq, rawActionTarget_eq,
    ambient, Closed.rightObject, Closed.object,
    ExternalTensorMappingEndAdjunction.rightObject_obj,
    ExternalRightModule.sigma, Category.assoc] using
      rawModuleSigma_ι d b S L B M N c a

end InheritedActionProjection

/-- Every whole mapping-module output-action projection is its original end evaluation,
target σ_N and genuine index associator. -/
theorem moduleSigma_π (M N : Module d S L) (c a j : I) :
    MonoidalClosed.uncurry
      (moduleSigma d b S L B M N c a ≫ π d b S L M N (c ⊗ a) j) =
    (α_ ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      (value d b S L M N c) (S.obj a)).inv ≫
    (MonoidalClosed.uncurry (π d b S L M N c j) ▷ S.obj a) ≫
    ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
      (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
      (α_ j c a).hom := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let i : value d b S L M N c ⟶ H.toEnrichedFunctor.obj c := valueι d b S L M N c
  let tail := ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N)
    (j ⊗ c) a ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ j c a).hom
  have hs : moduleSigma d b S L B M N c a ≫ π d b S L M N (c ⊗ a) j =
      (i ⊗ₘ 𝟙 (S.obj a)) ≫
        Generators.point d.tensorEnrichedFunctor H.toEnrichedFunctor S (c, a) ≫
        component (outputArrow d S L M N) (c ⊗ a) ≫ Closed.π d F Y (c ⊗ a) j := by
    rw [π, ← Category.assoc, moduleSigma_valueι, auxiliaryAction_eq_outputArrow]
    simp only [i, F, H, Y, Category.assoc]
  have hp := outputArrow_source_point d S L M N c a j
  have he : (F.toEnrichedFunctor.obj j ◁ i) ≫
      MonoidalClosed.uncurry (Closed.π d F Y c j) =
        MonoidalClosed.uncurry (π d b S L M N c j) :=
    (MonoidalClosed.uncurry_natural_left i (Closed.π d F Y c j)).symm
  calc
    _ = (F.toEnrichedFunctor.obj j ◁ (i ⊗ₘ 𝟙 (S.obj a))) ≫
        MonoidalClosed.uncurry
          (Generators.point d.tensorEnrichedFunctor H.toEnrichedFunctor S (c, a) ≫
            component (outputArrow d S L M N) (c ⊗ a) ≫ Closed.π d F Y (c ⊗ a) j) :=
      (congrArg MonoidalClosed.uncurry hs).trans (MonoidalClosed.uncurry_natural_left _ _)
    _ = (F.toEnrichedFunctor.obj j ◁ (i ▷ S.obj a)) ≫
        (α_ (F.toEnrichedFunctor.obj j) (H.toEnrichedFunctor.obj c) (S.obj a)).inv ≫
        (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫ tail :=
      (congrArg (fun z => (F.toEnrichedFunctor.obj j ◁ z) ≫
        MonoidalClosed.uncurry
          (Generators.point d.tensorEnrichedFunctor H.toEnrichedFunctor S (c, a) ≫
            component (outputArrow d S L M N) (c ⊗ a) ≫ Closed.π d F Y (c ⊗ a) j))
        (tensorHom_id i (S.obj a))).trans
        (congrArg (fun z => (F.toEnrichedFunctor.obj j ◁ (i ▷ S.obj a)) ≫ z) hp)
    _ = (α_ (F.toEnrichedFunctor.obj j) (value d b S L M N c) (S.obj a)).inv ≫
        ((F.toEnrichedFunctor.obj j ◁ i) ▷ S.obj a) ≫
        (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫ tail := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫ tail)
        (associator_inv_naturality_middle (F.toEnrichedFunctor.obj j) i (S.obj a))
    _ = _ := by
      rw [← comp_whiskerRight_assoc]
      exact congrArg (fun z =>
        (α_ (F.toEnrichedFunctor.obj j) (value d b S L M N c) (S.obj a)).inv ≫
          (z ▷ S.obj a) ≫ tail) he

section ActionFormula

attribute [local irreducible] Closed.monoidalClosed

set_option backward.isDefEq.respectTransparency true in
/-- The actual mapping-module action retains its original full translated end inclusion. -/
@[reassoc]
theorem rawModuleAction_ι (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    (RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N).action ≫
        RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N =
      (RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N ▷
        (⟨S⟩ : EnrichedFunctorCat V I)) ≫
        RightModuleMappingEnd.auxiliaryRightAction (⟨S⟩ : EnrichedFunctorCat V I) M N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleMappingEnd.moduleObject_action_ι (⟨S⟩ : EnrichedFunctorCat V I) M N

end ActionFormula

/-- The original relative right-module tensor is built from the same Day structure and scalar. -/
@[instance_reducible]
def moduleMonoidal : MonoidalCategory (Module d S L) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)

/-- The source tensor orientation is adjoint to the original right-translation action equalizer. -/
def adjunction (M : Module d S L) :
    letI := moduleMonoidal d b S L B
    tensorRight M ⊣ functor d b S L B M := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI := moduleMonoidal d b S L B
  exact RightModuleMappingEnd.adjunction (⟨S⟩ : EnrichedFunctorCat V I) M

end BraidedCoefficient

end CategoryTheory.Enriched.ModuleMappingR
