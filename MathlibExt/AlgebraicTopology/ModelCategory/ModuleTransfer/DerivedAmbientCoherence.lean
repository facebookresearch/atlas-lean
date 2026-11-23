/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientAssociatorComputation
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorCoherence
public import Mathlib.CategoryTheory.Monoidal.Action.End

/-!
# Coherence of the actual external derived module action

The acting category is the qualified chosen monoidal structure on the exact
canonical base localization. The acted-on category is the original module
localization. Every operation, associator and unit below is the already
constructed original Q action and its actual natural comparisons.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA wC

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MorphismProperty Functor
open scoped CategoryTheory.MonObj MonoidalCategory MonoidalLeftAction

namespace HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction.Coherence

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  [IsCofibrant (𝟙_ C)] {A : C} [MonObj A] {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (tA : RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C) A) I J κA)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

open CategoryTheory.HomogeneousLocalization MonoidalOpposite

local notation "qA" => tA.replacements
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "M" => Mod C A
local notation "H" => DerivedTensorConstructions.MonoidalHo (qC)
local notation "P" => DerivedTensorConstructions.MonoidalHo.projection (qC)
local notation "HA" => MorphismProperty.Localization (moduleWeak tA)
local notation "πA" => MorphismProperty.Q (moduleWeak tA)

/-- The structure data are the actual original derived action, associator and natural unit. -/
local instance actionStruct : MonoidalLeftActionStruct H HA where
  actionObj X N := ((action tA dC).obj X).obj N
  actionHomLeft f N := ((action tA dC).map f).app N
  actionHomRight X _ _ p := ((action tA dC).obj X).map p
  actionAssocIso X Y N := (((derivedAssociator tA dC).app X).app Y).app N
  actionUnitIso N := (unitIso tA dC).app N

local instance tensorCofibrant {U V : C} [IsCofibrant U] [IsCofibrant V] : IsCofibrant (U ⊗ V) :=
  DerivedTensorConstructions.tensor_isCofibrant U V

/-- The base tensor comparison is the exact qualified original cofibrant computation. -/
def baseComparison (U V : C) [IsCofibrant U] [IsCofibrant V] :
    (P).obj U ⊗ (P).obj V ≅ (P).obj (U ⊗ V) :=
  DerivedTensorConstructions.MonoidalHo.μ (qC) U V

/-- The action comparison is the exact original coefficient/module cofibrant computation. -/
def ν (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], (P).obj U ⊙ₗ (πA).obj N ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A U N) :=
  cofibrantComparison tA dC U N

/-- Coefficient composition retains exactly the actual action functor composition. -/
@[reassoc]
theorem comp_actionHomLeft {X Y Z : H} (f : X ⟶ Y) (g : Y ⟶ Z) (N : HA) :
    (f ≫ g) ⊵ₗ N = f ⊵ₗ N ≫ g ⊵ₗ N := by
  change ((action tA dC).map (f ≫ g)).app N = _
  rw [Functor.map_comp, NatTrans.comp_app]
  rfl

/-- Module composition retains exactly the actual action functor composition. -/
@[reassoc]
theorem actionHomRight_comp (X : H) {N N' N'' : HA} (p : N ⟶ N') (q : N' ⟶ N'') :
    X ⊴ₗ (p ≫ q) = X ⊴ₗ p ≫ X ⊴ₗ q :=
  ((action tA dC).obj X).map_comp p q

/-- The actual module action preserves every identity map. -/
theorem actionHomRight_id (X : H) (N : HA) : X ⊴ₗ 𝟙 N = 𝟙 (X ⊙ₗ N) :=
  ((action tA dC).obj X).map_id N

/-- The actual coefficient action preserves every identity map. -/
theorem id_actionHomLeft (X : H) (N : HA) : 𝟙 X ⊵ₗ N = 𝟙 (X ⊙ₗ N) := by
  exact congrArg (fun a => a.app N) ((action tA dC).map_id X)

/-- Both actual action variables retain their original interchange equation. -/
@[reassoc]
theorem action_exchange {X Y : H} (f : X ⟶ Y) {N N' : HA} (p : N ⟶ N') :
    X ⊴ₗ p ≫ f ⊵ₗ N' = f ⊵ₗ N ≫ Y ⊴ₗ p :=
  ((action tA dC).map f).naturality p

/-- The actual whole derived associator is natural in the first original homotopy coefficient. -/
@[reassoc]
theorem associator_naturality_left {X X' : H} (f : X ⟶ X') (Y : H) (N : HA) :
    (f ▷ Y) ⊵ₗ N ≫ (αₗ X' Y N).hom = (αₗ X Y N).hom ≫ f ⊵ₗ (Y ⊙ₗ N) :=
  NatTrans.congr_app (NatTrans.congr_app ((derivedAssociator tA dC).hom.naturality f) Y) N

/-- The actual whole derived associator is natural in the second original homotopy coefficient. -/
@[reassoc]
theorem associator_naturality_middle (X : H) {Y Y' : H} (f : Y ⟶ Y') (N : HA) :
    (X ◁ f) ⊵ₗ N ≫ (αₗ X Y' N).hom = (αₗ X Y N).hom ≫ X ⊴ₗ (f ⊵ₗ N) :=
  NatTrans.congr_app (((derivedAssociator tA dC).hom.app X).naturality f) N

/-- The actual whole derived associator is natural in every original module homotopy arrow. -/
@[reassoc]
theorem associator_naturality_right (X Y : H) {N N' : HA} (p : N ⟶ N') :
    (X ⊗ Y) ⊴ₗ p ≫ (αₗ X Y N').hom = (αₗ X Y N).hom ≫ X ⊴ₗ (Y ⊴ₗ p) :=
  (((derivedAssociator tA dC).hom.app X).app Y).naturality p

/-- The original action computation retains every cofibrant coefficient map. -/
@[reassoc]
theorem ν_natural_coefficient {U V : C} (f : U ⟶ V) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      (P).map f ⊵ₗ (πA).obj N ≫ (ν tA dC V N).hom =
        (ν tA dC U N).hom ≫ (πA).map (Mod.AmbientTensor.map A f (𝟙 N)) := by
  let : ModelCategory M := tA.model
  intro hN
  exact cofibrantComparison_naturality_coefficient tA dC f N

/-- The original action computation retains every cofibrant module map. -/
@[reassoc]
theorem ν_natural_module (U : C) [IsCofibrant U] {N N' : M} (p : N ⟶ N') :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N] [_hN' : IsCofibrant N'],
      (P).obj U ⊴ₗ (πA).map p ≫ (ν tA dC U N').hom =
        (ν tA dC U N).hom ≫ (πA).map ((Mod.AmbientTensor.functor A U).map p) := by
  let : ModelCategory M := tA.model
  intro hN hN'
  exact cofibrantComparison_naturality_module tA dC U p

/-- The inverse computation retains the same actual cofibrant module map. -/
@[reassoc]
theorem ν_inv_natural_module (U : C) [IsCofibrant U] {N N' : M} (p : N ⟶ N') :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N] [_hN' : IsCofibrant N'],
      (πA).map ((Mod.AmbientTensor.functor A U).map p) ≫ (ν tA dC U N').inv =
        (ν tA dC U N).inv ≫ (P).obj U ⊴ₗ (πA).map p := by
  let : ModelCategory M := tA.model
  intro hN hN'
  apply (cancel_epi (ν tA dC U N).hom).mp
  rw [← ν_natural_module_assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual derived module associator is the original module associator between both computations. -/
theorem associator_hom_app (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      letI : IsCofibrant (Mod.AmbientTensor.tensorModule A V N) := tensorModule_isCofibrant tA V N inferInstance
      (αₗ ((P).obj U) ((P).obj V) ((πA).obj N)).hom =
        (baseComparison dC U V).hom ⊵ₗ (πA).obj N ≫ (ν tA dC (U ⊗ V) N).hom ≫
          (πA).map (AmbientActionPointSet.associate U V N).hom ≫
          (ν tA dC U (Mod.AmbientTensor.tensorModule A V N)).inv ≫
          (P).obj U ⊴ₗ (ν tA dC V N).inv := by
  let : ModelCategory M := tA.model
  intro hN
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A V N) := tensorModule_isCofibrant tA V N hN
  have h := derivedAssociator_cofibrant tA dC U V N
  dsimp [leftCofibrantComparison, rightCofibrantComparison] at h
  simp only [Category.assoc] at h
  exact h

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- The actual original action takes values in the monoidal opposite of its endofunctors. -/
def actionMop : H ⥤ (HA ⥤ HA)ᴹᵒᵖ := action tA dC ⋙ mopFunctor _

/-- The complete actual derived module associator is the whole two-variable oplax tensor Iso. -/
def δIso : curriedTensorPost (actionMop tA dC) ≅ curriedTensorPre (actionMop tA dC) :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun Y => (mopFunctor (HA ⥤ HA)).mapIso (((derivedAssociator tA dC).app X).app Y)) (by
        intro Y Y' f
        apply MonoidalOpposite.hom_ext
        exact (((derivedAssociator tA dC).hom.app X).naturality f))) (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      apply MonoidalOpposite.hom_ext
      exact NatTrans.congr_app ((derivedAssociator tA dC).hom.naturality f) Y)

/-- Both actual derived action pentagon paths agree on the original cofibrant source objects. -/
theorem pentagon_cofibrant (U V W : C) [IsCofibrant U] [IsCofibrant V] [IsCofibrant W] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      (αₗ ((P).obj U ⊗ (P).obj V) ((P).obj W) ((πA).obj N)).hom ≫
          (αₗ ((P).obj U) ((P).obj V) ((P).obj W ⊙ₗ (πA).obj N)).hom =
        (α_ ((P).obj U) ((P).obj V) ((P).obj W)).hom ⊵ₗ (πA).obj N ≫
          (αₗ ((P).obj U) ((P).obj V ⊗ (P).obj W) ((πA).obj N)).hom ≫
          (P).obj U ⊴ₗ (αₗ ((P).obj V) ((P).obj W) ((πA).obj N)).hom := by
  let : ModelCategory M := tA.model
  intro hN
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A W N) := tensorModule_isCofibrant tA W N hN
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A V (Mod.AmbientTensor.tensorModule A W N)) :=
    tensorModule_isCofibrant tA V _ inferInstance
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A (V ⊗ W) N) :=
    tensorModule_isCofibrant tA (V ⊗ W) N hN
  have hci {X Y : H} (e : X ≅ Y) (E : HA) :
      e.inv ⊵ₗ E ≫ e.hom ⊵ₗ E = 𝟙 (Y ⊙ₗ E) :=
    Iso.map_inv_hom_id_app e (action tA dC) E
  have hmi (X : H) {E E' : HA} (e : E ≅ E') :
      X ⊴ₗ e.inv ≫ X ⊴ₗ e.hom = 𝟙 (X ⊙ₗ E') := by
    rw [← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]
  have h₁ : (((baseComparison dC U V).hom ▷ (P).obj W) ⊵ₗ (πA).obj N) ≫
        (αₗ ((P).obj (U ⊗ V)) ((P).obj W) ((πA).obj N)).hom ≫
        (baseComparison dC U V).inv ⊵ₗ ((P).obj W ⊙ₗ (πA).obj N) =
      (αₗ ((P).obj U ⊗ (P).obj V) ((P).obj W) ((πA).obj N)).hom := by
    simp only [associator_naturality_left_assoc, ← comp_actionHomLeft,
      Iso.hom_inv_id, id_actionHomLeft, Category.comp_id]
  have h₂ : (((P).obj U ◁ (baseComparison dC V W).inv) ⊵ₗ (πA).obj N) ≫
        (αₗ ((P).obj U) ((P).obj V ⊗ (P).obj W) ((πA).obj N)).hom ≫
        (P).obj U ⊴ₗ ((baseComparison dC V W).hom ⊵ₗ (πA).obj N) =
      (αₗ ((P).obj U) ((P).obj (V ⊗ W)) ((πA).obj N)).hom := by
    simp only [associator_naturality_middle_assoc, ← actionHomRight_comp,
      ← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft, actionHomRight_id,
      Category.comp_id]
  have h₃ : (((P).obj U ⊗ (P).obj V) ⊴ₗ (ν tA dC W N).hom) ≫
        (αₗ ((P).obj U) ((P).obj V) ((πA).obj (Mod.AmbientTensor.tensorModule A W N))).hom ≫
        (P).obj U ⊴ₗ ((P).obj V ⊴ₗ (ν tA dC W N).inv) =
      (αₗ ((P).obj U) ((P).obj V) ((P).obj W ⊙ₗ (πA).obj N)).hom := by
    simp only [associator_naturality_right_assoc, ← actionHomRight_comp,
      Iso.hom_inv_id, actionHomRight_id, Category.comp_id]
  have h₄ : ((P).obj (U ⊗ V) ⊴ₗ (ν tA dC W N).inv) ≫
        (baseComparison dC U V).inv ⊵ₗ ((P).obj W ⊙ₗ (πA).obj N) ≫
        ((P).obj U ⊗ (P).obj V) ⊴ₗ (ν tA dC W N).hom ≫
        (baseComparison dC U V).hom ⊵ₗ (πA).obj (Mod.AmbientTensor.tensorModule A W N) = 𝟙 _ := by
    rw [← action_exchange_assoc]
    simp only [← actionHomRight_comp_assoc, Iso.inv_hom_id, actionHomRight_id,
      Category.id_comp, hci]
  rw [DerivedTensorConstructions.MonoidalHo.associator_hom_app,
    associator_hom_app tA dC V W N]
  simp only [comp_actionHomLeft, actionHomRight_comp, Category.assoc]
  erw [reassoc_of% h₂, associator_hom_app tA dC U (V ⊗ W) N, ← h₁, ← h₃,
    associator_hom_app tA dC (U ⊗ V) W N,
    associator_hom_app tA dC U V (Mod.AmbientTensor.tensorModule A W N)]
  dsimp only [baseComparison]
  simp only [Category.assoc, reassoc_of% hci, reassoc_of% hmi]
  erw [reassoc_of% h₄]
  simp only [Iso.inv_hom_id_assoc]
  erw [ν_natural_coefficient_assoc, ← ν_inv_natural_module_assoc]
  simp only [← (πA).map_comp_assoc]
  rw [AmbientActionPointSet.pentagon]

/-- The entire oplax associativity transformation satisfies the actual module pentagon. -/
theorem pentagon_natTrans :
    OplaxMonoidal.ofBifunctor.firstMap (δIso tA dC).hom =
      OplaxMonoidal.ofBifunctor.secondMap (δIso tA dC).hom := by
  apply GeneratedFunctorialReplacements.natTrans₃_ext_cofibrant (qC)
  intro U V W _ _ _
  apply MonoidalOpposite.hom_ext
  let : ModelCategory M := tA.model
  apply GeneratedFunctorialReplacements.natTrans_ext_cofibrant (qA)
  intro N hN
  change (αₗ ((P).obj U ⊗ (P).obj V) ((P).obj W) ((πA).obj N)).hom ≫
        (αₗ ((P).obj U) ((P).obj V) ((P).obj W ⊙ₗ (πA).obj N)).hom ≫ 𝟙 _ =
      (α_ ((P).obj U) ((P).obj V) ((P).obj W)).hom ⊵ₗ (πA).obj N ≫
        (αₗ ((P).obj U) ((P).obj V ⊗ (P).obj W) ((πA).obj N)).hom ≫
        (P).obj U ⊴ₗ (αₗ ((P).obj V) ((P).obj W) ((πA).obj N)).hom
  rw [Category.comp_id]
  exact pentagon_cofibrant tA dC U V W N

/-- The whole derived unit retains the original two-counit comparison and actual module unit. -/
theorem unit_hom_source (N : M) :
    letI : ModelCategory M := tA.model
    (unitIso tA dC).hom.app ((πA).obj N) = ordinaryComparison tA dC (𝟙_ C) N ≫
      (πA).map ((AmbientActionPointSet.unitNatIso (A := A)).hom.app N :
        Mod.AmbientTensor.tensorModule A (𝟙_ C) N ⟶ N) := by
  let : ModelCategory M := tA.model
  have hu : Mod.AmbientTensor.map A ((qC).q.app (𝟙_ C)) (𝟙 ((qA).Q.obj N)) ≫
        (pointSetLeftUnit (A := A)).hom.app ((qA).Q.obj N) ≫ (qA).q.app N =
      Mod.AmbientTensor.map A ((qC).q.app (𝟙_ C)) ((qA).q.app N) ≫
        (pointSetLeftUnit (A := A)).hom.app N := by
    erw [← (pointSetLeftUnit (A := A)).hom.naturality ((qA).q.app N)]
    erw [← Category.assoc, ← Mod.AmbientTensor.map_comp, Category.comp_id, Category.id_comp]
    rfl
  change (unitIso tA dC).hom.app ((πA).obj N) = _
  rw [unitIso_hom_app]
  dsimp [unitComparison, rawUnitMap, ordinaryComparison, ordinaryComparisonMap,
    AmbientActionPointSet.unitNatIso]
  simp only [Category.assoc, ← (πA).map_comp]
  erw [hu]

/-- On actual cofibrant modules the same unit is the ordinary module unit between computations. -/
theorem unit_hom_cofibrant (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], (λₗ ((πA).obj N)).hom =
      (ν tA dC (𝟙_ C) N).hom ≫
        (πA).map ((AmbientActionPointSet.unitNatIso (A := A)).hom.app N :
          Mod.AmbientTensor.tensorModule A (𝟙_ C) N ⟶ N) := by
  let : ModelCategory M := tA.model
  intro hN
  exact unit_hom_source tA dC N

/-- The original natural unit commutes with every actual module homotopy arrow. -/
@[reassoc]
theorem unit_naturality {N N' : HA} (p : N ⟶ N') :
    (𝟙_ H) ⊴ₗ p ≫ (λₗ N').hom = (λₗ N).hom ≫ p :=
  (unitIso tA dC).hom.naturality p

/-- The derived coefficient left unit agrees with the original module unit and associator. -/
theorem left_unit_cofibrant (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      (αₗ (𝟙_ H) ((P).obj U) ((πA).obj N)).hom ≫
          (λₗ ((P).obj U ⊙ₗ (πA).obj N)).hom =
        (λ_ ((P).obj U)).hom ⊵ₗ (πA).obj N := by
  let : ModelCategory M := tA.model
  intro hN
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A U N) := tensorModule_isCofibrant tA U N hN
  have hbase : (λ_ ((P).obj U)).hom =
      (baseComparison dC (𝟙_ C) U).hom ≫ (P).map (λ_ U).hom :=
    DerivedTensorConstructions.derivedLeftUnitor_hom_source (qC) U
  apply (cancel_mono (ν tA dC U N).hom).mp
  rw [Category.assoc, ← unit_naturality]
  change (αₗ ((P).obj (𝟙_ C)) ((P).obj U) ((πA).obj N)).hom ≫
      (P).obj (𝟙_ C) ⊴ₗ (ν tA dC U N).hom ≫
      (λₗ ((πA).obj (Mod.AmbientTensor.tensorModule A U N))).hom = _
  rw [associator_hom_app, unit_hom_cofibrant, hbase, comp_actionHomLeft]
  simp only [Category.assoc, ← actionHomRight_comp_assoc, Iso.inv_hom_id,
    actionHomRight_id, Category.id_comp, Iso.inv_hom_id_assoc]
  erw [← (πA).map_comp, AmbientActionPointSet.left_unit, ν_natural_coefficient]

/-- The derived coefficient right unit agrees with the original module unit and associator. -/
theorem right_unit_cofibrant (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      (αₗ ((P).obj U) (𝟙_ H) ((πA).obj N)).hom ≫
          (P).obj U ⊴ₗ (λₗ ((πA).obj N)).hom =
        (ρ_ ((P).obj U)).hom ⊵ₗ (πA).obj N := by
  let : ModelCategory M := tA.model
  intro hN
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A (𝟙_ C) N) :=
    tensorModule_isCofibrant tA (𝟙_ C) N hN
  have hbase : (ρ_ ((P).obj U)).hom =
      (baseComparison dC U (𝟙_ C)).hom ≫ (P).map (ρ_ U).hom :=
    DerivedTensorConstructions.derivedRightUnitor_hom_source (qC) U
  apply (cancel_mono (ν tA dC U N).hom).mp
  rw [Category.assoc]
  change (αₗ ((P).obj U) ((P).obj (𝟙_ C)) ((πA).obj N)).hom ≫
      (P).obj U ⊴ₗ (λₗ ((πA).obj N)).hom ≫ (ν tA dC U N).hom = _
  rw [associator_hom_app, unit_hom_cofibrant, hbase, comp_actionHomLeft,
    actionHomRight_comp]
  simp only [Category.assoc, ← actionHomRight_comp_assoc, Iso.inv_hom_id_assoc]
  erw [ν_natural_module]
  simp only [Iso.inv_hom_id_assoc]
  erw [← (πA).map_comp, AmbientActionPointSet.right_unit, ν_natural_coefficient]

/-- The original whole natural module unit is the oplax unit in the exact endofunctor category. -/
def unitMopIso : (actionMop tA dC).obj (𝟙_ H) ≅ 𝟙_ ((HA ⥤ HA)ᴹᵒᵖ) :=
  (mopFunctor (HA ⥤ HA)).mapIso (unitIso tA dC)

/-- The complete left unit transformation holds on every original localized coefficient and module. -/
theorem left_unit_natTrans :
    OplaxMonoidal.ofBifunctor.leftMapₗ (actionMop tA dC) =
      OplaxMonoidal.ofBifunctor.topMapₗ (actionMop tA dC) ≫
        (δIso tA dC).hom.app (𝟙_ H) ≫
        OplaxMonoidal.ofBifunctor.bottomMapₗ (unitMopIso tA dC).hom := by
  apply GeneratedFunctorialReplacements.natTrans_ext_cofibrant (qC)
  intro U _
  apply MonoidalOpposite.hom_ext
  let : ModelCategory M := tA.model
  apply GeneratedFunctorialReplacements.natTrans_ext_cofibrant (qA)
  intro N hN
  change 𝟙 ((P).obj U ⊙ₗ (πA).obj N) =
    (λ_ ((P).obj U)).inv ⊵ₗ (πA).obj N ≫
      (αₗ (𝟙_ H) ((P).obj U) ((πA).obj N)).hom ≫
      (λₗ ((P).obj U ⊙ₗ (πA).obj N)).hom
  rw [left_unit_cofibrant, ← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

/-- The complete right unit transformation holds on the same original two homotopy categories. -/
theorem right_unit_natTrans :
    OplaxMonoidal.ofBifunctor.leftMapᵣ (actionMop tA dC) =
      OplaxMonoidal.ofBifunctor.topMapᵣ (actionMop tA dC) ≫
        ((flipFunctor _ _ _).map (δIso tA dC).hom).app (𝟙_ H) ≫
        OplaxMonoidal.ofBifunctor.bottomMapᵣ (unitMopIso tA dC).hom := by
  apply GeneratedFunctorialReplacements.natTrans_ext_cofibrant (qC)
  intro U _
  apply MonoidalOpposite.hom_ext
  let : ModelCategory M := tA.model
  apply GeneratedFunctorialReplacements.natTrans_ext_cofibrant (qA)
  intro N hN
  change 𝟙 ((P).obj U ⊙ₗ (πA).obj N) =
    (ρ_ ((P).obj U)).inv ⊵ₗ (πA).obj N ≫
      (αₗ ((P).obj U) (𝟙_ H) ((πA).obj N)).hom ≫
      (P).obj U ⊴ₗ (λₗ ((πA).obj N)).hom
  rw [right_unit_cofibrant, ← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

/-- The actual derived action, its original unit and full associator give a strong monoidal functor. -/
def actionCoreMonoidal : (actionMop tA dC).CoreMonoidal := by
  refine Functor.CoreMonoidal.mk' (unitMopIso tA dC).symm
    (fun X Y => (((δIso tA dC).app X).app Y).symm) ?_ ?_ ?_ ?_ ?_
  · intro X Y f X'
    exact (NatTrans.congr_app ((δIso tA dC).hom.naturality f) X').symm
  · intro X Y X' f
    exact (((δIso tA dC).hom.app X').naturality f).symm
  · intro X Y Z
    exact NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app
      (pentagon_natTrans tA dC) X) Y) Z
  · intro X
    exact NatTrans.congr_app (left_unit_natTrans tA dC) X
  · intro X
    exact NatTrans.congr_app (right_unit_natTrans tA dC) X

/-- The canonical base homotopy category acts coherently on the original localized module category. -/
@[instance_reducible]
def monoidalAction : MonoidalLeftAction H HA := by
  letI : (actionMop tA dC).Monoidal := (actionCoreMonoidal tA dC).toMonoidal
  exact MonoidalLeftAction.actionOfMonoidalFunctorToEndofunctorMop (actionMop tA dC)

/-- The bundled action retains the original full derived object function. -/
theorem monoidalAction_obj (X : H) (N : HA) :
    letI := monoidalAction tA dC
    X ⊙ₗ N = ((action tA dC).obj X).obj N := rfl

/-- The bundled action retains the original full coefficient morphism function. -/
theorem monoidalAction_map_coefficient {X Y : H} (f : X ⟶ Y) (N : HA) :
    letI := monoidalAction tA dC
    f ⊵ₗ N = ((action tA dC).map f).app N := rfl

/-- The bundled action retains the original full module morphism function. -/
theorem monoidalAction_map_module (X : H) {N N' : HA} (p : N ⟶ N') :
    letI := monoidalAction tA dC
    X ⊴ₗ p = ((action tA dC).obj X).map p := rfl

/-- The complete bundled associator is exactly the previously constructed three-variable Iso. -/
theorem monoidalAction_associator (X Y : H) (N : HA) :
    letI := monoidalAction tA dC
    αₗ X Y N = (((derivedAssociator tA dC).app X).app Y).app N := rfl

/-- The complete bundled unit is exactly the previously constructed natural unit Iso. -/
theorem monoidalAction_unit (N : HA) :
    letI := monoidalAction tA dC
    λₗ[H] N = (unitIso tA dC).app N := rfl

/-- The actual bundled action retains the original module associator between both computations. -/
theorem monoidalAction_associator_cofibrant (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI := monoidalAction tA dC
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      letI : IsCofibrant (Mod.AmbientTensor.tensorModule A V N) := tensorModule_isCofibrant tA V N inferInstance
      (αₗ ((P).obj U) ((P).obj V) ((πA).obj N)).hom =
        (baseComparison dC U V).hom ⊵ₗ (πA).obj N ≫ (ν tA dC (U ⊗ V) N).hom ≫
          (πA).map (AmbientActionPointSet.associate U V N).hom ≫
          (ν tA dC U (Mod.AmbientTensor.tensorModule A V N)).inv ≫
          (P).obj U ⊴ₗ (ν tA dC V N).inv := by
  let : ModelCategory M := tA.model
  intro hN
  exact associator_hom_app tA dC U V N

/-- The actual bundled unit retains its source module-unit calculation. -/
theorem monoidalAction_unit_cofibrant (N : M) :
    letI := monoidalAction tA dC
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], (λₗ ((πA).obj N)).hom =
      (ν tA dC (𝟙_ C) N).hom ≫
        (πA).map ((AmbientActionPointSet.unitNatIso (A := A)).hom.app N :
          Mod.AmbientTensor.tensorModule A (𝟙_ C) N ⟶ N) := by
  let : ModelCategory M := tA.model
  intro hN
  exact unit_hom_cofibrant tA dC N

end HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction.Coherence
