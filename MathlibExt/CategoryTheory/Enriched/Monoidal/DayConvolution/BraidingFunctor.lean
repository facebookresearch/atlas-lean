/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingComponents
public import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso

/-!
# The actual Day braid as an enriched natural isomorphism

Full output Hom composition commutes with the original index and coefficient
braids. The descended coend components consequently define an isomorphism
between the unchanged genuine Day output functors.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingFunctor

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (F G : EnrichedFunctor V I V)

/-- The entire curried output Hom action commutes with the actual descended Day braid. -/
theorem actionDesc_natural (k l : I) :
    Output.actionDesc d.tensorEnrichedFunctor F G k l ≫
        (ihom (k ⟶[V] l)).map (BraidingComponents.component d b F G l) =
      BraidingComponents.component d b F G k ≫
        Output.actionDesc d.tensorEnrichedFunctor G F k l := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor F G k
  intro X
  let H : V := k ⟶[V] l
  let x : I := X.1 ⊗ X.2
  let y : I := X.2 ⊗ X.1
  let Q : V := F.obj X.1 ⊗ G.obj X.2
  let R : V := G.obj X.2 ⊗ F.obj X.1
  let A : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k
  let B : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor G F k
  let A' : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G l
  let B' : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor G F l
  let γ : (x ⟶[V] k) ⊗ Q ⟶ A := gen d.tensorEnrichedFunctor F G k X
  let δ : (y ⟶[V] k) ⊗ R ⟶ B := gen d.tensorEnrichedFunctor G F k (X.2, X.1)
  let γ' : (x ⟶[V] l) ⊗ Q ⟶ A' := gen d.tensorEnrichedFunctor F G l X
  let δ' : (y ⟶[V] l) ⊗ R ⟶ B' := gen d.tensorEnrichedFunctor G F l (X.2, X.1)
  let c : A ⟶ B := BraidingComponents.component d b F G k
  let c' : A' ⟶ B' := BraidingComponents.component d b F G l
  let s : (x ⟶[V] k) ⊗ Q ⟶ (y ⟶[V] k) ⊗ R :=
    eHomWhiskerRight V (β_ X.1 X.2).inv k ⊗ₘ (β_ (F.obj X.1) (G.obj X.2)).hom
  let s' : (x ⟶[V] l) ⊗ Q ⟶ (y ⟶[V] l) ⊗ R :=
    eHomWhiskerRight V (β_ X.1 X.2).inv l ⊗ₘ (β_ (F.obj X.1) (G.obj X.2)).hom
  let a : H ⊗ ((x ⟶[V] k) ⊗ Q) ⟶ A' := Output.outputAction x k l Q ≫ γ'
  let a' : H ⊗ ((y ⟶[V] k) ⊗ R) ⟶ B' := Output.outputAction y k l R ≫ δ'
  let f : A ⟶ (ihom H).obj A' := Output.actionDesc d.tensorEnrichedFunctor F G k l
  let g : B ⟶ (ihom H).obj B' := Output.actionDesc d.tensorEnrichedFunctor G F k l
  have hm : γ ≫ c = s ≫ δ := BraidingComponents.gen_component d b F G k X
  have hm' : γ' ≫ c' = s' ≫ δ' := BraidingComponents.gen_component d b F G l X
  have hf : γ ≫ f = MonoidalClosed.curry a :=
    Output.gen_actionDesc d.tensorEnrichedFunctor F G k l X
  have hg : δ ≫ g = MonoidalClosed.curry a' :=
    Output.gen_actionDesc d.tensorEnrichedFunctor G F k l (X.2, X.1)
  have hp : H ◁ s ≫ Output.outputAction y k l R = Output.outputAction x k l Q ≫ s' :=
    AssociatorNaturality.outputAction_precomposition (β_ X.1 X.2).inv k l
      (β_ (F.obj X.1) (G.obj X.2)).hom
  have ha : a ≫ c' = H ◁ s ≫ a' := by
    calc
      _ = Output.outputAction x k l Q ≫ s' ≫ δ' := by
        exact (Category.assoc (Output.outputAction x k l Q) γ' c').trans
          (congrArg (fun t => Output.outputAction x k l Q ≫ t) hm')
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ δ') hp.symm
  change γ ≫ (f ≫ (ihom H).map c') = γ ≫ (c ≫ g)
  calc
    _ = MonoidalClosed.curry a ≫ (ihom H).map c' := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ (ihom H).map c') hf
    _ = MonoidalClosed.curry (a ≫ c') := (MonoidalClosed.curry_natural_right a c').symm
    _ = MonoidalClosed.curry (H ◁ s ≫ a') := congrArg MonoidalClosed.curry ha
    _ = s ≫ MonoidalClosed.curry a' := MonoidalClosed.curry_natural_left s a'
    _ = s ≫ δ ≫ g := by
      simpa only [Category.assoc] using congrArg (fun t => s ≫ t) hg.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ g) hm.symm

/-- The genuine enriched output maps commute on the complete original output Hom object. -/
theorem full_naturality (k l : I) :
    MonoidalClosed.uncurry ((Output.functor d.tensorEnrichedFunctor F G).map k l) ≫
        BraidingComponents.component d b F G l =
      (BraidingComponents.component d b F G k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫
        MonoidalClosed.uncurry ((Output.functor d.tensorEnrichedFunctor G F).map k l) := by
  let H : V := k ⟶[V] l
  let A : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k
  let B : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor G F k
  let c : A ⟶ B := BraidingComponents.component d b F G k
  let c' := BraidingComponents.component d b F G l
  have hn := congrArg MonoidalClosed.uncurry (actionDesc_natural d b F G k l)
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_left] at hn
  have hb : (β_ H A).inv ≫ H ◁ c = (c ⊗ₘ 𝟙 H) ≫ (β_ H B).inv := by
    simpa only [tensorHom_id] using (braiding_inv_naturality_left c H).symm
  rw [Output.map_uncurry, Output.map_uncurry]
  calc
    _ = (β_ H A).inv ≫ H ◁ c ≫
        MonoidalClosed.uncurry (Output.actionDesc d.tensorEnrichedFunctor G F k l) := by
      simpa only [Category.assoc] using congrArg (fun t => (β_ H A).inv ≫ t) hn
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ MonoidalClosed.uncurry
          (Output.actionDesc d.tensorEnrichedFunctor G F k l)) hb

/-- The original continuous Day braiding on the unchanged enriched functor objects. -/
def functorIso :
    (⟨Output.functor d.tensorEnrichedFunctor F G⟩ : EnrichedFunctorCat V I) ≅
      ⟨Output.functor d.tensorEnrichedFunctor G F⟩ :=
  EnrichedFunctorCat.isoOfComponents _ _ (BraidingComponents.componentIso d b F G)
    (full_naturality d b F G)

/-- The entire forward component is the actual balanced coend braiding. -/
@[simp]
theorem functorIso_hom_component (k : I) :
    EnrichedFunctorCat.component (functorIso d b F G).hom k =
      BraidingComponents.component d b F G k :=
  EnrichedFunctorCat.isoOfComponents_hom_component _ _ _ _ k

/-- The entire inverse component is the original braid with the two inputs reversed. -/
@[simp]
theorem functorIso_inv_component (k : I) :
    EnrichedFunctorCat.component (functorIso d b F G).inv k =
      BraidingComponents.component d b G F k :=
  EnrichedFunctorCat.isoOfComponents_inv_component _ _ _ _ k

end CategoryTheory.EnrichedDayKernel.BraidingFunctor
