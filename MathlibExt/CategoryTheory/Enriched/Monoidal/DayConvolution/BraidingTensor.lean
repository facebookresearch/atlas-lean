/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingFunctor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor

/-!
# Full input naturality of the actual Day braiding

The original coend input maps commute with the actual index/coefficient
braids. This gives the naturality needed by the unchanged Day tensor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingTensor

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  {F F' G G' : EnrichedFunctor V I V}

/-- Every entire input map commutes with the original full coend braid. -/
theorem component_natural
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
    (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G') (k : I) :
    Input.mapAt d.tensorEnrichedFunctor a c k ≫ BraidingComponents.component d b F' G' k =
      BraidingComponents.component d b F G k ≫ Input.mapAt d.tensorEnrichedFunctor c a k := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor F G k
  intro X
  let H : V := (X.1 ⊗ X.2) ⟶[V] k
  let K : V := (X.2 ⊗ X.1) ⟶[V] k
  let Q : V := F.obj X.1 ⊗ G.obj X.2
  let R : V := G.obj X.2 ⊗ F.obj X.1
  let Q' : V := F'.obj X.1 ⊗ G'.obj X.2
  let R' : V := G'.obj X.2 ⊗ F'.obj X.1
  let γ : H ⊗ Q ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k :=
    gen d.tensorEnrichedFunctor F G k X
  let γ' : H ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F' G' k :=
    gen d.tensorEnrichedFunctor F' G' k X
  let δ : K ⊗ R ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor G F k :=
    gen d.tensorEnrichedFunctor G F k (X.2, X.1)
  let δ' : K ⊗ R' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor G' F' k :=
    gen d.tensorEnrichedFunctor G' F' k (X.2, X.1)
  let f : F.obj X.1 ⟶ F'.obj X.1 := (eHomEquiv V).symm (a.app X.1)
  let g : G.obj X.2 ⟶ G'.obj X.2 := (eHomEquiv V).symm (c.app X.2)
  let w : H ⟶ K := eHomWhiskerRight V (β_ X.1 X.2).inv k
  let v : Q ⟶ R := (β_ (F.obj X.1) (G.obj X.2)).hom
  let v' : Q' ⟶ R' := (β_ (F'.obj X.1) (G'.obj X.2)).hom
  let m := Input.mapAt d.tensorEnrichedFunctor a c k
  let n := Input.mapAt d.tensorEnrichedFunctor c a k
  let t := BraidingComponents.component d b F G k
  let t' := BraidingComponents.component d b F' G' k
  have hm : γ ≫ m = (𝟙 H ⊗ₘ (f ⊗ₘ g)) ≫ γ' := Input.gen_mapAt d.tensorEnrichedFunctor a c k X
  have hn : δ ≫ n = (𝟙 K ⊗ₘ (g ⊗ₘ f)) ≫ δ' :=
    Input.gen_mapAt d.tensorEnrichedFunctor c a k (X.2, X.1)
  have ht : γ ≫ t = (w ⊗ₘ v) ≫ δ := BraidingComponents.gen_component d b F G k X
  have ht' : γ' ≫ t' = (w ⊗ₘ v') ≫ δ' := BraidingComponents.gen_component d b F' G' k X
  have hv : (f ⊗ₘ g) ≫ v' = v ≫ (g ⊗ₘ f) := braiding_naturality f g
  have hleft : (𝟙 H ⊗ₘ (f ⊗ₘ g)) ≫ (w ⊗ₘ v') = w ⊗ₘ ((f ⊗ₘ g) ≫ v') := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  have hright : (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ (g ⊗ₘ f)) = w ⊗ₘ (v ≫ (g ⊗ₘ f)) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  change γ ≫ m ≫ t' = γ ≫ t ≫ n
  calc
    _ = (𝟙 H ⊗ₘ (f ⊗ₘ g)) ≫ γ' ≫ t' := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ t') hm
    _ = (𝟙 H ⊗ₘ (f ⊗ₘ g)) ≫ (w ⊗ₘ v') ≫ δ' :=
      congrArg (fun z => (𝟙 H ⊗ₘ (f ⊗ₘ g)) ≫ z) ht'
    _ = (w ⊗ₘ ((f ⊗ₘ g) ≫ v')) ≫ δ' := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ δ') hleft
    _ = (w ⊗ₘ (v ≫ (g ⊗ₘ f))) ≫ δ' := congrArg (fun z => (w ⊗ₘ z) ≫ δ') hv
    _ = (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ (g ⊗ₘ f)) ≫ δ' := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ δ') hright.symm
    _ = (w ⊗ₘ v) ≫ δ ≫ n := congrArg (fun z => (w ⊗ₘ v) ≫ z) hn.symm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ n) ht.symm

/-- The original braiding isomorphisms are natural for the unchanged genuine Day tensor maps. -/
theorem naturality {F F' G G' : EnrichedFunctorCat V I} (f : F ⟶ F') (g : G ⟶ G') :
    (Input.bifunctor d.tensorEnrichedFunctor).map (X := (F, G)) (Y := (F', G')) (f, g) ≫
        (BraidingFunctor.functorIso d b F'.toEnrichedFunctor G'.toEnrichedFunctor).hom =
      (BraidingFunctor.functorIso d b F.toEnrichedFunctor G.toEnrichedFunctor).hom ≫
        (Input.bifunctor d.tensorEnrichedFunctor).map (X := (G, F)) (Y := (G', F')) (g, f) := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
    BraidingFunctor.functorIso_hom_component, BraidingFunctor.functorIso_hom_component]
  have hl : EnrichedFunctorCat.component
      ((Input.bifunctor d.tensorEnrichedFunctor).map (X := (F, G)) (Y := (F', G')) (f, g)) k =
      Input.mapAt d.tensorEnrichedFunctor f g k :=
    Input.natTrans_component d.tensorEnrichedFunctor f g k
  have hr : EnrichedFunctorCat.component
      ((Input.bifunctor d.tensorEnrichedFunctor).map (X := (G, F)) (Y := (G', F')) (g, f)) k =
      Input.mapAt d.tensorEnrichedFunctor g f k :=
    Input.natTrans_component d.tensorEnrichedFunctor g f k
  rw [hl, hr]
  exact component_natural d b f g k

end CategoryTheory.EnrichedDayKernel.BraidingTensor
