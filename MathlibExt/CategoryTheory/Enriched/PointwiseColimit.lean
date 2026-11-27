/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseColimitAction
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

/-!
# Particular pointwise colimits of genuine enriched functors

The objects and injections are the original evaluated colimits. Full Hom
naturality, enriched identities and composition are retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace CategoryTheory.EnrichedFunctorCat.PointwiseColimit
open Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)

/-- The selected pointwise colimit action preserves the full enriched identity. -/
theorem action_id (a : A) [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)] :
    (colimit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eId V a) ≫ action K a a =
      (ρ_ (colimit (K ⋙ EnrichedFunctorCat.evaluation a))).hom := by
  apply (isColimitOfPreserves (tensorRight (𝟙_ V))
    (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))).hom_ext
  intro j
  let X := (K.obj j).toEnrichedFunctor.obj a
  let L := colimit (K ⋙ EnrichedFunctorCat.evaluation a)
  let i : X ⟶ L := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j
  have hId := congrArg MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map_id a)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at hId
  have hExchange : (i ▷ (𝟙_ V)) ≫ (L ◁ eId V a) =
      (X ◁ eId V a) ≫ (i ▷ (a ⟶[V] a)) :=
    (whisker_exchange i (eId V a)).symm
  let H := a ⟶[V] a
  let act : X ⊗ H ⟶ X := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a a)
  let ac : L ⊗ H ⟶ L := action K a a
  have hInject : (i ▷ H) ≫ ac = act ≫ i := injection_action K a a j
  have hUnit : (X ◁ eId V a) ≫ act = (ρ_ X).hom := hId
  change (i ▷ (𝟙_ V)) ≫ ((L ◁ eId V a) ≫ ac) = (i ▷ (𝟙_ V)) ≫ (ρ_ L).hom
  calc
    _ = (X ◁ eId V a) ≫ (i ▷ H) ≫ ac := by
      simpa only [H, Category.assoc] using congrArg (fun q => q ≫ ac) hExchange
    _ = (X ◁ eId V a) ≫ act ≫ i := by rw [hInject]
    _ = (ρ_ X).hom ≫ i := by rw [← Category.assoc, hUnit]
    _ = _ := (rightUnitor_naturality i).symm

/-- The full colimit Hom action retains the original source-first enriched composition. -/
theorem action_comp (a b c : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation c)] :
    (colimit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eComp V a b c) ≫ action K a c =
      (α_ (colimit (K ⋙ EnrichedFunctorCat.evaluation a)) (a ⟶[V] b) (b ⟶[V] c)).inv ≫
        (action K a b ▷ (b ⟶[V] c)) ≫ action K b c := by
  let P := a ⟶[V] b
  let Q := b ⟶[V] c
  let H := a ⟶[V] c
  let L := colimit (K ⋙ EnrichedFunctorCat.evaluation a)
  let mapped := isColimitOfPreserves (tensorRight (P ⊗ Q))
    (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))
  apply mapped.hom_ext
  intro j
  let X := (K.obj j).toEnrichedFunctor.obj a
  let i : X ⟶ L := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j
  have hComp := congrArg MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map_comp a b c)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp] at hComp
  have hLeft : (i ▷ (P ⊗ Q)) ≫ (L ◁ eComp V a b c) =
      (X ◁ eComp V a b c) ≫ (i ▷ H) :=
    (whisker_exchange i (eComp V a b c)).symm
  let Y := (K.obj j).toEnrichedFunctor.obj b
  let Z := (K.obj j).toEnrichedFunctor.obj c
  let M := colimit (K ⋙ EnrichedFunctorCat.evaluation b)
  let N := colimit (K ⋙ EnrichedFunctorCat.evaluation c)
  let ib : Y ⟶ M := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j
  let ic : Z ⟶ N := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation c) j
  let ab : X ⊗ P ⟶ Y := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
  let bc : Y ⊗ Q ⟶ Z := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map b c)
  let ac : X ⊗ H ⟶ Z := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a c)
  let lab : L ⊗ P ⟶ M := action K a b
  let lbc : M ⊗ Q ⟶ N := action K b c
  let lac : L ⊗ H ⟶ N := action K a c
  have hAB : (i ▷ P) ≫ lab = ab ≫ ib := injection_action K a b j
  have hBC : (ib ▷ Q) ≫ lbc = bc ≫ ic := injection_action K b c j
  have hAC : (i ▷ H) ≫ lac = ac ≫ ic := injection_action K a c j
  have hOriginal : (X ◁ eComp V a b c) ≫ ac =
      (α_ X P Q).inv ≫ (ab ▷ Q) ≫ bc := hComp
  change (i ▷ (P ⊗ Q)) ≫ ((L ◁ eComp V a b c) ≫ lac) =
    (i ▷ (P ⊗ Q)) ≫ (α_ L P Q).inv ≫ (lab ▷ Q) ≫ lbc
  calc
    _ = (X ◁ eComp V a b c) ≫ (i ▷ H) ≫ lac := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ lac) hLeft
    _ = (X ◁ eComp V a b c) ≫ ac ≫ ic := by rw [hAC]
    _ = (α_ X P Q).inv ≫ (ab ▷ Q) ≫ bc ≫ ic := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ ic) hOriginal
    _ = _ := by
      symm
      have hAssoc : (i ▷ (P ⊗ Q)) ≫ (α_ L P Q).inv =
          (α_ X P Q).inv ≫ ((i ▷ P) ▷ Q) :=
        associator_inv_naturality_left i P Q
      have hABTensor : ((i ▷ P) ▷ Q) ≫ (lab ▷ Q) = (ab ▷ Q) ≫ (ib ▷ Q) := by
        simpa only [comp_whiskerRight] using congrArg (fun q => q ▷ Q) hAB
      calc
        _ = (α_ X P Q).inv ≫ ((i ▷ P) ▷ Q) ≫ (lab ▷ Q) ≫ lbc := by
          simpa only [Category.assoc] using congrArg (fun q => q ≫ (lab ▷ Q) ≫ lbc) hAssoc
        _ = (α_ X P Q).inv ≫ (ab ▷ Q) ≫ (ib ▷ Q) ≫ lbc := by
          rw [← Category.assoc ((i ▷ P) ▷ Q) (lab ▷ Q) lbc, hABTensor]
          simp only [Category.assoc]
        _ = _ := by rw [hBC]

variable [∀ a : A, HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]

/-- The genuine enriched functor on the original pointwise colimit objects. -/
abbrev object : EnrichedFunctorCat V A where
  toEnrichedFunctor :=
    { obj := fun a => colimit (K ⋙ EnrichedFunctorCat.evaluation a)
      map := fun a b => MonoidalClosed.curry (action K a b)
      map_id := fun a => by
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
          MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
          MonoidalClosed.uncurry_curry]
        exact action_id K a
      map_comp := fun a b c => by
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
          MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_curry,
          MonoidalClosed.uncurry_curry]
        exact action_comp K a b c }

/-- The original colimit injections as genuine full-Hom natural transformations. -/
def injection (j : J) : K.obj j ⟶ object K :=
  GradedNatTrans.unitOfComponents
    (fun a => colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j)
    (fun a b => by
      let X := (K.obj j).toEnrichedFunctor.obj a
      let Y := (K.obj j).toEnrichedFunctor.obj b
      let L := colimit (K ⋙ EnrichedFunctorCat.evaluation a)
      let M := colimit (K ⋙ EnrichedFunctorCat.evaluation b)
      let ia : X ⟶ L := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j
      let ib : Y ⟶ M := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j
      let H := a ⟶[V] b
      let act : X ⊗ H ⟶ Y := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      let ac : L ⊗ H ⟶ M := action K a b
      have h : (ia ▷ H) ≫ ac = act ≫ ib := injection_action K a b j
      have hc : MonoidalClosed.uncurry (MonoidalClosed.curry ac) = ac :=
        MonoidalClosed.uncurry_curry ac
      have ht : ia ⊗ₘ 𝟙 H = ia ▷ H := tensorHom_id ia H
      change act ≫ ib = (ia ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry ac)
      exact h.symm.trans (by rw [ht, hc]))

/-- Each ordinary injection component is the selected evaluated colimit leg. -/
theorem injection_component (j : J) (a : A) :
    EnrichedFunctorCat.component (injection K j) a =
      colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The original pointwise injections form a cocone on the genuine diagram. -/
def cocone : Cocone K where
  pt := object K
  ι :=
    { app := injection K
      naturality := by
        intro i j f
        apply EnrichedFunctorCat.hom_ext
        intro a
        have h : EnrichedFunctorCat.component (K.map f) a ≫
            colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j =
              colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) i :=
          colimit.w (K ⋙ EnrichedFunctorCat.evaluation a) f
        change EnrichedFunctorCat.component ((K.map f) ≫ injection K j) a =
          EnrichedFunctorCat.component (injection K i ≫ 𝟙 (object K)) a
        simp only [EnrichedFunctorCat.component_comp, injection_component, Category.comp_id]
        exact h }

/-- Descend each original evaluated cocone while retaining full Hom naturality. -/
def desc (q : Cocone K) : object K ⟶ q.pt :=
  GradedNatTrans.unitOfComponents
    (fun a => colimit.desc (K ⋙ EnrichedFunctorCat.evaluation a)
      ((EnrichedFunctorCat.evaluation a).mapCocone q))
    (fun a b => by
      apply (isColimitOfPreserves (tensorRight (a ⟶[V] b))
        (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))).hom_ext
      intro j
      let X := (K.obj j).toEnrichedFunctor.obj a
      let Y := (K.obj j).toEnrichedFunctor.obj b
      let L := colimit (K ⋙ EnrichedFunctorCat.evaluation a)
      let M := colimit (K ⋙ EnrichedFunctorCat.evaluation b)
      let H := a ⟶[V] b
      let ia : X ⟶ L := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j
      let ib : Y ⟶ M := colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j
      let da : L ⟶ q.pt.toEnrichedFunctor.obj a :=
        colimit.desc (K ⋙ EnrichedFunctorCat.evaluation a)
            ((EnrichedFunctorCat.evaluation a).mapCocone q)
      let db : M ⟶ q.pt.toEnrichedFunctor.obj b :=
        colimit.desc (K ⋙ EnrichedFunctorCat.evaluation b)
            ((EnrichedFunctorCat.evaluation b).mapCocone q)
      let qa : X ⟶ q.pt.toEnrichedFunctor.obj a := EnrichedFunctorCat.component (q.ι.app j) a
      let qb : Y ⟶ q.pt.toEnrichedFunctor.obj b := EnrichedFunctorCat.component (q.ι.app j) b
      let act : X ⊗ H ⟶ Y := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      let ac : L ⊗ H ⟶ M := action K a b
      let aq : q.pt.toEnrichedFunctor.obj a ⊗ H ⟶ q.pt.toEnrichedFunctor.obj b :=
        MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b)
      have hn : act ≫ qb = (qa ⊗ₘ 𝟙 H) ≫ aq := (q.ι.app j).uncurriedNaturality a b
      have hInject : (ia ▷ H) ≫ ac = act ≫ ib := injection_action K a b j
      have hA : ia ≫ da = qa := colimit.ι_desc ((EnrichedFunctorCat.evaluation a).mapCocone q) j
      have hB : ib ≫ db = qb := colimit.ι_desc ((EnrichedFunctorCat.evaluation b).mapCocone q) j
      have hc : MonoidalClosed.uncurry (MonoidalClosed.curry ac) = ac :=
        MonoidalClosed.uncurry_curry ac
      have ht : da ⊗ₘ 𝟙 H = da ▷ H := tensorHom_id da H
      change (ia ▷ H) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry ac) ≫ db =
        (ia ▷ H) ≫ (da ⊗ₘ 𝟙 H) ≫ aq
      rw [hc, ht]
      calc
        _ = act ≫ ib ≫ db := by rw [← Category.assoc, hInject, Category.assoc]
        _ = act ≫ qb := by rw [hB]
        _ = (qa ▷ H) ≫ aq := by simpa only [tensorHom_id] using hn
        _ = _ := by rw [← hA, comp_whiskerRight, Category.assoc])

/-- The genuine descender's components are the actual evaluated colimit descents. -/
theorem desc_component (q : Cocone K) (a : A) :
    EnrichedFunctorCat.component (desc K q) a =
      colimit.desc (K ⋙ EnrichedFunctorCat.evaluation a)
        ((EnrichedFunctorCat.evaluation a).mapCocone q) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The genuine pointwise cocone is a colimit cocone on the original enriched-functor diagram. -/
def isColimit : IsColimit (cocone K) where
  desc := desc K
  fac q j := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    change EnrichedFunctorCat.component (injection K j ≫ desc K q) a =
      EnrichedFunctorCat.component (q.ι.app j) a
    rw [EnrichedFunctorCat.component_comp, injection_component, desc_component]
    exact colimit.ι_desc ((EnrichedFunctorCat.evaluation a).mapCocone q) j
  uniq q m hm := by
    let m' : object K ⟶ q.pt := m
    change m' = desc K q
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [desc_component]
    apply colimit.hom_ext
    intro j
    have hOriginal : injection K j ≫ m' = q.ι.app j := hm j
    have h : EnrichedFunctorCat.component (injection K j ≫ m') a =
        EnrichedFunctorCat.component (q.ι.app j) a :=
      congrArg (fun z => EnrichedFunctorCat.component z a) hOriginal
    rw [EnrichedFunctorCat.component_comp, injection_component] at h
    exact h.trans (colimit.ι_desc ((EnrichedFunctorCat.evaluation a).mapCocone q) j).symm

/-- Evaluating the chosen genuine cocone gives the original selected colimit object and legs. -/
def evaluatedIsColimit (a : A) :
    IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone (cocone K)) := by
  apply IsColimit.ofIsoColimit (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))
  exact Cocone.ext (Iso.refl _) (fun j => by
    change colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j ≫ 𝟙 _ =
      EnrichedFunctorCat.component (injection K j) a
    rw [injection_component, Category.comp_id])

/-- Particular evaluated colimits supply the genuine diagram's colimit. -/
theorem hasColimit : HasColimit K :=
  HasColimit.mk ⟨cocone K, isColimit K⟩

/-- Evaluation preserves the original genuine diagram's colimit. -/
theorem evaluation_preservesColimit (a : A) :
    PreservesColimit K (EnrichedFunctorCat.evaluation a) :=
  preservesColimit_of_preserves_colimit_cocone (isColimit K) (evaluatedIsColimit K a)

end CategoryTheory.EnrichedFunctorCat.PointwiseColimit
