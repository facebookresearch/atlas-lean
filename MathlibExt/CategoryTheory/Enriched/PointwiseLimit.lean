/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseLimitAction
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace CategoryTheory.EnrichedFunctorCat.PointwiseLimit
open Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)

/-- The full target-limit action preserves the original enriched identity. -/
theorem action_id (a : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)] :
    (limit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eId V a) ≫ action K a a =
      (ρ_ (limit (K ⋙ EnrichedFunctorCat.evaluation a))).hom := by
  apply limit.hom_ext
  intro j
  let L := limit (K ⋙ EnrichedFunctorCat.evaluation a)
  let X := (K.obj j).toEnrichedFunctor.obj a
  let p : L ⟶ X := limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j
  let H := a ⟶[V] a
  let ac : L ⊗ H ⟶ L := action K a a
  let act : X ⊗ H ⟶ X := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a a)
  have hp : ac ≫ p = (p ▷ H) ≫ act := action_projection K a a j
  have hi := congrArg MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map_id a)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at hi
  have hUnit : (X ◁ eId V a) ≫ act = (ρ_ X).hom := hi
  have hExchange : (L ◁ eId V a) ≫ (p ▷ H) =
      (p ▷ (𝟙_ V)) ≫ (X ◁ eId V a) := whisker_exchange p (eId V a)
  change ((L ◁ eId V a) ≫ ac) ≫ p = (ρ_ L).hom ≫ p
  calc
    _ = (L ◁ eId V a) ≫ (p ▷ H) ≫ act := by rw [Category.assoc, hp]
    _ = (p ▷ (𝟙_ V)) ≫ (X ◁ eId V a) ≫ act := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ act) hExchange
    _ = (p ▷ (𝟙_ V)) ≫ (ρ_ X).hom := by rw [hUnit]
    _ = _ := rightUnitor_naturality p

/-- The complete limit Hom action retains source-first enriched composition. -/
theorem action_comp (a b c : A)
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation c)] :
    (limit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eComp V a b c) ≫ action K a c =
      (α_ (limit (K ⋙ EnrichedFunctorCat.evaluation a)) (a ⟶[V] b) (b ⟶[V] c)).inv ≫
        (action K a b ▷ (b ⟶[V] c)) ≫ action K b c := by
  apply limit.hom_ext
  intro j
  let P := a ⟶[V] b
  let Q := b ⟶[V] c
  let H := a ⟶[V] c
  let L := limit (K ⋙ EnrichedFunctorCat.evaluation a)
  let M := limit (K ⋙ EnrichedFunctorCat.evaluation b)
  let N := limit (K ⋙ EnrichedFunctorCat.evaluation c)
  let X := (K.obj j).toEnrichedFunctor.obj a
  let Y := (K.obj j).toEnrichedFunctor.obj b
  let Z := (K.obj j).toEnrichedFunctor.obj c
  let pa : L ⟶ X := limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j
  let pb : M ⟶ Y := limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j
  let pc : N ⟶ Z := limit.π (K ⋙ EnrichedFunctorCat.evaluation c) j
  let ab : X ⊗ P ⟶ Y := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
  let bc : Y ⊗ Q ⟶ Z := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map b c)
  let ac : X ⊗ H ⟶ Z := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a c)
  let lab : L ⊗ P ⟶ M := action K a b
  let lbc : M ⊗ Q ⟶ N := action K b c
  let lac : L ⊗ H ⟶ N := action K a c
  have hAB : lab ≫ pb = (pa ▷ P) ≫ ab := action_projection K a b j
  have hBC : lbc ≫ pc = (pb ▷ Q) ≫ bc := action_projection K b c j
  have hAC : lac ≫ pc = (pa ▷ H) ≫ ac := action_projection K a c j
  have hc := congrArg MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map_comp a b c)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp] at hc
  have hOriginal : (X ◁ eComp V a b c) ≫ ac =
      (α_ X P Q).inv ≫ (ab ▷ Q) ≫ bc := hc
  have hExchange : (L ◁ eComp V a b c) ≫ (pa ▷ H) =
      (pa ▷ (P ⊗ Q)) ≫ (X ◁ eComp V a b c) := whisker_exchange pa (eComp V a b c)
  have hAssoc : (pa ▷ (P ⊗ Q)) ≫ (α_ X P Q).inv =
      (α_ L P Q).inv ≫ ((pa ▷ P) ▷ Q) := associator_inv_naturality_left pa P Q
  change ((L ◁ eComp V a b c) ≫ lac) ≫ pc =
    ((α_ L P Q).inv ≫ (lab ▷ Q) ≫ lbc) ≫ pc
  calc
    _ = (L ◁ eComp V a b c) ≫ (pa ▷ H) ≫ ac := by rw [Category.assoc, hAC]
    _ = (pa ▷ (P ⊗ Q)) ≫ (X ◁ eComp V a b c) ≫ ac := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ ac) hExchange
    _ = (pa ▷ (P ⊗ Q)) ≫ (α_ X P Q).inv ≫ (ab ▷ Q) ≫ bc := by rw [hOriginal]
    _ = (α_ L P Q).inv ≫ ((pa ▷ P) ▷ Q) ≫ (ab ▷ Q) ≫ bc := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ (ab ▷ Q) ≫ bc) hAssoc
    _ = (α_ L P Q).inv ≫ (lab ▷ Q) ≫ (pb ▷ Q) ≫ bc := by
      have ht : (lab ▷ Q) ≫ (pb ▷ Q) = ((pa ▷ P) ▷ Q) ≫ (ab ▷ Q) := by
        simpa only [comp_whiskerRight] using congrArg (fun q => q ▷ Q) hAB
      simpa only [Category.assoc] using congrArg (fun q => (α_ L P Q).inv ≫ q ≫ bc) ht.symm
    _ = _ := by
      rw [← hBC]
      simp only [Category.assoc]

variable [∀ a : A, HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]

/-- The genuine enriched functor on the original pointwise limit objects. -/
abbrev object : EnrichedFunctorCat V A where
  toEnrichedFunctor :=
    { obj := fun a => limit (K ⋙ EnrichedFunctorCat.evaluation a)
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

/-- The original pointwise projections as full-Hom natural transformations. -/
def projection (j : J) : object K ⟶ K.obj j :=
  GradedNatTrans.unitOfComponents
    (fun a => limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j)
    (fun a b => by
      let L := limit (K ⋙ EnrichedFunctorCat.evaluation a)
      let M := limit (K ⋙ EnrichedFunctorCat.evaluation b)
      let X := (K.obj j).toEnrichedFunctor.obj a
      let Y := (K.obj j).toEnrichedFunctor.obj b
      let pa : L ⟶ X := limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j
      let pb : M ⟶ Y := limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j
      let H := a ⟶[V] b
      let ac : L ⊗ H ⟶ M := action K a b
      let act : X ⊗ H ⟶ Y := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      have hp : ac ≫ pb = (pa ▷ H) ≫ act := action_projection K a b j
      have ht : pa ⊗ₘ 𝟙 H = pa ▷ H := tensorHom_id pa H
      change MonoidalClosed.uncurry (MonoidalClosed.curry ac) ≫ pb = (pa ⊗ₘ 𝟙 H) ≫ act
      rw [MonoidalClosed.uncurry_curry, ht]
      exact hp)

/-- Projection components are the original selected limit legs. -/
theorem projection_component (j : J) (a : A) :
    EnrichedFunctorCat.component (projection K j) a =
      limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The original pointwise projections form a genuine cone on K. -/
def cone : Cone K where
  pt := object K
  π :=
    { app := projection K
      naturality := by
        intro i j f
        apply EnrichedFunctorCat.hom_ext
        intro a
        have hp : limit.π (K ⋙ EnrichedFunctorCat.evaluation a) i ≫
            EnrichedFunctorCat.component (K.map f) a =
              limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j :=
          limit.w (K ⋙ EnrichedFunctorCat.evaluation a) f
        change EnrichedFunctorCat.component (𝟙 (object K) ≫ projection K j) a =
          EnrichedFunctorCat.component (projection K i ≫ K.map f) a
        simp only [EnrichedFunctorCat.component_comp, projection_component, Category.id_comp]
        exact hp.symm }

/-- Lift the original evaluated cones with their complete enriched Hom naturality. -/
def lift (q : Cone K) : q.pt ⟶ object K :=
  GradedNatTrans.unitOfComponents
    (fun a => limit.lift (K ⋙ EnrichedFunctorCat.evaluation a)
      ((EnrichedFunctorCat.evaluation a).mapCone q))
    (fun a b => by
      apply limit.hom_ext
      intro j
      let L := limit (K ⋙ EnrichedFunctorCat.evaluation a)
      let M := limit (K ⋙ EnrichedFunctorCat.evaluation b)
      let X := (K.obj j).toEnrichedFunctor.obj a
      let Y := (K.obj j).toEnrichedFunctor.obj b
      let H := a ⟶[V] b
      let pa : L ⟶ X := limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j
      let pb : M ⟶ Y := limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j
      let la : q.pt.toEnrichedFunctor.obj a ⟶ L :=
        limit.lift (K ⋙ EnrichedFunctorCat.evaluation a)
          ((EnrichedFunctorCat.evaluation a).mapCone q)
      let lb : q.pt.toEnrichedFunctor.obj b ⟶ M :=
        limit.lift (K ⋙ EnrichedFunctorCat.evaluation b)
          ((EnrichedFunctorCat.evaluation b).mapCone q)
      let qa : q.pt.toEnrichedFunctor.obj a ⟶ X := EnrichedFunctorCat.component (q.π.app j) a
      let qb : q.pt.toEnrichedFunctor.obj b ⟶ Y := EnrichedFunctorCat.component (q.π.app j) b
      let ac : L ⊗ H ⟶ M := action K a b
      let act : X ⊗ H ⟶ Y := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      let aq : q.pt.toEnrichedFunctor.obj a ⊗ H ⟶ q.pt.toEnrichedFunctor.obj b :=
        MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b)
      have hn : aq ≫ qb = (qa ⊗ₘ 𝟙 H) ≫ act := (q.π.app j).uncurriedNaturality a b
      have hA : la ≫ pa = qa := limit.lift_π ((EnrichedFunctorCat.evaluation a).mapCone q) j
      have hB : lb ≫ pb = qb := limit.lift_π ((EnrichedFunctorCat.evaluation b).mapCone q) j
      have hp : ac ≫ pb = (pa ▷ H) ≫ act := action_projection K a b j
      have ht : la ⊗ₘ 𝟙 H = la ▷ H := tensorHom_id la H
      change (aq ≫ lb) ≫ pb =
        ((la ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry ac)) ≫ pb
      rw [MonoidalClosed.uncurry_curry, ht]
      calc
        _ = aq ≫ qb := by rw [Category.assoc, hB]
        _ = (qa ▷ H) ≫ act := by simpa only [tensorHom_id] using hn
        _ = (la ▷ H) ≫ (pa ▷ H) ≫ act := by rw [← hA, comp_whiskerRight, Category.assoc]
        _ = _ := by rw [← hp, Category.assoc])

/-- Lift components are the actual chosen evaluated limit lifts. -/
theorem lift_component (q : Cone K) (a : A) :
    EnrichedFunctorCat.component (lift K q) a =
      limit.lift (K ⋙ EnrichedFunctorCat.evaluation a)
        ((EnrichedFunctorCat.evaluation a).mapCone q) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The genuine pointwise cone has the complete original limit universal property. -/
def isLimit : IsLimit (cone K) where
  lift := lift K
  fac q j := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    change EnrichedFunctorCat.component (lift K q ≫ projection K j) a =
      EnrichedFunctorCat.component (q.π.app j) a
    rw [EnrichedFunctorCat.component_comp, lift_component, projection_component]
    exact limit.lift_π ((EnrichedFunctorCat.evaluation a).mapCone q) j
  uniq q m hm := by
    let m' : q.pt ⟶ object K := m
    change m' = lift K q
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [lift_component]
    apply limit.hom_ext
    intro j
    have hOriginal : m' ≫ projection K j = q.π.app j := hm j
    have h := congrArg (fun z => EnrichedFunctorCat.component z a) hOriginal
    rw [EnrichedFunctorCat.component_comp, projection_component] at h
    exact h.trans (limit.lift_π ((EnrichedFunctorCat.evaluation a).mapCone q) j).symm

/-- Evaluating the genuine cone gives the original selected limit object and projections. -/
def evaluatedIsLimit (a : A) :
    IsLimit ((EnrichedFunctorCat.evaluation a).mapCone (cone K)) := by
  apply IsLimit.ofIsoLimit (limit.isLimit (K ⋙ EnrichedFunctorCat.evaluation a))
  exact Cone.ext (Iso.refl _) (fun j => by
    exact (projection_component K j a).symm.trans
      (Category.id_comp (EnrichedFunctorCat.component (projection K j) a)).symm)

/-- The original family of evaluated limits supplies the genuine diagram limit. -/
theorem hasLimit : HasLimit K := HasLimit.mk ⟨cone K, isLimit K⟩

/-- Evaluation preserves the actual genuine diagram limit. -/
theorem evaluation_preservesLimit (a : A) : PreservesLimit K (EnrichedFunctorCat.evaluation a) :=
  preservesLimit_of_preserves_limit_cone (isLimit K) (evaluatedIsLimit K a)

end CategoryTheory.EnrichedFunctorCat.PointwiseLimit
