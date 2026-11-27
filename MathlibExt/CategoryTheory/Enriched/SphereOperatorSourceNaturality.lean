/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorActionRecovery

/-!
# Original source-index and coefficient naturality

The source unit law and actual operator composition give naturality in the
entire coefficient object. The coefficient-index law is the original full
coend relation. These are the two input relations needed for the continuous
Day action; no action or Day coherence law is supplied as a hypothesis.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

omit [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)] in
/-- The source right unit law retains the actual complete decoded coefficient action. -/
theorem coefficient_right_unit_action (a : I) :
    (S.obj a ◁ L.epsilon) ≫ L.mu a (𝟙_ I) ≫
      ((ρ_ (S.obj (a ⊗ (𝟙_ I)))).inv ≫
        S.obj (a ⊗ (𝟙_ I)) ◁ eHomEquiv V (ρ_ a).hom ≫
        MonoidalClosed.uncurry (S.map (a ⊗ (𝟙_ I)) a)) = (ρ_ (S.obj a)).hom := by
  let s := (eHomEquiv V).symm
    (eHomEquiv V (ρ_ a).hom ≫ S.map (a ⊗ (𝟙_ I)) a)
  have hs : s = (ρ_ (S.obj (a ⊗ (𝟙_ I)))).inv ≫
      S.obj (a ⊗ (𝟙_ I)) ◁ eHomEquiv V (ρ_ a).hom ≫
      MonoidalClosed.uncurry (S.map (a ⊗ (𝟙_ I)) a) := by
    dsimp only [s]
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
    dsimp only [MonoidalClosed.uncurry']
    rw [MonoidalClosed.uncurry_natural_left]
  have h : (S.obj a ◁ L.epsilon) ≫ L.mu a (𝟙_ I) ≫ s = (ρ_ (S.obj a)).hom :=
    (L.unit a).2.symm
  exact (congrArg (fun z => (S.obj a ◁ L.epsilon) ≫ L.mu a (𝟙_ I) ≫ z) hs).symm.trans h

/-- Every original source index point is natural on the entire sphere coefficient. -/
theorem coefficientHom_precompose (n m k a : I)
    (f : n ⟶ m) (g : a ⊗ m ⟶ k) :
    (λ_ (S.obj a)).inv ≫
      ((eHomEquiv V f ≫ indexHom d S L n m) ⊗ₘ coefficientHom d S m k a g) ≫
      composition d S L n m k = coefficientHom d S n k a ((a ◁ f) ≫ g) := by
  let U := 𝟙_ I
  let A := S.obj a
  let B := S.obj U
  let C := S.obj (a ⊗ U)
  let f' := (λ_ n).hom ≫ f
  let pf := coefficientHom d S n m U f'
  let pg := coefficientHom d S m k a g
  let q := (β_ B A).hom ≫ L.mu a U
  let label := (α_ a U n).hom ≫ (a ◁ f') ≫ g
  let c := coefficientHom d S n k (a ⊗ U) label
  let z := coefficientHom d S n k a ((a ◁ f) ≫ g)
  let s : C ⟶ A :=
    (ρ_ C).inv ≫ C ◁ eHomEquiv V (ρ_ a).hom ≫
      MonoidalClosed.uncurry (S.map (a ⊗ U) a)
  have hPoint : eHomEquiv V f ≫ indexHom d S L n m = L.epsilon ≫ pf :=
    indexHom_point_eq_coefficient d S L n m f
  have hPair : (L.epsilon ≫ pf) ⊗ₘ pg =
      (L.epsilon ⊗ₘ 𝟙 A) ≫ (pf ⊗ₘ pg) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom L.epsilon (𝟙 A) pf pg).symm
  have hProduct : (pf ⊗ₘ pg) ≫ composition d S L n m k = q ≫ c :=
    coefficientHom_comp d S L n m k U a f' g
  have hPrefix : (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ q =
      (ρ_ A).inv ≫ (A ◁ L.epsilon) ≫ L.mu a U := by
    dsimp only [q]
    rw [tensorHom_id, BraidedCategory.braiding_naturality_left_assoc,
      braiding_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hTensorUnit : (α_ a U n).hom ≫ (a ◁ (λ_ n).hom) = (ρ_ a).hom ▷ n := by
    monoidal
  have hLabel : label = ((ρ_ a).hom ▷ n) ≫ ((a ◁ f) ≫ g) := by
    calc
      _ = (α_ a U n).hom ≫ (a ◁ (λ_ n).hom) ≫ (a ◁ f) ≫ g := by
        simp only [label, f', whiskerLeft_comp, Category.assoc]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ (a ◁ f) ≫ g) hTensorUnit
  have hRelation : c = s ≫ z :=
    (congrArg (coefficientHom d S n k (a ⊗ U)) hLabel).trans
      (coefficientHom_relation d S n k (a ⊗ U) a (ρ_ a).hom ((a ◁ f) ≫ g))
  have hUnit : (A ◁ L.epsilon) ≫ L.mu a U ≫ s = (ρ_ A).hom :=
    coefficient_right_unit_action d S L a
  calc
    _ = (λ_ A).inv ≫ ((L.epsilon ≫ pf) ⊗ₘ pg) ≫ composition d S L n m k :=
      congrArg (fun t => (λ_ A).inv ≫ (t ⊗ₘ pg) ≫ composition d S L n m k) hPoint
    _ = (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ (pf ⊗ₘ pg) ≫
        composition d S L n m k := by
      simpa only [Category.assoc] using congrArg
        (fun t => (λ_ A).inv ≫ t ≫ composition d S L n m k) hPair
    _ = (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ q ≫ c :=
      congrArg (fun t => (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ t) hProduct
    _ = (ρ_ A).inv ≫ (A ◁ L.epsilon) ≫ L.mu a U ≫ c := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ c) hPrefix
    _ = (ρ_ A).inv ≫ (A ◁ L.epsilon) ≫ L.mu a U ≫ (s ≫ z) :=
      congrArg (fun t => (ρ_ A).inv ≫ (A ◁ L.epsilon) ≫ L.mu a U ≫ t) hRelation
    _ = (ρ_ A).inv ≫ (ρ_ A).hom ≫ z := by
      simpa only [Category.assoc] using congrArg (fun t => (ρ_ A).inv ≫ t ≫ z) hUnit
    _ = _ := Iso.inv_hom_id_assoc _ z

/-- Every coefficient-index arrow retains the original full source coefficient action. -/
theorem coefficientAction_relation
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k a b : I)
    (u : a ⟶ b) (g : b ⊗ n ⟶ k) :
    coefficientAction d S L F n k a ((u ▷ n) ≫ g) =
      (F.toEnrichedFunctor.obj ⟨n⟩ ◁ S.toOrdinaryFunctor.map u) ≫
        coefficientAction d S L F n k b g := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let p := coefficientHom d S n k b g
  let z := MonoidalClosed.uncurry (F.toEnrichedFunctor.map (⟨n⟩ : OperatorIndex d S L) ⟨k⟩)
  let s := (ρ_ (S.obj a)).inv ≫ S.obj a ◁ eHomEquiv V u ≫
    MonoidalClosed.uncurry (S.map a b)
  have hSource : S.toOrdinaryFunctor.map u = s := by
    change (eHomEquiv V).symm (eHomEquiv V u ≫ S.map a b) = s
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
    dsimp only [MonoidalClosed.uncurry', s]
    rw [MonoidalClosed.uncurry_natural_left]
  have hRelation : coefficientHom d S n k a ((u ▷ n) ≫ g) =
      S.toOrdinaryFunctor.map u ≫ p :=
    (coefficientHom_relation d S n k a b u g).trans
      (congrArg (fun t => t ≫ p) hSource.symm)
  calc
    _ = (X ◁ (S.toOrdinaryFunctor.map u ≫ p)) ≫ z :=
      congrArg (fun t => (X ◁ t) ≫ z) hRelation
    _ = (X ◁ S.toOrdinaryFunctor.map u) ≫ (X ◁ p) ≫ z :=
      (congrArg (fun t => t ≫ z) (whiskerLeft_comp X (S.toOrdinaryFunctor.map u) p)).trans
        (Category.assoc _ _ _)
    _ = _ := by rfl

/-- The source index action commutes with the whole original coefficient action. -/
theorem coefficientAction_precompose
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n m k a : I)
    (f : n ⟶ m) (g : a ⊗ m ⟶ k) :
    (((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f ▷ S.obj a) ≫
        coefficientAction d S L F m k a g =
      coefficientAction d S L F n k a ((a ◁ f) ≫ g) := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let Y := F.toEnrichedFunctor.obj (⟨m⟩ : OperatorIndex d S L)
  let Z := F.toEnrichedFunctor.obj (⟨k⟩ : OperatorIndex d S L)
  let A := S.obj a
  let q := eHomEquiv V f ≫ indexHom d S L n m
  let p := coefficientHom d S m k a g
  let t := coefficientHom d S n k a ((a ◁ f) ≫ g)
  let h := F.toEnrichedFunctor.map (⟨n⟩ : OperatorIndex d S L) ⟨m⟩
  let j := F.toEnrichedFunctor.map (⟨m⟩ : OperatorIndex d S L) ⟨k⟩
  let c := F.toEnrichedFunctor.map (⟨n⟩ : OperatorIndex d S L) ⟨k⟩
  let r : X ⟶ Y :=
    ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f
  have hRestriction : ((indexRestriction d S L).obj F).toEnrichedFunctor.map n m =
      indexHom d S L n m ≫ h := rfl
  have hPoint : eHomEquiv V r = q ≫ h :=
    (EnrichedFunctor.toOrdinaryFunctor_map
      ((indexRestriction d S L).obj F).toEnrichedFunctor f).trans
      ((congrArg (fun z => eHomEquiv V f ≫ z) hRestriction).trans
        (Category.assoc (eHomEquiv V f) (indexHom d S L n m) h).symm)
  have hFull : composition d S L n m k ≫ c =
      (h ⊗ₘ j) ≫ eComp V X Y Z := by
    have hF := F.toEnrichedFunctor.map_comp
      (⟨n⟩ : OperatorIndex d S L) ⟨m⟩ ⟨k⟩
    rw [operatorIndex_comp] at hF
    exact hF
  have hPair : (q ⊗ₘ p) ≫ (h ⊗ₘ j) = (q ≫ h) ⊗ₘ (p ≫ j) :=
    tensorHom_comp_tensorHom q p h j
  have hUnit : (λ_ A).inv ≫ ((q ≫ h) ⊗ₘ (p ≫ j)) =
      (p ≫ j) ≫ (λ_ ((ihom Y).obj Z)).inv ≫ (q ≫ h) ▷ ((ihom Y).obj Z) :=
    leftUnitor_inv_comp_tensorHom (q ≫ h) (p ≫ j)
  have hMapped : t ≫ c = (p ≫ j) ≫ eHomWhiskerRight V r Z := by
    calc
      _ = ((λ_ A).inv ≫ (q ⊗ₘ p) ≫ composition d S L n m k) ≫ c :=
        congrArg (fun z => z ≫ c) (coefficientHom_precompose d S L n m k a f g).symm
      _ = (λ_ A).inv ≫ (q ⊗ₘ p) ≫ ((h ⊗ₘ j) ≫ eComp V X Y Z) := by
        simpa only [Category.assoc] using
          congrArg (fun z => (λ_ A).inv ≫ (q ⊗ₘ p) ≫ z) hFull
      _ = (λ_ A).inv ≫ ((q ≫ h) ⊗ₘ (p ≫ j)) ≫ eComp V X Y Z := by
        simpa only [Category.assoc] using
          congrArg (fun z => (λ_ A).inv ≫ z ≫ eComp V X Y Z) hPair
      _ = (p ≫ j) ≫ (λ_ ((ihom Y).obj Z)).inv ≫
          ((q ≫ h) ▷ ((ihom Y).obj Z)) ≫ eComp V X Y Z :=
        (Category.assoc (λ_ A).inv ((q ≫ h) ⊗ₘ (p ≫ j)) (eComp V X Y Z)).symm.trans
          ((congrArg (fun z => z ≫ eComp V X Y Z) hUnit).trans
            ((Category.assoc (p ≫ j)
              ((λ_ ((ihom Y).obj Z)).inv ≫ (q ≫ h) ▷ ((ihom Y).obj Z))
              (eComp V X Y Z)).trans
                (congrArg (fun z => (p ≫ j) ≫ z)
                  (Category.assoc (λ_ ((ihom Y).obj Z)).inv
                    ((q ≫ h) ▷ ((ihom Y).obj Z)) (eComp V X Y Z)))))
      _ = _ := by
        rw [← hPoint]
        rfl
  have hAction : coefficientAction d S L F m k a g = MonoidalClosed.uncurry (p ≫ j) :=
    (MonoidalClosed.uncurry_natural_left p j).symm
  calc
    _ = (r ▷ A) ≫ MonoidalClosed.uncurry (p ≫ j) := congrArg (fun z => (r ▷ A) ≫ z) hAction
    _ = MonoidalClosed.uncurry ((p ≫ j) ≫ eHomWhiskerRight V r Z) := by
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
        MonoidalClosed.uncurry_pre_app]
    _ = MonoidalClosed.uncurry (t ≫ c) := congrArg MonoidalClosed.uncurry hMapped.symm
    _ = _ := MonoidalClosed.uncurry_natural_left t c

/-- Both actual input arrows act on the complete original sphere coefficient. -/
theorem coefficientAction_twoInputs
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n m k a b : I)
    (f : n ⟶ m) (u : a ⟶ b) (g : b ⊗ m ⟶ k) :
    ((((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f) ⊗ₘ
        S.toOrdinaryFunctor.map u) ≫ coefficientAction d S L F m k b g =
      coefficientAction d S L F n k a ((u ⊗ₘ f) ≫ g) := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let r := ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f
  let s := S.toOrdinaryFunctor.map u
  have hF := coefficientAction_precompose d S L F n m k b f g
  have hU := coefficientAction_relation d S L F n k a b u ((b ◁ f) ≫ g)
  have hLabel : (u ▷ n) ≫ ((b ◁ f) ≫ g) = (u ⊗ₘ f) ≫ g :=
    (Category.assoc (u ▷ n) (b ◁ f) g).symm.trans
      (congrArg (fun z => z ≫ g) (tensorHom_def u f).symm)
  have hSplit : (r ⊗ₘ s) ≫ coefficientAction d S L F m k b g =
      (X ◁ s) ≫ ((r ▷ S.obj b) ≫ coefficientAction d S L F m k b g) :=
    (congrArg (fun z => z ≫ coefficientAction d S L F m k b g)
      (tensorHom_def' r s)).trans (Category.assoc _ _ _)
  have hMiddle : (X ◁ s) ≫ ((r ▷ S.obj b) ≫ coefficientAction d S L F m k b g) =
      (X ◁ s) ≫ coefficientAction d S L F n k b ((b ◁ f) ≫ g) :=
    congrArg (fun z => (X ◁ s) ≫ z) hF
  have hCombined : (r ⊗ₘ s) ≫ coefficientAction d S L F m k b g =
      coefficientAction d S L F n k a ((u ▷ n) ≫ ((b ◁ f) ≫ g)) :=
    hSplit.trans (hMiddle.trans hU.symm)
  exact hCombined.trans (congrArg (coefficientAction d S L F n k a) hLabel)

end CategoryTheory.Enriched.SphereOperator
