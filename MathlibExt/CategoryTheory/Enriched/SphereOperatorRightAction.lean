/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorGeneratorNaturality
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexUnitFunctor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Kernel

/-!
# Original right sphere actions from full operator diagrams

The coefficient inclusions are the original weighted-coend generators. The
right external action uses the actual index block braiding. The family for
the original Day coend keeps its entire continuous index Hom object. These
are derived arrows of the existing genuine enriched-functor carrier; the
full Day descent and original module equivalence are separate obligations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits Opposite

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

/-- The actual coefficient inclusion at every original continuous index arrow. -/
def coefficientHom (n k a : I) (f : a ⊗ n ⟶ k) : S.obj a ⟶ Hom d S n k :=
  ((λ_ (S.obj a)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (S.obj a))) ≫
    weightedCoend.ι (weight d n k) S a

/-- A whole operator diagram acts through the original coefficient inclusion. -/
def coefficientAction (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a : I) (f : a ⊗ n ⟶ k) :
    F.toEnrichedFunctor.obj ⟨n⟩ ⊗ S.obj a ⟶ F.toEnrichedFunctor.obj ⟨k⟩ :=
  (F.toEnrichedFunctor.obj ⟨n⟩ ◁ coefficientHom d S n k a f) ≫
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)

/-- The coefficient action is exactly the complete original generator action. -/
theorem coefficientAction_eq_generator
    (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a : I) (f : a ⊗ n ⟶ k) :
    coefficientAction d S L F n k a f =
      (F.toEnrichedFunctor.obj ⟨n⟩ ◁
        ((λ_ (S.obj a)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (S.obj a)))) ≫
      generatorAction d S L F n k a := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let p : S.obj a ⟶ weightedCoend.objects (weight d n k) S a :=
    (λ_ (S.obj a)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (S.obj a))
  let i := weightedCoend.ι (weight d n k) S a
  let u := MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  have hg : generatorAction d S L F n k a = (X ◁ i) ≫ u := rfl
  calc
    _ = (X ◁ (p ≫ i)) ≫ u := rfl
    _ = ((X ◁ p) ≫ (X ◁ i)) ≫ u :=
      congrArg (fun z => z ≫ u) (whiskerLeft_comp X p i)
    _ = (X ◁ p) ≫ ((X ◁ i) ≫ u) := Category.assoc _ _ _
    _ = _ := congrArg (fun z => (X ◁ p) ≫ z) hg.symm

/-- Every actual genuine transformation preserves the complete coefficient action. -/
theorem coefficientAction_natural
    {F G : EnrichedFunctorCat V (OperatorIndex d S L)} (q : F ⟶ G)
    (n k a : I) (f : a ⊗ n ⟶ k) :
    coefficientAction d S L F n k a f ≫ EnrichedFunctorCat.component q ⟨k⟩ =
      (EnrichedFunctorCat.component q ⟨n⟩ ▷ S.obj a) ≫
        coefficientAction d S L G n k a f := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let Y := G.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let H := Hom d S n k
  let i := coefficientHom d S n k a f
  let u := MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  let v := MonoidalClosed.uncurry (G.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  let qN := EnrichedFunctorCat.component q (⟨n⟩ : OperatorIndex d S L)
  let qK := EnrichedFunctorCat.component q (⟨k⟩ : OperatorIndex d S L)
  have h : u ≫ qK = (qN ▷ H) ≫ v := by
    have ht := GradedNatTrans.uncurriedNaturality q (⟨n⟩ : OperatorIndex d S L) ⟨k⟩
    rw [tensorHom_id] at ht
    exact ht
  dsimp only [coefficientAction]
  calc
    _ = (X ◁ i) ≫ (u ≫ qK) := Category.assoc _ _ _
    _ = (X ◁ i) ≫ ((qN ▷ H) ≫ v) := congrArg (fun z => (X ◁ i) ≫ z) h
    _ = ((X ◁ i) ≫ (qN ▷ H)) ≫ v := (Category.assoc _ _ _).symm
    _ = ((qN ▷ S.obj a) ≫ (Y ◁ i)) ≫ v :=
      congrArg (fun z => z ≫ v) (whisker_exchange qN i)
    _ = _ := Category.assoc _ _ _

/-- Restriction uses the entire original unit-coefficient Hom map. -/
theorem restricted_index_action
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    MonoidalClosed.uncurry
        (((indexRestriction d S L).obj F).toEnrichedFunctor.map n k) =
      (F.toEnrichedFunctor.obj ⟨n⟩ ◁ indexHom d S L n k) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) := by
  exact MonoidalClosed.uncurry_natural_left (indexHom d S L n k)
    (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)

/-- The original coefficient unit and source unitor recover the whole functor identity. -/
theorem coefficientAction_unit
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n : I) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁ L.epsilon) ≫
        coefficientAction d S L F n n (𝟙_ I) (λ_ n).hom =
      (ρ_ (F.toEnrichedFunctor.obj ⟨n⟩)).hom := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let p : (𝟙_ V) ⟶ (((𝟙_ I) ⊗ n) ⟶[V] n) := eHomEquiv V (λ_ n).hom
  let i : S.obj (𝟙_ I) ⟶ (((𝟙_ I) ⊗ n) ⟶[V] n) ⊗ S.obj (𝟙_ I) :=
    (λ_ (S.obj (𝟙_ I))).inv ≫ (p ⊗ₘ 𝟙 (S.obj (𝟙_ I)))
  let e : (𝟙_ V) ⟶ (((𝟙_ I) ⊗ n) ⟶[V] n) ⊗ S.obj (𝟙_ I) :=
    (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon)
  let g := generatorAction d S L F n n (𝟙_ I)
  have hInsertion : L.epsilon ≫ i = e := by
    simpa only [i, e, tensorHom_id] using
      (leftUnitor_inv_comp_tensorHom p L.epsilon).symm
  have hAction : coefficientAction d S L F n n (𝟙_ I) (λ_ n).hom = (X ◁ i) ≫ g :=
    coefficientAction_eq_generator d S L F n n (𝟙_ I) (λ_ n).hom
  calc
    _ = (X ◁ L.epsilon) ≫ ((X ◁ i) ≫ g) :=
      congrArg (fun z => (X ◁ L.epsilon) ≫ z) hAction
    _ = ((X ◁ L.epsilon) ≫ (X ◁ i)) ≫ g := (Category.assoc _ _ _).symm
    _ = (X ◁ (L.epsilon ≫ i)) ≫ g :=
      congrArg (fun z => z ≫ g) (whiskerLeft_comp X L.epsilon i).symm
    _ = (X ◁ e) ≫ g := congrArg (fun z => (X ◁ z) ≫ g) hInsertion
    _ = _ := generatorAction_unit d S L F n

/-- Two entire original coefficient inclusions act through the actual binary composition. -/
theorem coefficientAction_comp
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k l a b : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁
      ((coefficientHom d S n k a f ⊗ₘ coefficientHom d S k l b g) ≫
        composition d S L n k l)) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩) =
    (α_ (F.toEnrichedFunctor.obj ⟨n⟩) (S.obj a) (S.obj b)).inv ≫
      (coefficientAction d S L F n k a f ▷ S.obj b) ≫
      coefficientAction d S L F k l b g := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let Y := F.toEnrichedFunctor.obj (⟨k⟩ : OperatorIndex d S L)
  let H := Hom d S n k
  let K := Hom d S k l
  let p := coefficientHom d S n k a f
  let q := coefficientHom d S k l b g
  let u := MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  let v := MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨k⟩ ⟨l⟩)
  have hFull :
      (X ◁ composition d S L n k l) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩) =
      (α_ X H K).inv ≫ (u ▷ K) ≫ v := by
    have h := congrArg MonoidalClosed.uncurry
      (F.toEnrichedFunctor.map_comp (⟨n⟩ : OperatorIndex d S L) ⟨k⟩ ⟨l⟩)
    rw [operatorIndex_comp, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_eComp] at h
    exact h
  have hAssoc :
      (X ◁ (p ⊗ₘ q)) ≫ (α_ X H K).inv =
        (α_ X (S.obj a) (S.obj b)).inv ≫ ((X ◁ p) ⊗ₘ q) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 X) p q
  have hSplit :
      ((X ◁ p) ⊗ₘ q) ≫ (u ▷ K) =
        ((X ◁ p ≫ u) ▷ S.obj b) ≫ (Y ◁ q) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, tensorHom_def]
  calc
    _ = (X ◁ (p ⊗ₘ q)) ≫ ((X ◁ composition d S L n k l) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩)) := by
      rw [whiskerLeft_comp, Category.assoc]
    _ = (X ◁ (p ⊗ₘ q)) ≫ ((α_ X H K).inv ≫ (u ▷ K) ≫ v) :=
      congrArg (fun z => (X ◁ (p ⊗ₘ q)) ≫ z) hFull
    _ = (α_ X (S.obj a) (S.obj b)).inv ≫ ((X ◁ p) ⊗ₘ q) ≫ (u ▷ K) ≫ v := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (u ▷ K) ≫ v) hAssoc
    _ = (α_ X (S.obj a) (S.obj b)).inv ≫
        ((X ◁ p ≫ u) ▷ S.obj b) ≫ (Y ◁ q) ≫ v := by
      simpa only [Category.assoc] using congrArg
        (fun z => (α_ X (S.obj a) (S.obj b)).inv ≫ z ≫ v) hSplit
    _ = _ := by
      dsimp only [coefficientAction]

section RightOrientation

variable [BraidedCategory I]

/-- The source right sphere inclusion uses the original index block braiding. -/
def rightSphereHom (n a : I) : S.obj a ⟶ Hom d S n (n ⊗ a) :=
  coefficientHom d S n (n ⊗ a) a (β_ a n).hom

/-- The original external right sphere action of a whole operator diagram. -/
def rightSphereAction (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n a : I) :
    F.toEnrichedFunctor.obj ⟨n⟩ ⊗ S.obj a ⟶ F.toEnrichedFunctor.obj ⟨n ⊗ a⟩ :=
  coefficientAction d S L F n (n ⊗ a) a (β_ a n).hom

/-- Every original transformation preserves the exact right sphere action. -/
theorem rightSphereAction_natural
    {F G : EnrichedFunctorCat V (OperatorIndex d S L)} (q : F ⟶ G) (n a : I) :
    rightSphereAction d S L F n a ≫ EnrichedFunctorCat.component q ⟨n ⊗ a⟩ =
      (EnrichedFunctorCat.component q ⟨n⟩ ▷ S.obj a) ≫
        rightSphereAction d S L G n a :=
  coefficientAction_natural d S L q n (n ⊗ a) a (β_ a n).hom

attribute [local instance] Enriched.prodCategory

/-- The full continuous family for the original right Day action, before descent. -/
def rightDayActionGenerator (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (k : I) (a : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor
      ((indexRestriction d S L).obj F).toEnrichedFunctor S k a ⟶
        F.toEnrichedFunctor.obj ⟨k⟩ :=
  ((α_ ((a.1 ⊗ a.2) ⟶[V] k) (F.toEnrichedFunctor.obj ⟨a.1⟩) (S.obj a.2)).inv ≫
    ((β_ ((a.1 ⊗ a.2) ⟶[V] k) (F.toEnrichedFunctor.obj ⟨a.1⟩)).hom ▷
      S.obj a.2) ≫
    (α_ (F.toEnrichedFunctor.obj ⟨a.1⟩) ((a.1 ⊗ a.2) ⟶[V] k) (S.obj a.2)).hom) ≫
    (F.toEnrichedFunctor.obj ⟨a.1⟩ ◁
      (eHomWhiskerRight V (β_ a.2 a.1).hom k ⊗ₘ 𝟙 (S.obj a.2))) ≫
    generatorAction d S L F a.1 k a.2

omit [MonoidalClosed V] in
private theorem rightDaySwap_natural {X Y : V} (q : X ⟶ Y) (H A : V) :
    ((α_ H X A).inv ≫ ((β_ H X).hom ▷ A) ≫ (α_ X H A).hom) ≫
      (q ▷ (H ⊗ A)) =
    (H ◁ (q ▷ A)) ≫
      ((α_ H Y A).inv ≫ ((β_ H Y).hom ▷ A) ≫ (α_ Y H A).hom) := by
  have hA :
      (H ◁ (q ▷ A)) ≫ (α_ H Y A).inv =
        (α_ H X A).inv ≫ ((H ◁ q) ▷ A) := by
    simpa only [id_tensorHom, tensorHom_id] using
      associator_inv_naturality (𝟙 H) q (𝟙 A)
  have hB :
      ((H ◁ q) ▷ A) ≫ ((β_ H Y).hom ▷ A) =
        ((β_ H X).hom ▷ A) ≫ ((q ▷ H) ▷ A) := by
    simpa only [id_tensorHom, tensorHom_id, comp_whiskerRight] using
      congrArg (fun z => z ▷ A) (BraidedCategory.braiding_naturality (𝟙 H) q)
  have hC :
      ((q ▷ H) ▷ A) ≫ (α_ Y H A).hom =
        (α_ X H A).hom ≫ (q ▷ (H ⊗ A)) :=
    associator_naturality_left q H A
  calc
    _ = (α_ H X A).inv ≫ ((β_ H X).hom ▷ A) ≫
        ((q ▷ H) ▷ A) ≫ (α_ Y H A).hom := by
      simpa only [Category.assoc] using congrArg
        (fun z => (α_ H X A).inv ≫ ((β_ H X).hom ▷ A) ≫ z) hC.symm
    _ = (α_ H X A).inv ≫ ((H ◁ q) ▷ A) ≫
        ((β_ H Y).hom ▷ A) ≫ (α_ Y H A).hom := by
      simpa only [Category.assoc] using congrArg
        (fun z => (α_ H X A).inv ≫ z ≫ (α_ Y H A).hom) hB.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ ((β_ H Y).hom ▷ A) ≫ (α_ Y H A).hom) hA.symm

/-- Every original transformation preserves the entire Day generator family. -/
theorem rightDayActionGenerator_natural
    {F G : EnrichedFunctorCat V (OperatorIndex d S L)} (q : F ⟶ G)
    (k : I) (a : I × I) :
    rightDayActionGenerator d S L F k a ≫ EnrichedFunctorCat.component q ⟨k⟩ =
      (𝟙 ((a.1 ⊗ a.2) ⟶[V] k) ⊗ₘ
        (EnrichedFunctorCat.component q ⟨a.1⟩ ⊗ₘ 𝟙 (S.obj a.2))) ≫
        rightDayActionGenerator d S L G k a := by
  let X := F.toEnrichedFunctor.obj (⟨a.1⟩ : OperatorIndex d S L)
  let Y := G.toEnrichedFunctor.obj (⟨a.1⟩ : OperatorIndex d S L)
  let H := (a.1 ⊗ a.2) ⟶[V] k
  let Q := (a.2 ⊗ a.1) ⟶[V] k
  let A := S.obj a.2
  let b : H ⊗ A ⟶ Q ⊗ A :=
    eHomWhiskerRight V (β_ a.2 a.1).hom k ⊗ₘ 𝟙 A
  let qN := EnrichedFunctorCat.component q (⟨a.1⟩ : OperatorIndex d S L)
  let qK := EnrichedFunctorCat.component q (⟨k⟩ : OperatorIndex d S L)
  let f := generatorAction d S L F a.1 k a.2
  let g := generatorAction d S L G a.1 k a.2
  let rx := (α_ H X A).inv ≫ ((β_ H X).hom ▷ A) ≫ (α_ X H A).hom
  let ry := (α_ H Y A).inv ≫ ((β_ H Y).hom ▷ A) ≫ (α_ Y H A).hom
  have hFull :
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨a.1⟩ ⟨k⟩) ≫ qK =
        (qN ▷ Hom d S a.1 k) ≫
          MonoidalClosed.uncurry (G.toEnrichedFunctor.map ⟨a.1⟩ ⟨k⟩) := by
    have ht := GradedNatTrans.uncurriedNaturality q
      (⟨a.1⟩ : OperatorIndex d S L) ⟨k⟩
    rw [tensorHom_id] at ht
    exact ht
  have hGen : f ≫ qK = (qN ▷ (Q ⊗ A)) ≫ g :=
    generatorNaturality_of_fullNaturality d S L F G a.1 k qN qK hFull a.2
  have hSwap : rx ≫ (qN ▷ (H ⊗ A)) = (H ◁ (qN ▷ A)) ≫ ry :=
    rightDaySwap_natural qN H A
  have hF : rightDayActionGenerator d S L F k a = rx ≫ (X ◁ b) ≫ f := by rfl
  have hG : rightDayActionGenerator d S L G k a = ry ≫ (Y ◁ b) ≫ g := by rfl
  have hInput :
      (𝟙 H ⊗ₘ (qN ⊗ₘ 𝟙 A)) = H ◁ (qN ▷ A) := by
    rw [tensorHom_id, id_tensorHom]
  calc
    _ = (rx ≫ (X ◁ b) ≫ f) ≫ qK := congrArg (fun z => z ≫ qK) hF
    _ = rx ≫ (X ◁ b) ≫ (f ≫ qK) :=
      (Category.assoc rx ((X ◁ b) ≫ f) qK).trans
        (congrArg (fun z => rx ≫ z) (Category.assoc (X ◁ b) f qK))
    _ = rx ≫ (X ◁ b) ≫ ((qN ▷ (Q ⊗ A)) ≫ g) :=
      congrArg (fun z => rx ≫ (X ◁ b) ≫ z) hGen
    _ = rx ≫ (qN ▷ (H ⊗ A)) ≫ (Y ◁ b) ≫ g :=
      congrArg (fun z => rx ≫ z)
        ((Category.assoc (X ◁ b) (qN ▷ (Q ⊗ A)) g).symm.trans
          ((congrArg (fun z => z ≫ g) (whisker_exchange qN b)).trans
            (Category.assoc (qN ▷ (H ⊗ A)) (Y ◁ b) g)))
    _ = (H ◁ (qN ▷ A)) ≫ ry ≫ (Y ◁ b) ≫ g := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (Y ◁ b) ≫ g) hSwap
    _ = (H ◁ (qN ▷ A)) ≫ rightDayActionGenerator d S L G k a := by
      simpa only [Category.assoc] using congrArg
        (fun z => (H ◁ (qN ▷ A)) ≫ z) hG.symm
    _ = _ := congrArg (fun z => z ≫ rightDayActionGenerator d S L G k a) hInput.symm

end RightOrientation

end CategoryTheory.Enriched.SphereOperator
