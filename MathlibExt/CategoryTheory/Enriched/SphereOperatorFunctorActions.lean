/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategory
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Full generator actions of actual operator functors

These are derived actions of the canonical enriched functor carrier. The
generator family retains the entire index Hom and sphere coefficient. Its
balance, unit and multiplication equations are consequences of the existing
functor and operator laws; reconstruction uses the original mapped coend.
The comparison with an ordinary Day-module presentation is subsequent work.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

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

/-- Restrict the full operator action to one entire coend generator. -/
def generatorAction (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a : I) :
    F.toEnrichedFunctor.obj ⟨n⟩ ⊗ weightedCoend.objects (weight d n k) S a ⟶
      F.toEnrichedFunctor.obj ⟨k⟩ :=
  (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩)).map
      (weightedCoend.ι (weight d n k) S a) ≫
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)

/-- Every full enriched index relation is retained by the derived action. -/
theorem generatorAction_balanced
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    weightedCoend.Mapped.Balanced (weight d n k) S
      (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
      (generatorAction d S L F n k) := by
  exact ((weightedCoend.Mapped.homEquiv (weight d n k) S
    (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
    (F.toEnrichedFunctor.obj ⟨k⟩))
      (MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩))).property

/-- The actual epsilon and left-unitor point recover the functor identity. -/
theorem generatorAction_unit
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n : I) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁
      ((λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon))) ≫
        generatorAction d S L F n n (𝟙_ I) =
      (ρ_ (F.toEnrichedFunctor.obj ⟨n⟩)).hom := by
  have h := congrArg
    (fun q : (𝟙_ V) ⟶
        (ihom (F.toEnrichedFunctor.obj ⟨n⟩)).obj
          (F.toEnrichedFunctor.obj ⟨n⟩) =>
      MonoidalClosed.uncurry q)
    (F.toEnrichedFunctor.map_id (⟨n⟩ : OperatorIndex d S L))
  rw [operatorIndex_id, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
    MonoidalClosed.uncurry_curry] at h
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let P := weightedCoend.objects (weight d n n) S (𝟙_ I)
  let i : P ⟶ Hom d S n n := weightedCoend.ι (weight d n n) S (𝟙_ I)
  let e : (𝟙_ V) ⟶ P :=
    (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon)
  let f : X ⊗ Hom d S n n ⟶ X :=
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨n⟩)
  have hGenerator : identityGenerator d S L n = e ≫ i :=
    (Category.assoc (λ_ (𝟙_ V)).inv
      (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon) i).symm
  change (X ◁ identityGenerator d S L n) ≫ f = (ρ_ X).hom at h
  rw [hGenerator] at h
  change (X ◁ e) ≫ ((tensorLeft X).map i ≫ f) = (ρ_ X).hom
  have hi : (tensorLeft X).map i = X ◁ i := rfl
  rw [hi]
  exact ((congrArg (fun q : X ⊗ (𝟙_ V) ⟶ X ⊗ Hom d S n n => q ≫ f)
    (MonoidalCategory.whiskerLeft_comp X e i)).trans
      (Category.assoc (X ◁ e) (X ◁ i) f)).symm.trans h

/-- Both original generator factors act by the derived binary composition. -/
theorem generatorAction_comp
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k l a b : I) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁ compositionGenerator d S L n k l a b) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩) =
      (α_ (F.toEnrichedFunctor.obj ⟨n⟩)
        (weightedCoend.objects (weight d n k) S a)
        (weightedCoend.objects (weight d k l) S b)).inv ≫
        (generatorAction d S L F n k a ▷
          weightedCoend.objects (weight d k l) S b) ≫
        generatorAction d S L F k l b := by
  let X : V := F.toEnrichedFunctor.obj ⟨n⟩
  let Y : V := F.toEnrichedFunctor.obj ⟨k⟩
  let Z : V := F.toEnrichedFunctor.obj ⟨l⟩
  let P : V := weightedCoend.objects (weight d n k) S a
  let Q : V := weightedCoend.objects (weight d k l) S b
  let H : V := Hom d S n k
  let K : V := Hom d S k l
  let T : V := Hom d S n l
  let p : P ⟶ H := weightedCoend.ι (weight d n k) S a
  let q : Q ⟶ K := weightedCoend.ι (weight d k l) S b
  let f : X ⊗ H ⟶ Y :=
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  let g : Y ⊗ K ⟶ Z :=
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨k⟩ ⟨l⟩)
  let h : X ⊗ T ⟶ Z :=
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩)
  have hFull :
      X ◁ composition d S L n k l ≫ h =
        (α_ X H K).inv ≫ (f ▷ K) ≫ g := by
    have ht := congrArg
      (fun z : H ⊗ K ⟶ (ihom X).obj Z => MonoidalClosed.uncurry z)
      (F.toEnrichedFunctor.map_comp (⟨n⟩ : OperatorIndex d S L)
        ⟨k⟩ ⟨l⟩)
    rw [operatorIndex_comp, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_eComp] at ht
    exact ht
  have hGenerator : (p ⊗ₘ q) ≫ composition d S L n k l =
      compositionGenerator d S L n k l a b :=
    composition_generator d S L n k l a b
  have hPre := congrArg
    (fun z : X ⊗ (H ⊗ K) ⟶ Z => (X ◁ (p ⊗ₘ q)) ≫ z) hFull
  have hAssoc :
      (X ◁ (p ⊗ₘ q)) ≫ (α_ X H K).inv =
        (α_ X P Q).inv ≫ ((X ◁ p) ⊗ₘ q) := by
    simpa only [MonoidalCategory.id_tensorHom] using
      (MonoidalCategory.associator_inv_naturality (𝟙 X) p q)
  have hSplit :
      ((X ◁ p) ⊗ₘ q) ≫ (f ▷ K) =
        ((X ◁ p ≫ f) ▷ Q) ≫ (Y ◁ q) := by
    have hTensor :
        ((X ◁ p) ⊗ₘ q) ≫ (f ⊗ₘ 𝟙 K) = (X ◁ p ≫ f) ⊗ₘ q :=
      (MonoidalCategory.tensorHom_comp_tensorHom
        (X ◁ p) q f (𝟙 K)).trans
          (congrArg (fun z : Q ⟶ K => (X ◁ p ≫ f) ⊗ₘ z)
            (Category.comp_id q))
    have hLeft : ((X ◁ p) ⊗ₘ q) ≫ (f ▷ K) =
        ((X ◁ p) ⊗ₘ q) ≫ (f ⊗ₘ 𝟙 K) :=
      congrArg (fun z : (X ⊗ H) ⊗ K ⟶ Y ⊗ K => ((X ◁ p) ⊗ₘ q) ≫ z)
        (MonoidalCategory.tensorHom_id f K).symm
    exact hLeft.trans
      (hTensor.trans (MonoidalCategory.tensorHom_def (X ◁ p ≫ f) q))
  calc
    _ = (X ◁ ((p ⊗ₘ q) ≫ composition d S L n k l)) ≫ h :=
      congrArg (fun z : P ⊗ Q ⟶ T => X ◁ z ≫ h) hGenerator.symm
    _ = (X ◁ (p ⊗ₘ q)) ≫ (X ◁ composition d S L n k l) ≫ h := by
      rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = (X ◁ (p ⊗ₘ q)) ≫ (α_ X H K).inv ≫ (f ▷ K) ≫ g := by
      simpa only [Category.assoc] using hPre
    _ = (α_ X P Q).inv ≫ ((X ◁ p) ⊗ₘ q) ≫ (f ▷ K) ≫ g := by
      simpa only [Category.assoc] using congrArg
        (fun z : X ⊗ (P ⊗ Q) ⟶ (X ⊗ H) ⊗ K => z ≫ (f ▷ K) ≫ g)
        hAssoc
    _ = (α_ X P Q).inv ≫ ((X ◁ p ≫ f) ▷ Q) ≫ (Y ◁ q) ≫ g := by
      simpa only [Category.assoc] using congrArg
        (fun z : (X ⊗ P) ⊗ Q ⟶ Y ⊗ K => (α_ X P Q).inv ≫ z ≫ g)
        hSplit
    _ = _ := by
      have hf : generatorAction d S L F n k a = X ◁ p ≫ f := rfl
      have hg : generatorAction d S L F k l b = Y ◁ q ≫ g := rfl
      change (α_ X P Q).inv ≫ ((X ◁ p ≫ f) ▷ Q) ≫ (Y ◁ q) ≫ g =
        (α_ X P Q).inv ≫ (generatorAction d S L F n k a ▷ Q) ≫
          generatorAction d S L F k l b
      rw [hf, hg]

/-- The entire enriched Hom map is reconstructed from the generator actions. -/
theorem generatorAction_reconstruct
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    MonoidalClosed.curry
      (weightedCoend.Mapped.desc (weight d n k) S
        (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
        (generatorAction d S L F n k)
        (generatorAction_balanced d S L F n k)) =
      F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩ := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  apply weightedCoend.Mapped.hom_ext (weight d n k) S
    (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
  intro a
  exact weightedCoend.Mapped.gen_desc (weight d n k) S
    (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
    (generatorAction d S L F n k)
    (generatorAction_balanced d S L F n k) a

end CategoryTheory.Enriched.SphereOperator
