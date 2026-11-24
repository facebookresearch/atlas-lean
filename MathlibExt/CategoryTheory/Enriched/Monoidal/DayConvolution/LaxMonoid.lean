/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ColimitMonoidal
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.TransformationDescent
public import MathlibExt.CategoryTheory.Enriched.SphereMonoidalDayTransformations
public import MathlibExt.CategoryTheory.Enriched.Ordinary.MapHomWhisker
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Day monoids from the original enriched lax monoidal maps

The unit is extended through enriched Yoneda, and the tensorator is descended
through the full continuous Day coend. The internal laws are proved using the
constructed unitors and associator and the original external coherence laws.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LaxMonoid

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- Enriched Yoneda extends the original lax unit on the represented index unit. -/
abbrev unit : (⟨GradedYoneda.representable (V := V) (𝟙_ I)⟩ : EnrichedFunctorCat V I) ⟶ ⟨S⟩ :=
  Enriched.SphereOperator.sphereUnitTransformation d S L

/-- Evaluating the actual represented unit at the enriched identity recovers the original unit. -/
theorem unit_epsilon :
    eId V (𝟙_ I) ≫ EnrichedFunctorCat.component (unit d S L) (𝟙_ I) = L.epsilon :=
  Enriched.SphereOperator.sphereUnitTransformation_evaluate d S L

variable [HasColimitsOfSize.{uI, uI} V]

/-- The original enriched tensorator descends through the entire selected Day coend. -/
abbrev multiply :
    (⟨Output.functor d.tensorEnrichedFunctor S S⟩ : EnrichedFunctorCat V I) ⟶ ⟨S⟩ :=
  ActionFromTransformation.transformation d.tensorEnrichedFunctor S S S
    (Enriched.SphereOperator.tensoratorTransformation d S L)

/-- Every full Day generator is the original tensorator followed by the entire output action. -/
@[reassoc]
theorem gen_multiply (k : I) (a : I × I) :
    gen d.tensorEnrichedFunctor S S k a ≫ EnrichedFunctorCat.component (multiply d S L) k =
      (𝟙 ((a.1 ⊗ a.2) ⟶[V] k) ⊗ₘ L.mu a.1 a.2) ≫
        ActionFromTransformation.targetAction S (a.1 ⊗ a.2) k := by
  exact (ActionFromTransformation.gen_transformation d.tensorEnrichedFunctor S S S
    (Enriched.SphereOperator.tensoratorTransformation d S L) k a).trans
      (congrArg (fun z => (𝟙 ((a.1 ⊗ a.2) ⟶[V] k) ⊗ₘ z) ≫
        ActionFromTransformation.targetAction S (a.1 ⊗ a.2) k)
        (Enriched.SphereOperator.tensoratorTransformation_component d S L a))

omit [HasColimitsOfSize.{uI, uI} V] [MonoidalCategory I] in
/-- The entire output action evaluated at an original ordinary arrow is the original functor map. -/
theorem targetAction_point {x k : I} (f : x ⟶ k) :
    (λ_ (S.obj x)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (S.obj x)) ≫
        ActionFromTransformation.targetAction S x k = S.toOrdinaryFunctor.map f := by
  let g : S.obj x ⟶ S.obj k := S.toOrdinaryFunctor.map f
  have hp : (𝟙 (S.obj x) ⊗ₘ eHomEquiv V f) ≫ MonoidalClosed.uncurry (S.map x k) =
      (ρ_ (S.obj x)).hom ≫ g := S.uncurry_map_point f
  change (λ_ (S.obj x)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (S.obj x)) ≫
      ActionFromTransformation.targetAction S x k = g
  calc
    _ = (ρ_ (S.obj x)).inv ≫ (𝟙 (S.obj x) ⊗ₘ eHomEquiv V f) ≫
        MonoidalClosed.uncurry (S.map x k) := by
      dsimp only [ActionFromTransformation.targetAction]
      rw [BraidedCategory.braiding_naturality_assoc, braiding_tensorUnit_left]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (ρ_ (S.obj x)).inv ≫ (ρ_ (S.obj x)).hom ≫ g :=
      congrArg (fun z => (ρ_ (S.obj x)).inv ≫ z) hp
    _ = g := Iso.inv_hom_id_assoc (ρ_ (S.obj x)) g

/-- The original multiplication on a generator labelled by any original ordinary arrow. -/
@[reassoc]
theorem labelledGenerator_multiply (a : I × I) {k : I} (f : a.1 ⊗ a.2 ⟶ k) :
    (λ_ (S.obj a.1 ⊗ S.obj a.2)).inv ≫
        (eHomEquiv V f ⊗ₘ 𝟙 (S.obj a.1 ⊗ S.obj a.2)) ≫
        gen d.tensorEnrichedFunctor S S k a ≫ EnrichedFunctorCat.component (multiply d S L) k =
      L.mu a.1 a.2 ≫ S.toOrdinaryFunctor.map f := by
  let Q : V := S.obj a.1 ⊗ S.obj a.2
  let x : I := a.1 ⊗ a.2
  let H : V := x ⟶[V] k
  let p : 𝟙_ V ⟶ H := eHomEquiv V f
  let q : Q ⟶ S.obj x := L.mu a.1 a.2
  let γ : H ⊗ Q ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k :=
    gen d.tensorEnrichedFunctor S S k a
  let m : EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k ⟶ S.obj k :=
    EnrichedFunctorCat.component (multiply d S L) k
  let t : H ⊗ S.obj x ⟶ S.obj k := ActionFromTransformation.targetAction S x k
  let g : S.obj x ⟶ S.obj k := S.toOrdinaryFunctor.map f
  have hg : γ ≫ m = (𝟙 H ⊗ₘ q) ≫ t := gen_multiply d S L k a
  have ht : (p ⊗ₘ 𝟙 Q) ≫ (𝟙 H ⊗ₘ q) = p ⊗ₘ q := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have hu : (λ_ Q).inv ≫ (p ⊗ₘ q) = q ≫ (λ_ (S.obj x)).inv ≫ (p ⊗ₘ 𝟙 (S.obj x)) := by
    simpa only [tensorHom_id] using leftUnitor_inv_comp_tensorHom p q
  have hp : (λ_ (S.obj x)).inv ≫ (p ⊗ₘ 𝟙 (S.obj x)) ≫ t = g := targetAction_point S f
  change (λ_ Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ γ ≫ m = q ≫ g
  calc
    _ = (λ_ Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ (𝟙 H ⊗ₘ q) ≫ t :=
      congrArg (fun z => (λ_ Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ z) hg
    _ = (λ_ Q).inv ≫ (p ⊗ₘ q) ≫ t := by
      simpa only [Category.assoc] using congrArg (fun z => (λ_ Q).inv ≫ z ≫ t) ht
    _ = q ≫ (λ_ (S.obj x)).inv ≫ (p ⊗ₘ 𝟙 (S.obj x)) ≫ t := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ t) hu
    _ = q ≫ g := congrArg (fun z => q ≫ z) hp

/-- Multiplication recovers the exact tensorator on every actual identity generator. -/
@[reassoc]
theorem unitGenerator_multiply (a : I × I) :
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S S a ≫
        EnrichedFunctorCat.component (multiply d S L) (a.1 ⊗ a.2) = L.mu a.1 a.2 := by
  let x : I := a.1 ⊗ a.2
  let Q : V := S.obj a.1 ⊗ S.obj a.2
  let γ : (x ⟶[V] x) ⊗ Q ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S S x :=
    gen d.tensorEnrichedFunctor S S x a
  let m := EnrichedFunctorCat.component (multiply d S L) x
  have h := labelledGenerator_multiply d S L a (𝟙 x)
  have hi : (S.toOrdinaryFunctor.map (𝟙 x) : S.obj x ⟶ S.obj x) = 𝟙 (S.obj x) :=
    S.toOrdinaryFunctor.map_id x
  have hr : L.mu a.1 a.2 ≫ S.toOrdinaryFunctor.map (𝟙 x) = L.mu a.1 a.2 :=
    (congrArg (fun z => L.mu a.1 a.2 ≫ z) hi).trans (Category.comp_id (L.mu a.1 a.2))
  have he : eHomEquiv V (𝟙 x) = eId V x := eHomEquiv_id V x
  have hl : (λ_ Q).inv ≫ (eHomEquiv V (𝟙 x) ⊗ₘ 𝟙 Q) ≫ γ ≫ m = L.mu a.1 a.2 := h.trans hr
  have hp : (λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q) ≫ γ ≫ m = L.mu a.1 a.2 :=
    (congrArg (fun z => (λ_ Q).inv ≫ (z ⊗ₘ 𝟙 Q) ≫ γ ≫ m) he).symm.trans hl
  have hgen : AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S S a =
      (λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q) ≫ γ :=
    Category.assoc (λ_ Q).inv (eId V x ⊗ₘ 𝟙 Q) γ
  exact (congrArg (fun z => z ≫ m) hgen).trans
    (by simpa only [Category.assoc] using hp)

omit [HasColimitsOfSize.{uI, uI} V] [MonoidalCategory I] in
/-- An actual source isomorphism transports arbitrary coefficients and the whole output Hom. -/
theorem targetAction_sourceIso {x y : I} (e : x ≅ y) (k : I)
    {Q P : V} (c : Q ⟶ S.obj x) (h : P ⟶ (x ⟶[V] k)) :
    (h ⊗ₘ c) ≫ ActionFromTransformation.targetAction S x k =
      ((h ≫ eHomWhiskerRight V e.inv k) ⊗ₘ (c ≫ S.toOrdinaryFunctor.map e.hom)) ≫
        ActionFromTransformation.targetAction S y k := by
  let g : S.obj x ⟶ S.obj y := S.toOrdinaryFunctor.map e.hom
  let r : P ⟶ (y ⟶[V] k) := h ≫ eHomWhiskerRight V e.inv k
  have hs : (c ⊗ₘ h) ≫ MonoidalClosed.uncurry (S.map x k) =
      ((c ≫ g) ⊗ₘ r) ≫ MonoidalClosed.uncurry (S.map y k) :=
    S.uncurry_map_sourceIso e k c h
  change (h ⊗ₘ c) ≫ ActionFromTransformation.targetAction S x k =
    (r ⊗ₘ (c ≫ g)) ≫ ActionFromTransformation.targetAction S y k
  calc
    _ = (β_ P Q).hom ≫ (c ⊗ₘ h) ≫ MonoidalClosed.uncurry (S.map x k) := by
      dsimp only [ActionFromTransformation.targetAction]
      rw [BraidedCategory.braiding_naturality_assoc]
    _ = (β_ P Q).hom ≫ ((c ≫ g) ⊗ₘ r) ≫ MonoidalClosed.uncurry (S.map y k) :=
      congrArg (fun z => (β_ P Q).hom ≫ z) hs
    _ = _ := by
      dsimp only [ActionFromTransformation.targetAction]
      rw [BraidedCategory.braiding_naturality_assoc]

omit [SymmetricCategory V] [MonoidalClosed V] [HasColimitsOfSize.{uI, uI} V] in
private theorem insert_word {A Q R H : V} (p : 𝟙_ V ⟶ H) (g : A ⟶ Q) (e : Q ⟶ R) :
    (λ_ A).inv ≫ (p ⊗ₘ g) ≫ (𝟙 H ⊗ₘ e) =
      (g ≫ e) ≫ (λ_ R).inv ≫ (p ⊗ₘ 𝟙 R) := by
  have ht : (p ⊗ₘ g) ≫ (𝟙 H ⊗ₘ e) = p ⊗ₘ (g ≫ e) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  calc
    _ = (λ_ A).inv ≫ (p ⊗ₘ (g ≫ e)) := by
      simpa only [Category.assoc] using congrArg (fun z => (λ_ A).inv ≫ z) ht
    _ = _ := by
      simpa only [tensorHom_id] using leftUnitor_inv_comp_tensorHom p (g ≫ e)

omit [SymmetricCategory V] [MonoidalClosed V] [HasColimitsOfSize.{uI, uI} V] in
private theorem leftInsert_word (A R E H : V) (p : 𝟙_ V ⟶ H)
    (i : 𝟙_ V ⟶ R) (e : R ⟶ E) :
    (λ_ A).inv ≫ (p ⊗ₘ ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A))) ≫
        (𝟙 H ⊗ₘ (e ⊗ₘ 𝟙 A)) =
      (λ_ A).inv ≫ ((i ≫ e) ⊗ₘ 𝟙 A) ≫ (λ_ (E ⊗ A)).inv ≫
        (p ⊗ₘ 𝟙 (E ⊗ A)) := by
  have h := insert_word p ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A)) (e ⊗ₘ 𝟙 A)
  have ht : ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A)) ≫ (e ⊗ₘ 𝟙 A) =
      (λ_ A).inv ≫ ((i ≫ e) ⊗ₘ 𝟙 A) := by
    rw [Category.assoc, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  have hf := congrArg (fun z => z ≫ (λ_ (E ⊗ A)).inv ≫ (p ⊗ₘ 𝟙 (E ⊗ A))) ht
  exact h.trans (by simpa only [Category.assoc] using hf)

omit [SymmetricCategory V] [MonoidalClosed V] [HasColimitsOfSize.{uI, uI} V] in
private theorem rightInsert_word (A R E H : V) (p : 𝟙_ V ⟶ H)
    (i : 𝟙_ V ⟶ R) (e : R ⟶ E) :
    (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) ≫
        (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ e)) =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e)) ≫ (λ_ (A ⊗ E)).inv ≫
        (p ⊗ₘ 𝟙 (A ⊗ E)) := by
  have h := insert_word p ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i)) (𝟙 A ⊗ₘ e)
  have ht : ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i)) ≫ (𝟙 A ⊗ₘ e) =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e)) := by
    rw [Category.assoc, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  have hf := congrArg (fun z => z ≫ (λ_ (A ⊗ E)).inv ≫ (p ⊗ₘ 𝟙 (A ⊗ E))) ht
  exact h.trans (by simpa only [Category.assoc] using hf)

/-- The original Day left-unitor inverse and represented unit recover the whole identity map. -/
theorem leftInv_unit_multiply (k : I) :
    Unitors.leftInvComponent d S k ≫
        Input.mapAt d.tensorEnrichedFunctor (unit d S L) (GradedNatTrans.unitId S) k ≫
        EnrichedFunctorCat.component (multiply d S L) k = 𝟙 (S.obj k) := by
  let A : V := S.obj k
  let R : V := (𝟙_ I) ⟶[V] (𝟙_ I)
  let E : V := S.obj (𝟙_ I)
  let H : V := ((𝟙_ I) ⊗ k) ⟶[V] k
  let p : 𝟙_ V ⟶ H := eHomEquiv V (λ_ k).hom
  let i : 𝟙_ V ⟶ R := eId V (𝟙_ I)
  let e : R ⟶ E := EnrichedFunctorCat.component (unit d S L) (𝟙_ I)
  let γ : H ⊗ (R ⊗ A) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) S k :=
    gen d.tensorEnrichedFunctor (GradedYoneda.representable (𝟙_ I)) S k (𝟙_ I, k)
  let γ' : H ⊗ (E ⊗ A) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k :=
    gen d.tensorEnrichedFunctor S S k (𝟙_ I, k)
  let f := Input.mapAt d.tensorEnrichedFunctor (unit d S L) (GradedNatTrans.unitId S) k
  let m := EnrichedFunctorCat.component (multiply d S L) k
  let g : S.obj ((𝟙_ I) ⊗ k) ⟶ A := S.toOrdinaryFunctor.map (λ_ k).hom
  have hm : γ ≫ f = (𝟙 H ⊗ₘ (e ⊗ₘ 𝟙 A)) ≫ γ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor (unit d S L)
      (GradedNatTrans.unitId S) k (𝟙_ I, k)).trans
      (congrArg (fun z => (𝟙 H ⊗ₘ (e ⊗ₘ z)) ≫ γ') (GradedNatTrans.unitId_component S k))
  have he : i ≫ e = L.epsilon := unit_epsilon d S L
  have hg : (λ_ (E ⊗ A)).inv ≫ (p ⊗ₘ 𝟙 (E ⊗ A)) ≫ γ' ≫ m =
      L.mu (𝟙_ I) k ≫ g := labelledGenerator_multiply d S L (𝟙_ I, k) (λ_ k).hom
  have hu : L.epsilon ▷ A ≫ L.mu (𝟙_ I) k ≫ g = (λ_ A).hom := (L.unit k).1.symm
  suffices h : (λ_ A).inv ≫ (p ⊗ₘ ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A))) ≫ γ ≫ f ≫ m = 𝟙 A by
    have hl : Unitors.leftInvComponent d S k =
        (λ_ A).inv ≫ (p ⊗ₘ ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A))) ≫ γ := rfl
    have hc := congrArg (fun z => z ≫ f ≫ m) hl
    exact hc.trans (by simpa only [Category.assoc] using h)
  calc
    _ = (λ_ A).inv ≫ (p ⊗ₘ ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A))) ≫
        (𝟙 H ⊗ₘ (e ⊗ₘ 𝟙 A)) ≫ γ' ≫ m := by
      simpa only [Category.assoc] using
        congrArg (fun z => (λ_ A).inv ≫ (p ⊗ₘ ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A))) ≫ z ≫ m) hm
    _ = (λ_ A).inv ≫ ((i ≫ e) ⊗ₘ 𝟙 A) ≫ (λ_ (E ⊗ A)).inv ≫
        (p ⊗ₘ 𝟙 (E ⊗ A)) ≫ γ' ≫ m := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ γ' ≫ m) (leftInsert_word A R E H p i e)
    _ = (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ (λ_ (E ⊗ A)).inv ≫
        (p ⊗ₘ 𝟙 (E ⊗ A)) ≫ γ' ≫ m :=
      congrArg (fun z => (λ_ A).inv ≫ (z ⊗ₘ 𝟙 A) ≫ (λ_ (E ⊗ A)).inv ≫
        (p ⊗ₘ 𝟙 (E ⊗ A)) ≫ γ' ≫ m) he
    _ = (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ L.mu (𝟙_ I) k ≫ g :=
      congrArg (fun z => (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A) ≫ z) hg
    _ = (λ_ A).inv ≫ (λ_ A).hom := by
      simpa only [tensorHom_id, Category.assoc] using congrArg (fun z => (λ_ A).inv ≫ z) hu
    _ = 𝟙 A := Iso.inv_hom_id (λ_ A)

/-- The original Day right-unitor inverse and represented unit recover the whole identity map. -/
theorem rightInv_unit_multiply (k : I) :
    Unitors.rightInvComponent d S k ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (unit d S L) k ≫
        EnrichedFunctorCat.component (multiply d S L) k = 𝟙 (S.obj k) := by
  let A : V := S.obj k
  let R : V := (𝟙_ I) ⟶[V] (𝟙_ I)
  let E : V := S.obj (𝟙_ I)
  let H : V := (k ⊗ (𝟙_ I)) ⟶[V] k
  let p : 𝟙_ V ⟶ H := eHomEquiv V (ρ_ k).hom
  let i : 𝟙_ V ⟶ R := eId V (𝟙_ I)
  let e : R ⟶ E := EnrichedFunctorCat.component (unit d S L) (𝟙_ I)
  let γ : H ⊗ (A ⊗ R) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S
      (GradedYoneda.representable (𝟙_ I)) k :=
    gen d.tensorEnrichedFunctor S (GradedYoneda.representable (𝟙_ I)) k (k, 𝟙_ I)
  let γ' : H ⊗ (A ⊗ E) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k :=
    gen d.tensorEnrichedFunctor S S k (k, 𝟙_ I)
  let f := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (unit d S L) k
  let m := EnrichedFunctorCat.component (multiply d S L) k
  let g : S.obj (k ⊗ (𝟙_ I)) ⟶ A := S.toOrdinaryFunctor.map (ρ_ k).hom
  have hm : γ ≫ f = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ e)) ≫ γ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S)
      (unit d S L) k (k, 𝟙_ I)).trans
      (congrArg (fun z => (𝟙 H ⊗ₘ (z ⊗ₘ e)) ≫ γ') (GradedNatTrans.unitId_component S k))
  have he : i ≫ e = L.epsilon := unit_epsilon d S L
  have hg : (λ_ (A ⊗ E)).inv ≫ (p ⊗ₘ 𝟙 (A ⊗ E)) ≫ γ' ≫ m =
      L.mu k (𝟙_ I) ≫ g := labelledGenerator_multiply d S L (k, 𝟙_ I) (ρ_ k).hom
  have hu : A ◁ L.epsilon ≫ L.mu k (𝟙_ I) ≫ g = (ρ_ A).hom := (L.unit k).2.symm
  suffices h : (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) ≫ γ ≫ f ≫ m = 𝟙 A by
    have hl : Unitors.rightInvComponent d S k =
        (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) ≫ γ := rfl
    have hc := congrArg (fun z => z ≫ f ≫ m) hl
    exact hc.trans (by simpa only [Category.assoc] using h)
  calc
    _ = (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) ≫
        (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ e)) ≫ γ' ≫ m := by
      simpa only [Category.assoc] using
        congrArg (fun z => (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) ≫ z ≫ m) hm
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e)) ≫ (λ_ (A ⊗ E)).inv ≫
        (p ⊗ₘ 𝟙 (A ⊗ E)) ≫ γ' ≫ m := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ γ' ≫ m) (rightInsert_word A R E H p i e)
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫ (λ_ (A ⊗ E)).inv ≫
        (p ⊗ₘ 𝟙 (A ⊗ E)) ≫ γ' ≫ m :=
      congrArg (fun z => (ρ_ A).inv ≫ (𝟙 A ⊗ₘ z) ≫ (λ_ (A ⊗ E)).inv ≫
        (p ⊗ₘ 𝟙 (A ⊗ E)) ≫ γ' ≫ m) he
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫ L.mu k (𝟙_ I) ≫ g :=
      congrArg (fun z => (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫ z) hg
    _ = (ρ_ A).inv ≫ (ρ_ A).hom := by
      simpa only [id_tensorHom, Category.assoc] using congrArg (fun z => (ρ_ A).inv ≫ z) hu
    _ = 𝟙 A := Iso.inv_hom_id (ρ_ A)

end CategoryTheory.EnrichedDayKernel.LaxMonoid
