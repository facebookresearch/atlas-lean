/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientAlgebra

/-!
# Original coefficient unit and index recovery

The original coefficient unit recovers the complete index inclusion at every
ordinary index arrow. The source coefficient unitor is also retained as its
actual complete continuous action. These are original map equalities used
by the full module/operator reconstruction, not extra recovery hypotheses.
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

/-- The entire unit coefficient inclusion is the literal original unit coend point. -/
theorem epsilon_coefficientHom (n k : I) (f : (𝟙_ I) ⊗ n ⟶ k) :
    L.epsilon ≫ coefficientHom d S n k (𝟙_ I) f =
      (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ L.epsilon) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) := by
  let p := eHomEquiv V f
  let b : S.obj (𝟙_ I) ⟶ (((𝟙_ I) ⊗ n) ⟶[V] k) ⊗ S.obj (𝟙_ I) :=
    (λ_ (S.obj (𝟙_ I))).inv ≫ (p ⊗ₘ 𝟙 (S.obj (𝟙_ I)))
  let i := weightedCoend.ι (weight d n k) S (𝟙_ I)
  have hb : L.epsilon ≫ b = (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon) := by
    dsimp only [b]
    rw [tensorHom_id]
    exact (leftUnitor_inv_comp_tensorHom p L.epsilon).symm
  have hc : coefficientHom d S n k (𝟙_ I) f = b ≫ i := rfl
  calc
    _ = L.epsilon ≫ (b ≫ i) := congrArg (fun z => L.epsilon ≫ z) hc
    _ = (L.epsilon ≫ b) ≫ i := (Category.assoc _ _ _).symm
    _ = ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon)) ≫ i := congrArg (fun z => z ≫ i) hb
    _ = _ := Category.assoc _ _ _

/-- Every actual ordinary index point is recovered from the original coefficient unit. -/
theorem indexHom_point_eq_coefficient (n k : I) (f : n ⟶ k) :
    eHomEquiv V f ≫ indexHom d S L n k =
      L.epsilon ≫ coefficientHom d S n k (𝟙_ I) ((λ_ n).hom ≫ f) :=
  (indexHom_point d S L f).trans
    (epsilon_coefficientHom d S L n k ((λ_ n).hom ≫ f)).symm

/-- The original unit coefficient recovers the actual entire operator identity. -/
theorem epsilon_coefficientHom_identity (n : I) :
    L.epsilon ≫ coefficientHom d S n n (𝟙_ I) (λ_ n).hom = identityGenerator d S L n :=
  epsilon_coefficientHom d S L n n (λ_ n).hom

omit [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)] in
/-- The source left unit law keeps the actual full decoded coefficient action. -/
theorem coefficient_left_unit_action (a : I) :
    (L.epsilon ▷ S.obj a) ≫ L.mu (𝟙_ I) a ≫
      ((ρ_ (S.obj ((𝟙_ I) ⊗ a))).inv ≫
        S.obj ((𝟙_ I) ⊗ a) ◁ eHomEquiv V (λ_ a).hom ≫
        MonoidalClosed.uncurry (S.map ((𝟙_ I) ⊗ a) a)) = (λ_ (S.obj a)).hom := by
  let s := (eHomEquiv V).symm
    (eHomEquiv V (λ_ a).hom ≫ S.map ((𝟙_ I) ⊗ a) a)
  have hs : s = (ρ_ (S.obj ((𝟙_ I) ⊗ a))).inv ≫
      S.obj ((𝟙_ I) ⊗ a) ◁ eHomEquiv V (λ_ a).hom ≫
      MonoidalClosed.uncurry (S.map ((𝟙_ I) ⊗ a) a) := by
    dsimp only [s]
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
    dsimp only [MonoidalClosed.uncurry']
    rw [MonoidalClosed.uncurry_natural_left]
  have h : (L.epsilon ▷ S.obj a) ≫ L.mu (𝟙_ I) a ≫ s = (λ_ (S.obj a)).hom :=
    (L.unit a).1.symm
  exact (congrArg (fun z => (L.epsilon ▷ S.obj a) ≫ L.mu (𝟙_ I) a ≫ z) hs).symm.trans h


/-- Every full coefficient inclusion is natural under the original target-index arrow. -/
theorem coefficientHom_postcompose (n k l a : I)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    (ρ_ (S.obj a)).inv ≫
      (coefficientHom d S n k a f ⊗ₘ (eHomEquiv V g ≫ indexHom d S L k l)) ≫
      composition d S L n k l = coefficientHom d S n l a (f ≫ g) := by
  let U := 𝟙_ I
  let A := S.obj a
  let B := S.obj U
  let C := S.obj (U ⊗ a)
  let pf := coefficientHom d S n k a f
  let g' := (λ_ k).hom ≫ g
  let pg := coefficientHom d S k l U g'
  let m := (β_ A B).hom ≫ L.mu U a
  let label := (α_ U a n).hom ≫ (U ◁ f) ≫ g'
  let c := coefficientHom d S n l (U ⊗ a) label
  let z := coefficientHom d S n l a (f ≫ g)
  let s : C ⟶ A :=
    (ρ_ C).inv ≫ C ◁ eHomEquiv V (λ_ a).hom ≫
      MonoidalClosed.uncurry (S.map (U ⊗ a) a)
  have hPoint : eHomEquiv V g ≫ indexHom d S L k l = L.epsilon ≫ pg :=
    indexHom_point_eq_coefficient d S L k l g
  have hPair :
      pf ⊗ₘ (L.epsilon ≫ pg) = (𝟙 A ⊗ₘ L.epsilon) ≫ (pf ⊗ₘ pg) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (𝟙 A) L.epsilon pf pg).symm
  have hProduct : (pf ⊗ₘ pg) ≫ composition d S L n k l = m ≫ c :=
    coefficientHom_comp d S L n k l a U f g'
  have hPrefix :
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫ m =
        (λ_ A).inv ≫ (L.epsilon ▷ A) ≫ L.mu U a := by
    dsimp only [m]
    rw [id_tensorHom, BraidedCategory.braiding_naturality_right_assoc,
      braiding_tensorUnit_right]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hMiddle : (U ◁ f) ≫ (λ_ k).hom = (λ_ (a ⊗ n)).hom ≫ f :=
    leftUnitor_naturality f
  have hTensorUnit : (α_ U a n).hom ≫ (λ_ (a ⊗ n)).hom = (λ_ a).hom ▷ n := by
    monoidal
  have hLabel : label = ((λ_ a).hom ▷ n) ≫ (f ≫ g) := by
    calc
      _ = (α_ U a n).hom ≫ (U ◁ f) ≫ (λ_ k).hom ≫ g := by
        simp only [label, g']
      _ = (α_ U a n).hom ≫ (λ_ (a ⊗ n)).hom ≫ f ≫ g := by
        simpa only [Category.assoc] using congrArg
          (fun t => (α_ U a n).hom ≫ t ≫ g) hMiddle
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ f ≫ g) hTensorUnit
  have hRelation : c = s ≫ z :=
    (congrArg (coefficientHom d S n l (U ⊗ a)) hLabel).trans
      (coefficientHom_relation d S n l (U ⊗ a) a (λ_ a).hom (f ≫ g))
  have hUnit : (L.epsilon ▷ A) ≫ L.mu U a ≫ s = (λ_ A).hom :=
    coefficient_left_unit_action d S L a
  calc
    _ = (ρ_ A).inv ≫ (pf ⊗ₘ (L.epsilon ≫ pg)) ≫ composition d S L n k l :=
      congrArg (fun t => (ρ_ A).inv ≫ (pf ⊗ₘ t) ≫ composition d S L n k l) hPoint
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫
        (pf ⊗ₘ pg) ≫ composition d S L n k l := by
      simpa only [Category.assoc] using congrArg
        (fun t => (ρ_ A).inv ≫ t ≫ composition d S L n k l) hPair
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫ m ≫ c :=
      congrArg (fun t => (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon) ≫ t) hProduct
    _ = (λ_ A).inv ≫ (L.epsilon ▷ A) ≫ L.mu U a ≫ c := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ c) hPrefix
    _ = (λ_ A).inv ≫ (L.epsilon ▷ A) ≫ L.mu U a ≫ (s ≫ z) :=
      congrArg (fun t => (λ_ A).inv ≫ (L.epsilon ▷ A) ≫ L.mu U a ≫ t) hRelation
    _ = (λ_ A).inv ≫ (λ_ A).hom ≫ z := by
      simpa only [Category.assoc] using congrArg (fun t => (λ_ A).inv ≫ t ≫ z) hUnit
    _ = _ := Iso.inv_hom_id_assoc _ z

/-- The original sphere coefficient and index action recover every original coefficient map. -/
theorem coefficientHom_from_sphere_and_index (n k a : I) (f : a ⊗ n ⟶ k) :
    (ρ_ (S.obj a)).inv ≫
      (coefficientHom d S n (a ⊗ n) a (𝟙 (a ⊗ n)) ⊗ₘ
        (eHomEquiv V f ≫ indexHom d S L (a ⊗ n) k)) ≫
      composition d S L n (a ⊗ n) k = coefficientHom d S n k a f := by
  simpa only [Category.id_comp] using
    coefficientHom_postcompose d S L n (a ⊗ n) k a (𝟙 (a ⊗ n)) f

end CategoryTheory.Enriched.SphereOperator
