/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientAlgebra
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorSourceNaturality

/-!
# Full original right sphere unit and associativity

The original coefficient action, complete source composition and tensorator
braiding give the external right sphere laws. The source index is symmetric,
as the actual orthogonal index is. All coefficient and spectrum values are
retained; these laws supply the remaining original Day module equations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]

/-- The original inverse block braid, coefficient block flip, reassociation and
two final block braids give the actual inverse source associator. -/
theorem rightSphere_comp_label (n a b : I) :
    (β_ (a ⊗ b) n).inv ≫ ((β_ a b).hom ▷ n) ≫ (α_ b a n).hom ≫
        (b ◁ (β_ a n).hom) ≫ (β_ b (n ⊗ a)).hom = (α_ n a b).inv := by
  have hNature := braiding_naturality_right b (β_ a n).hom
  have hForward : (α_ b a n).hom ≫ (β_ b (a ⊗ n)).hom =
      ((β_ b a).hom ▷ n) ≫ (α_ a b n).hom ≫ (a ◁ (β_ b n).hom) ≫
        (α_ a n b).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun z => z ≫ (α_ a n b).inv) (hexagon_forward b a n)
  have hReverse : (β_ (a ⊗ b) n).hom ≫ (α_ n a b).inv =
      (α_ a b n).hom ≫ (a ◁ (β_ b n).hom) ≫ (α_ a n b).inv ≫
        ((β_ a n).hom ▷ b) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z => (α_ a b n).hom ≫ z) (hexagon_reverse a b n)
  have hCancel : ((β_ a b).hom ▷ n) ≫ ((β_ b a).hom ▷ n) =
      𝟙 ((a ⊗ b) ⊗ n) := by
    rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight]
  have hLabel : ((β_ a b).hom ▷ n) ≫ (α_ b a n).hom ≫
      (b ◁ (β_ a n).hom) ≫ (β_ b (n ⊗ a)).hom =
    (β_ (a ⊗ b) n).hom ≫ (α_ n a b).inv := by
    calc
      _ = ((β_ a b).hom ▷ n) ≫ (α_ b a n).hom ≫
          (β_ b (a ⊗ n)).hom ≫ ((β_ a n).hom ▷ b) := by
        simpa only [Category.assoc] using congrArg
          (fun z => ((β_ a b).hom ▷ n) ≫ (α_ b a n).hom ≫ z) hNature
      _ = ((β_ a b).hom ▷ n) ≫ ((β_ b a).hom ▷ n) ≫ (α_ a b n).hom ≫
          (a ◁ (β_ b n).hom) ≫ (α_ a n b).inv ≫ ((β_ a n).hom ▷ b) := by
        simpa only [Category.assoc] using congrArg
          (fun z => ((β_ a b).hom ▷ n) ≫ z ≫ ((β_ a n).hom ▷ b)) hForward
      _ = (α_ a b n).hom ≫ (a ◁ (β_ b n).hom) ≫
          (α_ a n b).inv ≫ ((β_ a n).hom ▷ b) := by
        simpa only [Category.assoc, Category.id_comp] using congrArg
          (fun z => z ≫ (α_ a b n).hom ≫ (a ◁ (β_ b n).hom) ≫
            (α_ a n b).inv ≫ ((β_ a n).hom ▷ b)) hCancel
      _ = _ := hReverse.symm
  exact (congrArg (fun z => (β_ (a ⊗ b) n).inv ≫ z) hLabel).trans
    (Iso.inv_hom_id_assoc (β_ (a ⊗ b) n) (α_ n a b).inv)

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- The actual sphere epsilon and original index right unitor act as the whole identity. -/
theorem rightSphereAction_unit
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n : I) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁ L.epsilon) ≫ rightSphereAction d S L F n (𝟙_ I) ≫
      ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
        (ρ_ (F.toEnrichedFunctor.obj ⟨n⟩)).hom := by
  have hLabel : (β_ (𝟙_ I) n).hom ≫ (ρ_ n).hom = (λ_ n).hom := by
    rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hAction : rightSphereAction d S L F n (𝟙_ I) ≫
      ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
    coefficientAction d S L F n n (𝟙_ I) (λ_ n).hom :=
    (coefficientAction_postcompose d S L F n (n ⊗ 𝟙_ I) n (𝟙_ I)
      (β_ (𝟙_ I) n).hom (ρ_ n).hom).trans
        (congrArg (coefficientAction d S L F n n (𝟙_ I)) hLabel)
  exact (congrArg (fun z => (F.toEnrichedFunctor.obj ⟨n⟩ ◁ L.epsilon) ≫ z) hAction).trans
    (coefficientAction_unit d S L F n)

/-- The original whole right sphere action obeys the exact external associativity equation. -/
theorem rightSphereAction_assoc (B : EnrichedFunctor.LaxBraidedData L)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n a b : I) :
    (α_ (F.toEnrichedFunctor.obj ⟨n⟩) (S.obj a) (S.obj b)).inv ≫
      (rightSphereAction d S L F n a ▷ S.obj b) ≫
        rightSphereAction d S L F (n ⊗ a) b =
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁ L.mu a b) ≫ rightSphereAction d S L F n (a ⊗ b) ≫
      ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let k := n ⊗ a
  let l := (n ⊗ a) ⊗ b
  let f := (β_ a n).hom
  let g := (β_ b k).hom
  let label : (b ⊗ a) ⊗ n ⟶ l := (α_ b a n).hom ≫ (b ◁ f) ≫ g
  let rlabel : (a ⊗ b) ⊗ n ⟶ l := ((β_ a b).hom ⊗ₘ 𝟙 n) ≫ label
  let m : S.obj a ⊗ S.obj b ⟶ S.obj (b ⊗ a) :=
    (β_ (S.obj a) (S.obj b)).hom ≫ L.mu b a
  let c := coefficientHom d S n l (b ⊗ a) label
  let u := MonoidalClosed.uncurry
    (F.toEnrichedFunctor.map (⟨n⟩ : OperatorIndex d S L) ⟨l⟩)
  have hAction : (α_ X (S.obj a) (S.obj b)).inv ≫
      (rightSphereAction d S L F n a ▷ S.obj b) ≫ rightSphereAction d S L F k b =
    (X ◁ (m ≫ c)) ≫ u :=
    (coefficientAction_comp d S L F n k l a b f g).symm.trans
      (congrArg (fun z => (X ◁ z) ≫ u) (coefficientHom_comp d S L n k l a b f g))
  have hSplit : (X ◁ (m ≫ c)) ≫ u =
      (X ◁ m) ≫ coefficientAction d S L F n l (b ⊗ a) label :=
    (congrArg (fun z => z ≫ u) (whiskerLeft_comp X m c)).trans
      (Category.assoc (X ◁ m) (X ◁ c) u)
  have hBraided : L.mu a b ≫ S.toOrdinaryFunctor.map (β_ a b).hom = m := B.braided a b
  have hMu : (X ◁ m) ≫ coefficientAction d S L F n l (b ⊗ a) label =
      (X ◁ L.mu a b) ≫ (X ◁ S.toOrdinaryFunctor.map (β_ a b).hom) ≫
        coefficientAction d S L F n l (b ⊗ a) label :=
    (congrArg (fun z => (X ◁ z) ≫ coefficientAction d S L F n l (b ⊗ a) label)
      hBraided.symm).trans
        ((congrArg (fun z => z ≫ coefficientAction d S L F n l (b ⊗ a) label)
          (whiskerLeft_comp X (L.mu a b) (S.toOrdinaryFunctor.map (β_ a b).hom))).trans
            (Category.assoc (X ◁ L.mu a b) (X ◁ S.toOrdinaryFunctor.map (β_ a b).hom)
              (coefficientAction d S L F n l (b ⊗ a) label)))
  have hId : ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
      (𝟙 n) = 𝟙 X := Functor.map_id _ n
  have hTensorId :
      ((((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (𝟙 n)) ⊗ₘ
        S.toOrdinaryFunctor.map (β_ a b).hom) ≫
          coefficientAction d S L F n l (b ⊗ a) label =
      (X ◁ S.toOrdinaryFunctor.map (β_ a b).hom) ≫
        coefficientAction d S L F n l (b ⊗ a) label :=
    (congrArg (fun z => (z ⊗ₘ S.toOrdinaryFunctor.map (β_ a b).hom) ≫
      coefficientAction d S L F n l (b ⊗ a) label) hId).trans
        (congrArg (fun z => z ≫ coefficientAction d S L F n l (b ⊗ a) label)
          (id_tensorHom X (S.toOrdinaryFunctor.map (β_ a b).hom)))
  have hCovar : (X ◁ S.toOrdinaryFunctor.map (β_ a b).hom) ≫
      coefficientAction d S L F n l (b ⊗ a) label =
    coefficientAction d S L F n l (a ⊗ b) rlabel :=
    hTensorId.symm.trans (coefficientAction_twoInputs d S L F n n l (a ⊗ b) (b ⊗ a)
      (𝟙 n) (β_ a b).hom label)
  have hIndex : (β_ (a ⊗ b) n).inv ≫ rlabel = (α_ n a b).inv := by
    simpa only [rlabel, label, f, g, k, l, tensorHom_id, Category.assoc] using
      rightSphere_comp_label n a b
  have hRecover : coefficientAction d S L F n l (a ⊗ b) rlabel =
      rightSphereAction d S L F n (a ⊗ b) ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv :=
    (coefficientAction_from_rightSphere_and_index d S L F n l (a ⊗ b) rlabel).trans
      (congrArg (fun z => rightSphereAction d S L F n (a ⊗ b) ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map z) hIndex)
  exact hAction.trans (hSplit.trans (hMu.trans
    ((congrArg (fun z => (X ◁ L.mu a b) ≫ z) hCovar).trans
      (congrArg (fun z => (X ◁ L.mu a b) ≫ z) hRecover))))

end CategoryTheory.Enriched.SphereOperator
