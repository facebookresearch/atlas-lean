/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorSourceNaturality

/-!
# Full two-input right sphere naturality

The original block braiding changes the operator's coefficient orientation
to the original right sphere orientation. The two actual input arrows then
act through the restricted index and original coefficient functor. The full
enriched pair-point equations retain the tensor of both index Hom objects.
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

omit [BraidedCategory V] in
/-- An arbitrary actual unit point computes the full uncurried closed action. -/
theorem uncurry_unitPoint {X Y H : V} (p : 𝟙_ V ⟶ H)
    (m : H ⟶ (ihom X).obj Y) (r : X ⟶ Y) (h : p ≫ m = eHomEquiv V r) :
    (X ◁ p) ≫ MonoidalClosed.uncurry m = (ρ_ X).hom ≫ r := by
  calc
    _ = MonoidalClosed.uncurry (p ≫ m) := (MonoidalClosed.uncurry_natural_left p m).symm
    _ = MonoidalClosed.uncurry (eHomEquiv V r) := congrArg MonoidalClosed.uncurry h
    _ = _ := by
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv]
      exact MonoidalClosed.uncurry_curry ((ρ_ X).hom ≫ r)

attribute [local instance] Enriched.prodCategory

omit [MonoidalCategory I] in
/-- Both entire index Hom points retain the actual external tensor action. -/
theorem externalTensor_pairPoint (X S : EnrichedFunctor V I V)
    {n m a b : I} (f : n ⟶ m) (u : a ⟶ b) :
    ((λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V u)) ≫
      (X.externalTensor S).map (n, a) (m, b) =
        eHomEquiv V (X.toOrdinaryFunctor.map f ⊗ₘ S.toOrdinaryFunctor.map u) := by
  let p := eHomEquiv V f
  let q := eHomEquiv V u
  let h := X.map n m
  let j := S.map a b
  let r : X.obj n ⟶ X.obj m := X.toOrdinaryFunctor.map f
  let s : S.obj a ⟶ S.obj b := S.toOrdinaryFunctor.map u
  let t := (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
    (X.obj n) (X.obj m) (S.obj a) (S.obj b)
  have hPair : (p ⊗ₘ q) ≫ (h ⊗ₘ j) = (p ≫ h) ⊗ₘ (q ≫ j) :=
    tensorHom_comp_tensorHom p q h j
  have hX : eHomEquiv V r = p ≫ h := EnrichedFunctor.toOrdinaryFunctor_map X f
  have hS : eHomEquiv V s = q ≫ j := EnrichedFunctor.toOrdinaryFunctor_map S u
  have hMiddle : ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫
      (X.externalTensor S).map (n, a) (m, b) =
      (λ_ (𝟙_ V)).inv ≫ ((p ≫ h) ⊗ₘ (q ≫ j)) ≫ t :=
    (Category.assoc (λ_ (𝟙_ V)).inv (p ⊗ₘ q) ((h ⊗ₘ j) ≫ t)).trans
      ((congrArg (fun z => (λ_ (𝟙_ V)).inv ≫ z)
        (Category.assoc (p ⊗ₘ q) (h ⊗ₘ j) t).symm).trans
          (congrArg (fun z => (λ_ (𝟙_ V)).inv ≫ z ≫ t) hPair))
  have hPoints : (p ≫ h) ⊗ₘ (q ≫ j) = eHomEquiv V r ⊗ₘ eHomEquiv V s :=
    (congrArg (fun z => z ⊗ₘ (q ≫ j)) hX.symm).trans
      (congrArg (fun z => eHomEquiv V r ⊗ₘ z) hS.symm)
  have hTensor : (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V r ⊗ₘ eHomEquiv V s) ≫ t =
      eHomEquiv V (r ⊗ₘ s) :=
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap_eHomEquiv r s
  exact hMiddle.trans
    ((congrArg (fun z => (λ_ (𝟙_ V)).inv ≫ z ≫ t) hPoints).trans hTensor)

/-- The native tensor-index point retains the actual complete composite index action. -/
theorem tensorComp_pairPoint (d : EnrichedMonoidalCategoryData V I)
    (X : EnrichedFunctor V I V) {n m a b : I} (f : n ⟶ m) (u : a ⟶ b) :
    ((λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V u)) ≫
      (d.tensorEnrichedFunctor.comp V X).map (n, a) (m, b) =
        eHomEquiv V (X.toOrdinaryFunctor.map (f ⊗ₘ u)) := by
  let p := (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V u)
  let t := d.tensorMap n m a b
  let h := X.map (n ⊗ a) (m ⊗ b)
  have hTensor : p ≫ t = eHomEquiv V (f ⊗ₘ u) :=
    (Category.assoc (λ_ (𝟙_ V)).inv (eHomEquiv V f ⊗ₘ eHomEquiv V u) t).trans
      (d.tensorMap_eHomEquiv f u)
  exact (Category.assoc p t h).symm.trans
    ((congrArg (fun z => z ≫ h) hTensor).trans
      (EnrichedFunctor.toOrdinaryFunctor_map X (f ⊗ₘ u)).symm)

variable [BraidedCategory I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- Both actual input arrows respect the entire original right sphere action. -/
theorem rightSphereAction_twoInputs
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) {n m a b : I}
    (f : n ⟶ m) (u : a ⟶ b) :
    (((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f ⊗ₘ
        S.toOrdinaryFunctor.map u) ≫ rightSphereAction d S L F m b =
      rightSphereAction d S L F n a ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (f ⊗ₘ u) := by
  have hInputs := coefficientAction_twoInputs d S L F n m (m ⊗ b) a b f u (β_ b m).hom
  have hBraid : (u ⊗ₘ f) ≫ (β_ b m).hom = (β_ a n).hom ≫ (f ⊗ₘ u) :=
    BraidedCategory.braiding_naturality u f
  have hLabel := congrArg (coefficientAction d S L F n (m ⊗ b) a) hBraid
  have hOutput := coefficientAction_postcompose d S L F n (n ⊗ a) (m ⊗ b) a
    (β_ a n).hom (f ⊗ₘ u)
  exact hInputs.trans (hLabel.trans hOutput.symm)

end CategoryTheory.Enriched.SphereOperator
