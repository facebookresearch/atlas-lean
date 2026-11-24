/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeWeightedEnd

/-!
# Precomposition by an actual map between free enriched functors

The constructed free/evaluation adjunct and full target Hom action determine
the weighted-end action of every genuine free-source map. The result uses
exactly the two free-weighted ends involved. It supplies the actual arbitrary-
index comparison needed by spectrum stabilization.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uI uV vV

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.FreeWeightedEndMap

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

/-- The actual free adjunct, shuffle and full target action give its internal-Hom map. -/
@[no_expose]
def transpose (a b : I) (A B : V) (X : EnrichedFunctor V I V)
    (f : EnrichedFunctorCat.Free.object b B ⟶ EnrichedFunctorCat.Free.object a A) :
    (ihom A).obj (X.obj a) ⟶ (ihom B).obj (X.obj b) := by
  let T := (ihom A).obj (X.obj a)
  let j : B ⟶ A ⊗ (a ⟶[V] b) :=
    (EnrichedFunctorCat.Free.adjunction (V := V) b).homEquiv
      B (EnrichedFunctorCat.Free.object a A) f
  exact MonoidalClosed.curry
    ((j ▷ T) ≫
      ((α_ A (a ⟶[V] b) T).hom ≫ (A ◁ (β_ (a ⟶[V] b) T).hom) ≫
        (α_ A T (a ⟶[V] b)).inv ≫
        ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (X.map a b)))

private theorem transpose_eq_private (a b : I) (A B : V) (X : EnrichedFunctor V I V)
    (f : EnrichedFunctorCat.Free.object b B ⟶ EnrichedFunctorCat.Free.object a A) :
    transpose a b A B X f =
      let T := (ihom A).obj (X.obj a)
      let j : B ⟶ A ⊗ (a ⟶[V] b) :=
        (EnrichedFunctorCat.Free.adjunction (V := V) b).homEquiv
          B (EnrichedFunctorCat.Free.object a A) f
      MonoidalClosed.curry
        ((j ▷ T) ≫
          ((α_ A (a ⟶[V] b) T).hom ≫ (A ◁ (β_ (a ⟶[V] b) T).hom) ≫
            (α_ A T (a ⟶[V] b)).inv ≫
            ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
            MonoidalClosed.uncurry (X.map a b))) := rfl

/-- The map retains the original free adjunct, positive shuffle and full target action. -/
theorem transpose_eq (a b : I) (A B : V) (X : EnrichedFunctor V I V)
    (f : EnrichedFunctorCat.Free.object b B ⟶ EnrichedFunctorCat.Free.object a A) :
    transpose a b A B X f =
      let T := (ihom A).obj (X.obj a)
      let j : B ⟶ A ⊗ (a ⟶[V] b) :=
        (EnrichedFunctorCat.Free.adjunction (V := V) b).homEquiv
          B (EnrichedFunctorCat.Free.object a A) f
      MonoidalClosed.curry
        ((j ▷ T) ≫
          ((α_ A (a ⟶[V] b) T).hom ≫ (A ◁ (β_ (a ⟶[V] b) T).hom) ≫
            (α_ A T (a ⟶[V] b)).inv ≫
            ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
            MonoidalClosed.uncurry (X.map a b))) :=
  transpose_eq_private a b A B X f

variable (a b : I) (A B : V) (X : EnrichedFunctor V I V)
  [HasProduct (weightedEnd.objects
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)]
  [HasProduct (weightedEnd.relations
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)]
  [HasEqualizer
    (weightedEnd.leftMap (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)
    (weightedEnd.rightMap (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)]
  [HasProduct (weightedEnd.objects
    (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor X)]
  [HasProduct (weightedEnd.relations
    (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor X)]
  [HasEqualizer
    (weightedEnd.leftMap (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor X)
    (weightedEnd.rightMap (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor X)]

set_option backward.isDefEq.respectTransparency false in
private theorem precomp_forward_private
    (f : EnrichedFunctorCat.Free.object b B ⟶ EnrichedFunctorCat.Free.object a A) :
    weightedEnd.mapWeight (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X
        (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor f ≫
        FreeWeightedEnd.forward b B X =
      FreeWeightedEnd.forward a A X ≫ transpose a b A B X f := by
  let WA := (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
  let WB := (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor
  let T := (ihom A).obj (X.obj a)
  let j : B ⟶ A ⊗ (a ⟶[V] b) :=
    (EnrichedFunctorCat.Free.adjunction (V := V) b).homEquiv
      B (EnrichedFunctorCat.Free.object a A) f
  let ηB : B ⟶ WB.obj b :=
    (EnrichedFunctorCat.Free.adjunction (V := V) b).unit.app B
  let fb : WB.obj b ⟶ WA.obj b := (eHomEquiv V).symm (f.app b)
  let θ : (A ⊗ (a ⟶[V] b)) ⊗ T ⟶ X.obj b :=
    (α_ A (a ⟶[V] b) T).hom ≫ (A ◁ (β_ (a ⟶[V] b) T).hom) ≫
      (α_ A T (a ⟶[V] b)).inv ≫
      ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (X.map a b)
  have hAdjunct : j = ηB ≫ fb := by
    simpa only [EnrichedFunctorCat.evaluation_map] using
      (EnrichedFunctorCat.Free.adjunction (V := V) b).homEquiv_apply
        B (EnrichedFunctorCat.Free.object a A) f
  have hPre : (MonoidalClosed.pre fb).app (X.obj b) ≫
      (MonoidalClosed.pre ηB).app (X.obj b) = (MonoidalClosed.pre j).app (X.obj b) := by
    rw [hAdjunct]
    exact (NatTrans.congr_app (MonoidalClosed.pre_map ηB fb) (X.obj b)).symm
  have hRaw : weightedEnd.mapWeight WA X WB f ≫ FreeWeightedEnd.forward b B X =
      weightedEnd.π WA X b ≫ (MonoidalClosed.pre j).app (X.obj b) := by
    rw [FreeWeightedEnd.forward_eq, ← Category.assoc, weightedEnd.mapWeight_π]
    simpa only [Category.assoc] using congrArg
      (fun z => weightedEnd.π WA X b ≫ z) hPre
  have hInverse : FreeWeightedEnd.inverse a A X ≫ weightedEnd.π WA X b =
      MonoidalClosed.curry θ :=
    FreeWeightedEnd.inverse_π a A X b
  have : IsIso (FreeWeightedEnd.inverse a A X) := by
    rw [← FreeWeightedEnd.iso_inv]
    infer_instance
  apply (cancel_epi (FreeWeightedEnd.inverse a A X)).1
  calc
    _ = FreeWeightedEnd.inverse a A X ≫
        (weightedEnd.π WA X b ≫ (MonoidalClosed.pre j).app (X.obj b)) :=
      congrArg (fun z => FreeWeightedEnd.inverse a A X ≫ z) hRaw
    _ = (FreeWeightedEnd.inverse a A X ≫ weightedEnd.π WA X b) ≫
        (MonoidalClosed.pre j).app (X.obj b) := (Category.assoc _ _ _).symm
    _ = MonoidalClosed.curry θ ≫ (MonoidalClosed.pre j).app (X.obj b) := by rw [hInverse]
    _ = MonoidalClosed.curry ((j ▷ T) ≫ θ) := MonoidalClosed.curry_pre_app j θ
    _ = transpose a b A B X f := by rfl
    _ = FreeWeightedEnd.inverse a A X ≫
        (FreeWeightedEnd.forward a A X ≫ transpose a b A B X f) := by
      rw [← Category.assoc, FreeWeightedEnd.inverse_forward, Category.id_comp]

/-- Precomposition by the actual free arrow is its complete original adjunct action. -/
theorem precomp_forward
    (f : EnrichedFunctorCat.Free.object b B ⟶ EnrichedFunctorCat.Free.object a A) :
    weightedEnd.mapWeight (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X
        (EnrichedFunctorCat.Free.object b B).toEnrichedFunctor f ≫
        FreeWeightedEnd.forward b B X =
      FreeWeightedEnd.forward a A X ≫ transpose a b A B X f :=
  precomp_forward_private a b A B X f

end CategoryTheory.Enriched.FreeWeightedEndMap
