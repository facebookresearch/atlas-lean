/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
public import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffle
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.ActionIndexComparison

/-!
# Coefficient actions on enriched cotensors

Over a symmetric monoidal closed base, a coefficient arrow into an enriched
Hom gives an action formula for the scalar cotensor of an enriched
functor into the base. The formula expresses its uncurried hom-object map using the
coefficient shuffle, closed evaluation, braiding and the original enriched
action, followed by currying.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor.CotensorCoefficientAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

/-- Every complete coefficient arrow into the original enriched Hom acts on the actual pointwise
cotensor by the full coefficient shuffle and original evaluation. -/
theorem action (M : V) (G : EnrichedFunctor V I V) (a b : I)
    (A : V) (q : A ⟶ (a ⟶[V] b)) :
    (β_ A ((ihom M).obj (G.obj a))).hom ≫
        (((ihom M).obj (G.obj a)) ◁ q) ≫
        MonoidalClosed.uncurry ((EnrichedFunctor.cotensor M G).map a b) =
      MonoidalClosed.curry
        (CoefficientShuffle.map M A ((ihom M).obj (G.obj a)) ≫
          (A ◁ (ihom.ev M).app (G.obj a)) ≫
          (β_ A (G.obj a)).hom ≫ (G.obj a ◁ q) ≫
          MonoidalClosed.uncurry (G.map a b)) := by
  let X := G.obj a
  let H := (ihom M).obj X
  let e : M ⊗ H ⟶ X := (ihom.ev M).app X
  have hs : CoefficientShuffle.map M A H ≫ (β_ A (M ⊗ H)).hom =
      (M ◁ (β_ A H).hom) ≫ (α_ M H A).inv := by
    simpa only [CoefficientShuffle.map, CoefficientIndexBraiding.leftCoefficientComparison,
      Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc] using
      CoefficientIndexBraiding.rightOrder A M H
  apply MonoidalClosed.uncurry_injective (A := M)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    EnrichedFunctor.cotensor_doubleUncurry, MonoidalClosed.uncurry_curry,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  change (M ◁ (β_ A H).hom) ≫ (α_ M H A).inv ≫ (e ▷ A) ≫
      (X ◁ q) ≫ MonoidalClosed.uncurry (G.map a b) =
    CoefficientShuffle.map M A H ≫ (A ◁ e) ≫ (β_ A X).hom ≫
      (X ◁ q) ≫ MonoidalClosed.uncurry (G.map a b)
  have hb : (A ◁ e) ≫ (β_ A X).hom = (β_ A (M ⊗ H)).hom ≫ (e ▷ A) :=
    BraidedCategory.braiding_naturality_right A e
  rw [reassoc_of% hb, reassoc_of% hs]

end CategoryTheory.EnrichedFunctor.CotensorCoefficientAction
