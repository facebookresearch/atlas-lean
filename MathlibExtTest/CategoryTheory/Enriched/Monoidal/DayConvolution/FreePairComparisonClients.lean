/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.FreePairComparison

/-!
# Public clients of the enriched Day free-pair comparison

Use the complete object isomorphism and its coefficient natural family through
the public API. Both coefficient arrows and both source-Hom arrows retain their
original naturality squares while the comparison constructors stay irreducible.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace MathlibExtTest.FreePairComparisonClients

open CategoryTheory.EnrichedFunctorCat CategoryTheory.EnrichedDayKernel
attribute [local instance] Enriched.prodCategory
attribute [local irreducible] FreePairComparison.iso FreePairComparison.functorIso

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) F.toEnrichedFunctor)]

/-- The public object comparison identifies the entire chosen Day free pair. -/
def selectedPairIso (n : C) (m : D) (X Y : V) :
    FreePairComparison.dayObject T n m X Y ≅ Free.object (T.obj (n, m)) (X ⊗ Y) :=
  FreePairComparison.iso T n m X Y

/-- The two original coefficient variables form the complete public natural isomorphism. -/
def selectedPairFunctorIso (n : C) (m : D) :
    FreePairComparison.dayPairFunctor T n m ≅ FreePairComparison.freePairFunctor T n m :=
  FreePairComparison.functorIso T n m

/-- A caller obtains the same full comparison at each coefficient pair. -/
theorem selectedPairFunctorIso_component (n : C) (m : D) (X Y : V) :
    (selectedPairFunctorIso T n m).hom.app (X, Y) = (selectedPairIso T n m X Y).hom :=
  FreePairComparison.functorIso_hom_app T n m (X, Y)

/-- Both coefficient maps preserve the complete public comparison. -/
theorem coefficient_square (n : C) (m : D)
    {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') :
    Input.natTrans T (Free.coefficientMap n f) (Free.coefficientMap m g) ≫
      (selectedPairIso T n m X' Y').hom =
        (selectedPairIso T n m X Y).hom ≫ Free.coefficientMap (T.obj (n, m)) (f ⊗ₘ g) :=
  FreePairComparison.iso_coefficient T n m f g

/-- Both complete source-Hom maps retain their original contravariant square. -/
theorem source_square {n n' : C} {m m' : D}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V) :
    Input.natTrans T (Free.sourceMap p X) (Free.sourceMap q Y) ≫
      (selectedPairIso T n m X Y).hom =
        (selectedPairIso T n' m' X Y).hom ≫
          Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫ T.map (n, m) (n', m')) (X ⊗ Y) :=
  FreePairComparison.iso_source T p q X Y

end MathlibExtTest.FreePairComparisonClients
