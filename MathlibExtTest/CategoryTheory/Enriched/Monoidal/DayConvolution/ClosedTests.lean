/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedMaps

/-!
# Public clients of the actual Day closed structure

The chosen monoidal category and closed factory are used explicitly. The
right-translation end, all original source and target maps, and the complete
unit and counit formulas are checked on independent value and index universes.
The index category is only monoidal in these clients.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ClosedTests

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)

/-- The actual closed-class value is the whole literal right-translation weighted end. -/
example (F Y : EnrichedFunctorCat V I) (c : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := Closed.monoidalClosed d
    ((ihom F).obj Y).toEnrichedFunctor.obj c =
      WeightedEndVariance.object F (Closed.translatedTarget d Y c) := rfl

/-- The genuine selected closed-class curry retains every original Day point. -/
theorem selected_curry_projection (F G Y : EnrichedFunctorCat V I)
    (f : Closed.tensorObject d F G ⟶ Y) (c j : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := Closed.monoidalClosed d
    component (MonoidalClosed.curry f) c ≫ Closed.π d F Y c j =
      MonoidalClosed.curry
        (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor
          G.toEnrichedFunctor (j, c) ≫ component f (j ⊗ c)) :=
  Closed.closedCurry_π d F G Y f c j

/-- The actual closed-class source arrow retains every complete original source component. -/
theorem selected_pre_projection {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (Y : EnrichedFunctorCat V I) (c j : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := Closed.monoidalClosed d
    component ((MonoidalClosed.pre f).app Y) c ≫ Closed.π d F' Y c j =
      Closed.π d F Y c j ≫ (MonoidalClosed.pre (component f j)).app
        (Y.toEnrichedFunctor.obj (j ⊗ c)) :=
  Closed.closedPre_π d f Y c j

omit [HasColimitsOfSize.{uI, uI} V] in
/-- Every complete original target arrow acts at the same original right tensor index. -/
theorem target_projection (F : EnrichedFunctorCat V I) {Y Y' : EnrichedFunctorCat V I}
    (g : Y ⟶ Y') (c j : I) :
    component ((Closed.rightFunctor d F).map g) c ≫ Closed.π d F Y' c j =
      Closed.π d F Y c j ≫ (ihom (F.toEnrichedFunctor.obj j)).map
        (component g (j ⊗ c)) :=
  Closed.rightMap_π d F g c j

omit [HasColimitsOfSize.{uI, uI} V] in
/-- Every full original parameter Hom acts by the genuine tensor Hom and composition. -/
theorem parameter_projection (F Y : EnrichedFunctorCat V I) (c c' j : I) :
    MonoidalClosed.uncurry ((Closed.rightObject d F Y).toEnrichedFunctor.map c c') ≫
        Closed.π d F Y c' j =
      (Closed.π d F Y c j ⊗ₘ Closed.parameterComponent d Y c c' j) ≫
        eComp V (F.toEnrichedFunctor.obj j) (Y.toEnrichedFunctor.obj (j ⊗ c))
          (Y.toEnrichedFunctor.obj (j ⊗ c')) :=
  Closed.rightObject_map_π d F Y c c' j

/-- The original composite unit is detected by every actual source point. -/
theorem unit_projection (F G : EnrichedFunctorCat V I) (c j : I) :
    component ((Closed.adjunction d F).unit.app G) c ≫
        Closed.π d F (Closed.tensorObject d F G) c j =
      MonoidalClosed.curry (Generators.point d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) :=
  Closed.adjunction_unit_π d F G c j

/-- The entire original composite counit retains its whole output weight. -/
theorem counit_generator (F Y : EnrichedFunctorCat V I) (k : I) (p : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F.toEnrichedFunctor
        (Closed.rightObject d F Y).toEnrichedFunctor k p ≫
        component ((Closed.adjunction d F).counit.app Y) k =
      (𝟙 ((p.1 ⊗ p.2) ⟶[V] k) ⊗ₘ MonoidalClosed.uncurry (Closed.π d F Y p.2 p.1)) ≫
        (β_ ((p.1 ⊗ p.2) ⟶[V] k) (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k) :=
  Closed.adjunction_counit_gen d F Y k p

/-- Complete original tensor maps are recovered by the actual composite Hom functions. -/
example (F G Y : EnrichedFunctorCat V I) (f : Closed.tensorObject d F G ⟶ Y) :
    Closed.untranspose d F G Y (Closed.transpose d F G Y f) = f :=
  Closed.untranspose_transpose d F G Y f

/-- Complete original maps into the whole translated end are recovered. -/
example (F G Y : EnrichedFunctorCat V I) (g : G ⟶ Closed.rightObject d F Y) :
    Closed.transpose d F G Y (Closed.untranspose d F G Y g) = g :=
  Closed.transpose_untranspose d F G Y g

end CategoryTheory.EnrichedDayKernel.ClosedTests
