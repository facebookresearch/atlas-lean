/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Public colimit clients of the genuine Day closed adjunction

Every shape and every leg is retained. The canonical forward and inverse
colimit maps are supplied by the constructed adjunction and the original
Day braid, with no preservation hypothesis on either tensor functor.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uI vI w z

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.EnrichedDayKernel.ClosedColimitsTests

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  {J : Type z} [Category.{w} J]

/-- The original left Day tensor carries each complete chosen colimit to its colimit. -/
def leftTensorColimitIso (F : EnrichedFunctorCat V I) (K : J ⥤ EnrichedFunctorCat V I)
    [HasColimit K] [HasColimit (K ⋙ Closed.leftFunctor d F)] :
    (Closed.leftFunctor d F).obj (colimit K) ≅ colimit (K ⋙ Closed.leftFunctor d F) := by
  let : PreservesColimitsOfSize.{w, z} (Closed.leftFunctor d F) :=
    Closed.leftTensorPreserves d F
  exact preservesColimitIso (Closed.leftFunctor d F) K

/-- Every original colimit leg is retained by the complete forward left-tensor map. -/
@[reassoc]
theorem leftTensorColimitIso_hom (F : EnrichedFunctorCat V I)
    (K : J ⥤ EnrichedFunctorCat V I) [HasColimit K]
    [HasColimit (K ⋙ Closed.leftFunctor d F)] (j : J) :
    (Closed.leftFunctor d F).map (colimit.ι K j) ≫
        (leftTensorColimitIso d F K).hom = colimit.ι (K ⋙ Closed.leftFunctor d F) j := by
  let : PreservesColimitsOfSize.{w, z} (Closed.leftFunctor d F) :=
    Closed.leftTensorPreserves d F
  exact ι_preservesColimitIso_hom (Closed.leftFunctor d F) K j

/-- Every original colimit leg is retained by the complete inverse left-tensor map. -/
@[reassoc]
theorem leftTensorColimitIso_inv (F : EnrichedFunctorCat V I)
    (K : J ⥤ EnrichedFunctorCat V I) [HasColimit K]
    [HasColimit (K ⋙ Closed.leftFunctor d F)] (j : J) :
    colimit.ι (K ⋙ Closed.leftFunctor d F) j ≫
        (leftTensorColimitIso d F K).inv = (Closed.leftFunctor d F).map (colimit.ι K j) := by
  let : PreservesColimitsOfSize.{w, z} (Closed.leftFunctor d F) :=
    Closed.leftTensorPreserves d F
  exact ι_preservesColimitIso_inv (Closed.leftFunctor d F) K j

/-- Every complete cocone descent is retained by the original left-tensor inverse. -/
@[reassoc]
theorem leftTensorColimitIso_desc (F : EnrichedFunctorCat V I)
    (K : J ⥤ EnrichedFunctorCat V I) [HasColimit K]
    [HasColimit (K ⋙ Closed.leftFunctor d F)] (q : Cocone K) :
    (leftTensorColimitIso d F K).inv ≫
        (Closed.leftFunctor d F).map (colimit.desc K q) =
      colimit.desc (K ⋙ Closed.leftFunctor d F) ((Closed.leftFunctor d F).mapCocone q) := by
  let : PreservesColimitsOfSize.{w, z} (Closed.leftFunctor d F) :=
    Closed.leftTensorPreserves d F
  exact preservesColimitIso_inv_comp_desc (Closed.leftFunctor d F) K q

section Right

variable [SymmetricCategory I] (b : EnrichedBraidedMonoidalCategoryData V I d)

/-- The literal original right Day tensor functor, with its selected monoidal structure. -/
abbrev rightTensorFunctor (F : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I :=
  letI := ColimitMonoidal.monoidalCategory d
  tensorRight F

include b in
/-- The actual Day braid supplies the original right-tensor colimit isomorphism. -/
def rightTensorColimitIso (F : EnrichedFunctorCat V I) (K : J ⥤ EnrichedFunctorCat V I)
    [HasColimit K] [HasColimit (K ⋙ rightTensorFunctor d F)] :
    (rightTensorFunctor d F).obj (colimit K) ≅ colimit (K ⋙ rightTensorFunctor d F) := by
  let : PreservesColimitsOfSize.{w, z} (rightTensorFunctor d F) :=
    Closed.rightTensorPreserves d b F
  exact preservesColimitIso (rightTensorFunctor d F) K

/-- Every original leg is retained by the complete right-tensor forward map. -/
@[reassoc]
theorem rightTensorColimitIso_hom (F : EnrichedFunctorCat V I)
    (K : J ⥤ EnrichedFunctorCat V I) [HasColimit K]
    [HasColimit (K ⋙ rightTensorFunctor d F)] (j : J) :
    (rightTensorFunctor d F).map (colimit.ι K j) ≫
        (rightTensorColimitIso d b F K).hom = colimit.ι (K ⋙ rightTensorFunctor d F) j := by
  let : PreservesColimitsOfSize.{w, z} (rightTensorFunctor d F) :=
    Closed.rightTensorPreserves d b F
  exact ι_preservesColimitIso_hom (rightTensorFunctor d F) K j

/-- Every original leg is retained by the complete right-tensor inverse map. -/
@[reassoc]
theorem rightTensorColimitIso_inv (F : EnrichedFunctorCat V I)
    (K : J ⥤ EnrichedFunctorCat V I) [HasColimit K]
    [HasColimit (K ⋙ rightTensorFunctor d F)] (j : J) :
    colimit.ι (K ⋙ rightTensorFunctor d F) j ≫
        (rightTensorColimitIso d b F K).inv = (rightTensorFunctor d F).map (colimit.ι K j) := by
  let : PreservesColimitsOfSize.{w, z} (rightTensorFunctor d F) :=
    Closed.rightTensorPreserves d b F
  exact ι_preservesColimitIso_inv (rightTensorFunctor d F) K j

/-- Every complete original cocone is retained by the right-tensor inverse. -/
@[reassoc]
theorem rightTensorColimitIso_desc (F : EnrichedFunctorCat V I)
    (K : J ⥤ EnrichedFunctorCat V I) [HasColimit K]
    [HasColimit (K ⋙ rightTensorFunctor d F)] (q : Cocone K) :
    (rightTensorColimitIso d b F K).inv ≫
        (rightTensorFunctor d F).map (colimit.desc K q) =
      colimit.desc (K ⋙ rightTensorFunctor d F) ((rightTensorFunctor d F).mapCocone q) := by
  let : PreservesColimitsOfSize.{w, z} (rightTensorFunctor d F) :=
    Closed.rightTensorPreserves d b F
  exact preservesColimitIso_inv_comp_desc (rightTensorFunctor d F) K q

end Right

end CategoryTheory.EnrichedDayKernel.ClosedColimitsTests
