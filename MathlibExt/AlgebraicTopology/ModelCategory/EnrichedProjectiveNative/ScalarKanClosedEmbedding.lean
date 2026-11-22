/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.LeftKanTensor
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.HomotopyExtensionClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHTensorClosedEmbedding
import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds

/-!
# Original coefficient boundaries after actual scalar Kan extension

The original enriched Kan tensor comparison identifies the whole coefficient
arrow with scalar tensor of the same boundary and the actual Kan object.
At each original evaluation this is the original pointed boundary tensored
with an arbitrary pointed object, whose underlying arrow is a closed embedding.
Both isomorphism components and their scalar naturality are retained.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uA uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open Topology
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.ScalarKanClosedEmbedding

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

variable {D : Type uD} [EnrichedCategory PointedCGWH.{u, v} D]

/-- The actual closed-embedding class measured by one original native evaluation. -/
def evaluatedClosed (d : D) : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} D) :=
  TopCat.closedEmbeddings.inverseImage
    (evaluation (V := PointedCGWH.{u, v}) d ⋙ PointedCGWH.pointedToCGWH ⋙ CGWH.cgwhToTop)

instance evaluatedClosed_respectsIso (d : D) : (evaluatedClosed d).RespectsIso := by
  dsimp [evaluatedClosed]
  infer_instance

/-- Membership retains the exact original evaluated continuous map. -/
theorem evaluatedClosed_iff {X Y : EnrichedFunctorCat PointedCGWH.{u, v} D} (f : X ⟶ Y) (d : D) :
    evaluatedClosed d f ↔ IsClosedEmbedding (ConcreteCategory.hom (component f d).right) := Iff.rfl

/-- The whole original Arrow comparison preserves the same evaluated closed class. -/
theorem evaluatedClosed_ofArrowIso {X Y X' Y' : EnrichedFunctorCat PointedCGWH.{u, v} D}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g) (d : D)
    (hg : evaluatedClosed d g) : evaluatedClosed d f :=
  ((evaluatedClosed d).arrow_mk_iso_iff e).mpr hg

variable {A : Type uA} [EnrichedCategory PointedCGWH.{u, v} A]
  (j : EnrichedFunctor PointedCGWH.{u, v} A D)
  [∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (d : D),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j d) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (d : D),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j d) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (d : D),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j d) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j d) X.toEnrichedFunctor)]

/-- The full original Kan coefficient arrow is isomorphic to the original scalar tensor arrow. -/
def coefficientArrowIso {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Arrow.mk ((leftKan j).map (scalarTensorMap i Y)) ≅
      Arrow.mk (scalarTensorMap i ((leftKan j).obj Y)) :=
  Arrow.isoMk (leftKanTensorIso j K Y) (leftKanTensorIso j L Y)
    (leftKanTensorHom_scalar_naturality j i Y).symm

/-- Every original realized boundary has a closed embedding after scalar Kan extension at every evaluation. -/
theorem originalBoundary_component_isClosedEmbedding {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : PointedCGWH.realizedBoundaryInclusions i)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} A) (d : D) :
    IsClosedEmbedding (ConcreteCategory.hom
      (component ((leftKan j).map (scalarTensorMap i Y)) d).right) := by
  let : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).mpr
    (PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.boundaryMap_modelCofibration i hi)
  have ht : evaluatedClosed d (scalarTensorMap i ((leftKan j).obj Y)) := by
    apply (evaluatedClosed_iff _ d).mpr
    rw [scalarTensorMap_component]
    exact PointedCGWH.modelCofibration_whiskerRight_isClosedEmbedding i _
  exact (evaluatedClosed_iff _ d).mp (evaluatedClosed_ofArrowIso (coefficientArrowIso j i Y) d ht)

/-- The complete original Kan boundary belongs to the same actual evaluated closed class. -/
theorem originalBoundary_mem_evaluatedClosed {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : PointedCGWH.realizedBoundaryInclusions i)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} A) (d : D) :
    evaluatedClosed d ((leftKan j).map (scalarTensorMap i Y)) :=
  (evaluatedClosed_iff _ d).mpr (originalBoundary_component_isClosedEmbedding j i hi Y d)

end HomotopicalAlgebra.EnrichedProjective.Native.ScalarKanClosedEmbedding
