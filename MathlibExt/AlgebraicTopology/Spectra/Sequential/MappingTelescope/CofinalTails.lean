/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Filtered.NatTail
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.HomotopyStructureSquares
import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail

/-!
# Whole cofinal tails of the actual native spectrum diagonal

Every finite offset retains the original changing-degree diagonal, every
map and the full original group-colimit comparison in both directions.
All integer degree conventions and all input spectrum maps are preserved.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace GrpCat.FilteredColimits.OriginalNatTailGeometry
open CategoryTheory.NatTail (tailFunctor)
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The actual positive tail is a whisker of the SAME ONE original varying-degree diagram. -/
def diagonalTailDiagramFunctor (m k r : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ GrpCat.{v}) :=
  diagonalDiagramFunctor m k ⋙
    tailDiagramFunctor r

/-- EVERY tail object is the original group at the actual shifted degree and original level. -/
theorem diagonalTailDiagramFunctor_obj_obj (m k r : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalTailDiagramFunctor m k r).obj X).obj n =
      (PointedCGWH.piNPositiveFunctor (k + (r + n))).obj (X.level (m + (r + n))) := rfl

/-- EVERY original spectrum Arrow retains its entire original positive-tail component function. -/
theorem diagonalTailDiagramFunctor_map_app (m k r : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    ((diagonalTailDiagramFunctor m k r).map f).app n =
      (PointedCGWH.piNPositiveFunctor (k + (r + n))).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + (r + n))) := rfl

/-- EVERY actual tail finite map is the SAME original diagonal map on shifted original indexes. -/
theorem diagonalTailDiagramFunctor_obj_map (m k r : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    ((diagonalTailDiagramFunctor m k r).obj X).map f =
      (diagonalDiagram X m k).map
        ((tailFunctor r).map f) := rfl

/-- The WHOLE actual original diagonal tail has BOTH genuine original colimit comparison maps. -/
def diagonalTailColimitNatIso (m k r : ℕ) : diagonalTailDiagramFunctor.{u, v} m k r ⋙
    GrpCat.FilteredColimits.colimitFunctor ≅
      diagonalDiagramFunctor
        m k ⋙ GrpCat.FilteredColimits.colimitFunctor :=
  Functor.associator
      (diagonalDiagramFunctor
        m k) (tailDiagramFunctor r) GrpCat.FilteredColimits.colimitFunctor ≪≫
    Functor.isoWhiskerLeft
      (diagonalDiagramFunctor
        m k) (tailColimitNatIso r)

/-- ALL integer degrees remain literal homotopy-minus-level degrees in EVERY genuine tail. -/
theorem integerDiagonalTail_degree (q : ℤ) (r n : ℕ) :
    ((integerTailPositiveIndex
          q + (r + n) + 1 : ℕ) : ℤ) -
      ((integerTailLevel q +
          (r + n) : ℕ) : ℤ) = q :=
  integerTail_degree q (r + n)

/-- Every original integer stable-degree tail retains BOTH full same-diagonal colimit maps. -/
def integerDiagonalTailColimitNatIso (q : ℤ) (r : ℕ) :
    diagonalTailDiagramFunctor.{u, v}
        (integerTailLevel q)
        (integerTailPositiveIndex
          q) r ⋙ GrpCat.FilteredColimits.colimitFunctor ≅
      integerDiagonalDiagramFunctor
        q ⋙ GrpCat.FilteredColimits.colimitFunctor :=
  diagonalTailColimitNatIso
    (integerTailLevel q)
    (integerTailPositiveIndex q) r

end GrpCat.FilteredColimits.OriginalNatTailGeometry
