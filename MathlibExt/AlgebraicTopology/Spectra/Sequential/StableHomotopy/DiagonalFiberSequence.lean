/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.LoopedGroupComparison
import MathlibExt.Algebra.Category.Grp.ExactnessTransport

/-!
# The original diagonal fiber connecting map and all three exact pairs

The strictly natural fixed-degree looped Serre connecting maps are
transported by the actual whole iteration/cube/diagonal comparisons. Both
original projection maps remain the literal maps of the original diagonal
quotients. The connecting map retains every original comparison function
instead of suppressing the loop-coordinate permutations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory


namespace PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams (zeroTo)
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupComparison

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
  (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (m k : ℕ)

/-- Both total diagram comparison maps are the same original diagonal/iteration/cube maps. -/
def diagonalTotalGroupNatIso :
    diagonalDiagram X m k ≅ loopedTotalGroupDiagram p hp m k :=
  ((iterationDiagonalNatIso m k).app X).symm ≪≫ loopedTotalGroupNatIso p hp m k

/-- Both base diagram comparison maps are the same original diagonal/iteration/cube maps. -/
def diagonalBaseGroupNatIso :
    diagonalDiagram Y m k ≅ loopedBaseGroupDiagram p hp m k :=
  ((iterationDiagonalNatIso m k).app Y).symm ≪≫ loopedBaseGroupNatIso p hp m k

/-- Both full fiber diagram maps preserve the original chosen fiber and every loop comparison. -/
def diagonalFiberGroupNatIso :
    diagonalDiagram c.pt m k ≅ loopedFiberGroupDiagram p hp m k :=
  ((iterationDiagonalNatIso m k).app c.pt).symm ≪≫ loopedFiberGroupNatIso p hp m k c hc

/-- The unchanged original projection retains the whole diagonal comparison square. -/
theorem diagonalProjectionGroup_square :
    (diagonalDiagramFunctor m k).map p ≫ (diagonalBaseGroupNatIso p hp m k).hom =
      (diagonalTotalGroupNatIso p hp m k).hom ≫ loopedProjectionGroupMap p hp m k := by
  change (diagonalDiagramFunctor m k).map p ≫
      ((iterationDiagonalNatIso m k).inv.app Y ≫ (loopedBaseGroupNatIso p hp m k).hom) =
    ((iterationDiagonalNatIso m k).inv.app X ≫ (loopedTotalGroupNatIso p hp m k).hom) ≫ _
  rw [← Category.assoc, (iterationDiagonalNatIso m k).inv.naturality p,
    Category.assoc, loopedProjectionGroup_square p hp m k, ← Category.assoc]

/-- The unchanged original chosen-fiber inclusion retains the whole diagonal comparison square. -/
theorem diagonalInclusionGroup_square :
    (diagonalDiagramFunctor m k).map c.fst ≫ (diagonalTotalGroupNatIso p hp m k).hom =
      (diagonalFiberGroupNatIso p c hc hp m k).hom ≫ loopedInclusionGroupMap p hp m k := by
  change (diagonalDiagramFunctor m k).map c.fst ≫
      ((iterationDiagonalNatIso m k).inv.app X ≫ (loopedTotalGroupNatIso p hp m k).hom) =
    ((iterationDiagonalNatIso m k).inv.app c.pt ≫
      (loopedFiberGroupNatIso p hp m k c hc).hom) ≫ _
  rw [← Category.assoc, (iterationDiagonalNatIso m k).inv.naturality c.fst,
    Category.assoc, loopedInclusionGroup_square p hp m k c hc, ← Category.assoc]

/-- The actual group quotient functor retains both full original total comparison functions. -/
def diagonalTotalColimitIso :
    GrpCat.FilteredColimits.colimit (diagonalDiagram X m k) ≅
      GrpCat.FilteredColimits.colimit (loopedTotalGroupDiagram p hp m k) :=
  GrpCat.FilteredColimits.colimitFunctor.mapIso (diagonalTotalGroupNatIso p hp m k)

/-- The actual group quotient functor retains both full original base comparison functions. -/
def diagonalBaseColimitIso :
    GrpCat.FilteredColimits.colimit (diagonalDiagram Y m k) ≅
      GrpCat.FilteredColimits.colimit (loopedBaseGroupDiagram p hp m k) :=
  GrpCat.FilteredColimits.colimitFunctor.mapIso (diagonalBaseGroupNatIso p hp m k)

/-- The actual group quotient functor retains both full original
chosen-fiber comparison functions. -/
def diagonalFiberColimitIso :
    GrpCat.FilteredColimits.colimit (diagonalDiagram c.pt m k) ≅
      GrpCat.FilteredColimits.colimit (loopedFiberGroupDiagram p hp m k) :=
  GrpCat.FilteredColimits.colimitFunctor.mapIso (diagonalFiberGroupNatIso p c hc hp m k)

/-- Both original projection quotient maps retain the full original comparison square. -/
theorem diagonalProjectionColimit_square :
    GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map p) ≫
        (diagonalBaseColimitIso p hp m k).hom =
      (diagonalTotalColimitIso p hp m k).hom ≫
        GrpCat.FilteredColimits.colimitMap (loopedProjectionGroupMap p hp m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalProjectionGroup_square p hp m k)).trans (Q.map_comp _ _))

/-- Both original inclusion quotient maps retain the same original
chosen-fiber comparison square. -/
theorem diagonalInclusionColimit_square :
    GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map c.fst) ≫
        (diagonalTotalColimitIso p hp m k).hom =
      (diagonalFiberColimitIso p c hc hp m k).hom ≫
        GrpCat.FilteredColimits.colimitMap (loopedInclusionGroupMap p hp m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalInclusionGroup_square p c hc hp m k)).trans (Q.map_comp _ _))

/-- The actual original diagonal connecting map retains all looped comparison and quotient maps. -/
def diagonalConnectingMap :
    GrpCat.FilteredColimits.colimit (diagonalDiagram Y m (k + 1)) ⟶
      GrpCat.FilteredColimits.colimit (diagonalDiagram c.pt m k) :=
  (diagonalBaseColimitIso p hp m (k + 1)).hom ≫
    GrpCat.FilteredColimits.colimitMap (loopedConnectingGroupMap p hp m k) ≫
      (diagonalFiberColimitIso p c hc hp m k).inv

/-- The whole diagonal connecting function reconstructs the same original
looped quotient function. -/
theorem diagonalConnectingMap_reconstruction :
    diagonalConnectingMap p c hc hp m k ≫ (diagonalFiberColimitIso p c hc hp m k).hom =
      (diagonalBaseColimitIso p hp m (k + 1)).hom ≫
        GrpCat.FilteredColimits.colimitMap (loopedConnectingGroupMap p hp m k) := by
  rw [diagonalConnectingMap, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Every original connecting quotient leg retains the actual looped stage connecting function. -/
theorem diagonalConnectingMap_leg (n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (diagonalDiagram Y m (k + 1))).ι.app n ≫
        diagonalConnectingMap p c hc hp m k =
      (diagonalBaseGroupNatIso p hp m (k + 1)).hom.app n ≫
        (loopedConnectingGroupMap p hp m k).app n ≫
          (GrpCat.FilteredColimits.colimitCocone (loopedFiberGroupDiagram p hp m k)).ι.app n ≫
            (diagonalFiberColimitIso p c hc hp m k).inv := by
  let e := (diagonalBaseGroupNatIso p hp m (k + 1)).hom
  let d := loopedConnectingGroupMap p hp m k
  have he := GrpCat.FilteredColimits.colimitMap_ι e n
  have hd := GrpCat.FilteredColimits.colimitMap_ι d n
  change _ ≫ (GrpCat.FilteredColimits.colimitMap e ≫
      GrpCat.FilteredColimits.colimitMap d ≫ (diagonalFiberColimitIso p c hc hp m k).inv) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc
    ((GrpCat.FilteredColimits.colimitCocone (loopedBaseGroupDiagram p hp m (k + 1))).ι.app n),
    hd, Category.assoc]

include hc hp in
/-- Every same original positive diagonal fiber sequence is exact at its total group quotient. -/
theorem diagonal_exact_at_total :
    Function.MulExact
      (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map c.fst)).hom
      (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map p)).hom :=
  GrpCat.mulExact_of_iso_ladder (diagonalFiberColimitIso p c hc hp m k)
    (diagonalTotalColimitIso p hp m k) (diagonalBaseColimitIso p hp m k) _ _ _ _
    (diagonalInclusionColimit_square p c hc hp m k)
    (diagonalProjectionColimit_square p hp m k) (loopedColimit_exact_at_total p hp m k)

/-- The actual connecting map is exact at every original positive diagonal fiber quotient. -/
theorem diagonal_exact_at_fiber :
    Function.MulExact (diagonalConnectingMap p c hc hp m k).hom
      (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map c.fst)).hom :=
  GrpCat.mulExact_of_iso_ladder (diagonalBaseColimitIso p hp m (k + 1))
    (diagonalFiberColimitIso p c hc hp m k) (diagonalTotalColimitIso p hp m k) _ _ _ _
    (diagonalConnectingMap_reconstruction p c hc hp m k)
    (diagonalInclusionColimit_square p c hc hp m k) (loopedColimit_exact_at_fiber p hp m k)

/-- The actual connecting map is exact at every original next-degree diagonal base quotient. -/
theorem diagonal_exact_at_base :
    Function.MulExact
      (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m (k + 1)).map p)).hom
      (diagonalConnectingMap p c hc hp m k).hom :=
  GrpCat.mulExact_of_iso_ladder (diagonalTotalColimitIso p hp m (k + 1))
    (diagonalBaseColimitIso p hp m (k + 1)) (diagonalFiberColimitIso p c hc hp m k) _ _ _ _
    (diagonalProjectionColimit_square p hp m (k + 1))
    (diagonalConnectingMap_reconstruction p c hc hp m k) (loopedColimit_exact_at_base p hp m k)

end PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence
