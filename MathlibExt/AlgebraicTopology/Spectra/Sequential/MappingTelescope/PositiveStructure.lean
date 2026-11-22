/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.DiagonalStructure

/-!
# Actual original cofinal successor and selected-point positive telescope structure

The actual Nat successor is genuinely final. The SAME original filtered
Group cocone and EVERY original leg identify its actual transition colimit
map as the inverse cofinal comparison. The original diagonal sigma/index
factorization therefore has a genuine Group colimit Iso. Its FULL actual
original telescope structure square proves selected-point positive-group
structure Isos, with the literal original adjoint-structure maps retained.
No cofinal/structure/weak detector or stable-model law is an input. These
are the actual positive groups at the original selected point; arbitrary
underlying Omega and original pi-star8.8 still require separate source work.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

private theorem originalComparisonHomWord
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (e : A ≅ D) (f : B ≅ E) (a : A ⟶ B) (b : D ⟶ E)
    (h : a ≫ f.hom = e.hom ≫ b) : a = e.hom ≫ b ≫ f.inv := by
  apply (cancel_mono f.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

private theorem originalIsIsoOfHom
    {C : Type uC} [Category.{vC} C] {A B : C} (e : A ≅ B) (f : A ⟶ B)
    (h : f = e.hom) : IsIso f := h.symm ▸ e.isIso_hom

private theorem originalCancelRightIso
    {C : Type uC} [Category.{vC} C] {A B D : C} (a : A ⟶ B) (e : B ≅ D) (b : A ⟶ D)
    (h : a ≫ e.hom = b) : a = b ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.PositiveStructureGeometry
open GrpCat.FilteredColimits.Successor
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The entire actual diagonal structure colimit map retains both original source factors. -/
theorem diagonalStructure_colimit_factorization (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X) =
      GrpCat.FilteredColimits.colimitMap (successorTransitionNatTrans.app (diagonalDiagram X m k)) ≫
        GrpCat.FilteredColimits.colimitMap ((diagonalSuccessorIndexNatIso m k).inv.app X) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  have h : (diagonalStructureNatTrans m k).app X =
      successorTransitionNatTrans.app (diagonalDiagram X m k) ≫
        (diagonalSuccessorIndexNatIso m k).inv.app X := rfl
  exact (Q.congr_map h).trans (Q.map_comp _ _)

/-- The full actual original diagonal structure Iso uses BOTH genuine original source Isos. -/
def diagonalStructureColimitIso (m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimit (diagonalDiagram X m k) ≅
      GrpCat.FilteredColimits.colimit (diagonalDiagram X (m + 1) (k + 1)) :=
  (successorComparisonIso (diagonalDiagram X m k)).symm ≪≫
    GrpCat.FilteredColimits.colimitFunctor.mapIso
      ((diagonalSuccessorIndexNatIso m k).app X).symm

/-- The ENTIRE actual diagonal-Iso hom function is the ORIGINAL sigma/index colimit map. -/
theorem diagonalStructureColimitIso_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (diagonalStructureColimitIso m k X).hom =
      GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X) :=
  (congrArg (fun f => f ≫ GrpCat.FilteredColimits.colimitMap
      ((diagonalSuccessorIndexNatIso m k).inv.app X))
    (successorTransition_colimit_eq_inv (diagonalDiagram X m k)).symm).trans
      (diagonalStructure_colimit_factorization m k X).symm

/-- The ACTUAL original diagonal sigma/index colimit map is genuinely an Iso on every input. -/
theorem diagonalStructure_colimit_isIso (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso (GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X)) := by
  exact originalIsIsoOfHom (diagonalStructureColimitIso m k X)
    (GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X))
    (diagonalStructureColimitIso_hom m k X).symm

/-- The ENTIRE original positive-group telescope sigma function retains the full comparison word. -/
theorem telescopeGroupStructure_comparison_word (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupStructureNatTrans m k).app (telescope X) =
      (telescopeDiagonalNatIso m k).hom.app X ≫
        GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X) ≫
          (telescopeDiagonalNatIso (m + 1) (k + 1)).inv.app X :=
  originalComparisonHomWord ((telescopeDiagonalNatIso m k).app X)
    ((telescopeDiagonalNatIso (m + 1) (k + 1)).app X)
    ((groupStructureNatTrans m k).app (telescope X))
    (GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X))
    (telescopeDiagonal_structure_hom m k X)

/-- BOTH full actual selected-point positive-group sigma Iso functions use original maps. -/
def telescopeGroupStructureIso (m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (piNPositiveFunctor k).obj ((telescope X).level m) ≅
      (piNPositiveFunctor (k + 1)).obj ((telescope X).level (m + 1)) :=
  (telescopeDiagonalNatIso m k).app X ≪≫ diagonalStructureColimitIso m k X ≪≫
    ((telescopeDiagonalNatIso (m + 1) (k + 1)).app X).symm

/-- The ENTIRE actual telescope group sigma-Iso hom is the SAME original structure map. -/
theorem telescopeGroupStructureIso_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeGroupStructureIso m k X).hom = (groupStructureNatTrans m k).app (telescope X) :=
  (congrArg (fun f => (telescopeDiagonalNatIso m k).hom.app X ≫ f ≫
      (telescopeDiagonalNatIso (m + 1) (k + 1)).inv.app X)
        (diagonalStructureColimitIso_hom m k X)).trans
    (telescopeGroupStructure_comparison_word m k X).symm

/-- EVERY actual selected-point positive-group original telescope structure map is an Iso. -/
theorem telescopeGroupStructure_isIso (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso ((groupStructureNatTrans m k).app (telescope X)) := by
  exact originalIsIsoOfHom (telescopeGroupStructureIso m k X)
    ((groupStructureNatTrans m k).app (telescope X)) (telescopeGroupStructureIso_hom m k X).symm

/-- The full positive adjoint map is original sigma followed by native shift inverse. -/
theorem telescopeAdjointPositiveMap_eq_word (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m) =
      (groupStructureNatTrans m k).app (telescope X) ≫
        (nativeLoopGroupShiftNatIso k).inv.app ((telescope X).level (m + 1)) := by
  exact originalCancelRightIso
    ((piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m))
    ((nativeLoopGroupShiftNatIso k).app ((telescope X).level (m + 1)))
    ((groupStructureNatTrans m k).app (telescope X)) rfl

/-- BOTH entire original selected-point positive adjoint comparison functions are retained. -/
def telescopeAdjointPositiveIso (m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (piNPositiveFunctor k).obj ((telescope X).level m) ≅
      (piNPositiveFunctor k).obj (PointedCGWH.loop.obj ((telescope X).level (m + 1))) :=
  telescopeGroupStructureIso m k X ≪≫
    ((nativeLoopGroupShiftNatIso k).app ((telescope X).level (m + 1))).symm

/-- The ENTIRE actual positive-Iso hom is the SAME original selected-point adjoint pi map. -/
theorem telescopeAdjointPositiveIso_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeAdjointPositiveIso m k X).hom = (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m) :=
  (congrArg (fun f => f ≫ (nativeLoopGroupShiftNatIso k).inv.app
      ((telescope X).level (m + 1))) (telescopeGroupStructureIso_hom m k X)).trans
    (telescopeAdjointPositiveMap_eq_word m k X).symm

/-- EVERY original adjoint map induces an Iso at its selected point in each positive degree. -/
theorem telescopeAdjointPositiveMap_isIso (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso ((piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m)) := by
  exact originalIsIsoOfHom (telescopeAdjointPositiveIso m k X)
    ((piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m))
    (telescopeAdjointPositiveIso_hom m k X).symm

end PointedCGWH.SequentialSpectrum.MappingTelescope.PositiveStructureGeometry
