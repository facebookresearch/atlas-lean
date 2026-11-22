/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.PositiveStructure
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Association

/-!
# The full original R-input prefix and original diagonal unit square

The actual prefix equality of the SAME original iterates constructs an
Iso of the entire original iteration diagrams, including all finite
index maps and spectrum input maps. Its evaluated positive-group Iso
is joined to the ONE original changing-level and changing-degree
diagonal. The actual original R-unit map followed by this comparison
is proved equal to the SAME diagonal successor transition. Both full
comparison directions and every actual component function are retained.
No prefix, diagonal, unit, stable-pi or model-category law is an input.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC uD vD
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

private theorem originalUnitConjugation
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (i : A ≅ B) (j : D ≅ E) (k : F ≅ G)
    (a : B ⟶ E) (b : A ⟶ D) (p : D ⟶ F) (c : A ⟶ F) (t : B ⟶ G)
    (hNatural : a ≫ j.inv = i.inv ≫ b) (hUnit : b ≫ p = c)
    (hTransition : c ≫ k.hom = i.hom ≫ t) :
    a ≫ j.inv ≫ p ≫ k.hom = t := by
  simp only [← Category.assoc]
  rw [hNatural]
  simp only [Category.assoc]
  rw [← Category.assoc b p k.hom, hUnit, hTransition]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem originalNatUnitConjugation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    (R : C ⥤ C) (F G : C ⥤ D) (S : D ⥤ D) (u : 𝟭 C ⟶ R)
    (e : F ≅ G) (p : R ⋙ F ≅ F ⋙ S) (t : 𝟭 D ⟶ S)
    (h : Functor.whiskerRight u F ≫ p.hom = Functor.whiskerLeft F t) :
    Functor.whiskerRight u G ≫
        ((Functor.isoWhiskerLeft R e).symm ≪≫ p ≪≫
          Functor.isoWhiskerRight e S).hom = Functor.whiskerLeft G t := by
  apply NatTrans.ext
  funext X
  have hn : G.map (u.app X) ≫ e.inv.app (R.obj X) =
      e.inv.app X ≫ F.map (u.app X) := e.inv.naturality (u.app X)
  have hu : F.map (u.app X) ≫ p.hom.app X = t.app (F.obj X) := congr_app h X
  have ht : t.app (F.obj X) ≫ S.map (e.hom.app X) =
      e.hom.app X ≫ t.app (G.obj X) := (t.naturality (e.hom.app X)).symm
  exact originalUnitConjugation (e.app X) (e.app (R.obj X)) (S.mapIso (e.app X))
    (G.map (u.app X)) (F.map (u.app X)) (p.hom.app X) (t.app (F.obj X))
    (t.app (G.obj X)) hn hu ht

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.RUnitDiagonalGeometry
open GrpCat.FilteredColimits.Successor
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The entire next prefix inverse is the SAME original R-map of the preceding inverse. -/
theorem iteratePrefixNatIso_inv_succ (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iteratePrefixNatIso (n + 1)).inv.app X =
      functor.map ((iteratePrefixNatIso n).inv.app X) := by
  rw [iteratePrefixNatIso_inv_app, iteratePrefixNatIso_inv_app, eqToHom_map]
  rfl

/-- The SAME original successor acts on the full original spectrum diagrams. -/
def spectrumSuccessorDiagramFunctor :
    (ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) ⥤
      (ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) :=
  (Functor.whiskeringLeft ℕ ℕ PointedCGWH.SequentialSpectrum.{u, v}).obj successorFunctor

/-- Every actual prefix inverse respects the original successive unit transitions. -/
theorem iteratePrefix_inv_transition (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterateUnit n).app (functor.obj X) ≫ (iteratePrefixNatIso (n + 1)).inv.app X =
      (iteratePrefixNatIso n).inv.app X ≫ (iterateUnit (n + 1)).app X := by
  rw [iterateUnit_app, iterateUnit_app, iteratePrefixNatIso_inv_succ]
  exact (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.naturality
    ((iteratePrefixNatIso n).inv.app X)).symm

/-- The full original R-input iteration diagram maps by the exact original prefix inverse. -/
def iterationPrefixDiagramNatTrans : functor.{u, v} ⋙ iterationDiagramFunctor ⟶
    iterationDiagramFunctor ⋙ spectrumSuccessorDiagramFunctor where
  app X := NatTrans.ofSequence (fun n => (iteratePrefixNatIso n).inv.app X)
    (fun n => by
      have hs : ((functor ⋙ iterationDiagramFunctor).obj X).map
          (homOfLE (Nat.le_succ n)) = (iterateUnit n).app (functor.obj X) :=
        iterationDiagram_map_succ (functor.obj X) n
      have ht : ((iterationDiagramFunctor ⋙ spectrumSuccessorDiagramFunctor).obj X).map
          (homOfLE (Nat.le_succ n)) = (iterateUnit (n + 1)).app X :=
        iterationDiagram_map_succ X (n + 1)
      exact (congrArg (fun f => f ≫ (iteratePrefixNatIso (n + 1)).inv.app X) hs).trans
        ((iteratePrefix_inv_transition n X).trans
          (congrArg (fun f => (iteratePrefixNatIso n).inv.app X ≫ f) ht.symm)))
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (iteratePrefixNatIso n).inv.naturality f

/-- Both full original spectrum prefix maps form the actual whole iteration-diagram Iso. -/
def iterationPrefixDiagramNatIso : functor.{u, v} ⋙ iterationDiagramFunctor ≅
    iterationDiagramFunctor ⋙ spectrumSuccessorDiagramFunctor :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => ((iteratePrefixNatIso n).app X).symm)
    (fun f => (iterationPrefixDiagramNatTrans.app X).naturality f))
    (fun f => by
      apply NatTrans.ext
      funext n
      exact (iteratePrefixNatIso n).inv.naturality f)

/-- The entire diagram-Iso hom is the SAME genuine original prefix NatTrans. -/
theorem iterationPrefixDiagramNatIso_hom :
    iterationPrefixDiagramNatIso.{u, v}.hom = iterationPrefixDiagramNatTrans := rfl

/-- Every full forward prefix component retains the actual original inverse equality map. -/
theorem iterationPrefixDiagramNatIso_hom_app_app
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (iterationPrefixDiagramNatIso.hom.app X).app n =
      (iteratePrefixNatIso n).inv.app X := rfl

/-- Every full inverse prefix component retains the actual original forward equality map. -/
theorem iterationPrefixDiagramNatIso_inv_app_app
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (iterationPrefixDiagramNatIso.inv.app X).app n =
      (iteratePrefixNatIso n).hom.app X := rfl

/-- ALL actual original finite index maps retain the complete forward prefix square. -/
theorem iterationPrefixDiagramNatIso_hom_index_naturality
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    (iterationDiagram (functor.obj X)).map f ≫ (iteratePrefixNatIso j).inv.app X =
      (iteratePrefixNatIso i).inv.app X ≫
        (iterationDiagram X).map (successorFunctor.map f) :=
  (iterationPrefixDiagramNatIso.hom.app X).naturality f

/-- ALL actual original finite index maps retain the complete inverse prefix square. -/
theorem iterationPrefixDiagramNatIso_inv_index_naturality
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    (iterationDiagram X).map (successorFunctor.map f) ≫ (iteratePrefixNatIso j).hom.app X =
      (iteratePrefixNatIso i).hom.app X ≫ (iterationDiagram (functor.obj X)).map f :=
  (iterationPrefixDiagramNatIso.inv.app X).naturality f

/-- Genuine original evaluation and positive homotopy functors act on the complete diagrams. -/
def spectrumGroupDiagramFunctor (m k : ℕ) :
    (ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) ⥤ (ℕ ⥤ GrpCat.{v}) :=
  (Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
    PointedCGWH.{u, v}).obj (PointedCGWH.SequentialSpectrum.evaluation m) ⋙
      (Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (piNPositiveFunctor k)

/-- The whole positive-group prefix Iso is the actual evaluation of the SAME spectrum Iso. -/
def groupIterationPrefixNatIso (m k : ℕ) :
    functor.{u, v} ⋙ groupIterationDiagramFunctor m k ≅
      shiftedGroupIterationDiagramFunctor m k :=
  Functor.isoWhiskerRight iterationPrefixDiagramNatIso (spectrumGroupDiagramFunctor m k)

/-- Every entire positive-group prefix hom is the original pi map of the actual prefix inverse. -/
theorem groupIterationPrefixNatIso_hom_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((groupIterationPrefixNatIso m k).hom.app X).app n = (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((iteratePrefixNatIso n).inv.app X) m) := rfl

/-- Every entire positive-group prefix inv is the original pi map of the actual prefix hom. -/
theorem groupIterationPrefixNatIso_inv_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((groupIterationPrefixNatIso m k).inv.app X).app n = (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((iteratePrefixNatIso n).hom.app X) m) := rfl

/-- Both actual R-input diagonal comparison directions use the SAME original three Isos. -/
def rInputDiagonalNatIso (m k : ℕ) : functor.{u, v} ⋙ diagonalDiagramFunctor m k ≅
    diagonalDiagramFunctor m k ⋙ successorDiagramFunctor :=
  (Functor.isoWhiskerLeft functor (iterationDiagonalNatIso m k)).symm ≪≫
    groupIterationPrefixNatIso m k ≪≫
      Functor.isoWhiskerRight (iterationDiagonalNatIso m k) successorDiagramFunctor

/-- EVERY full R-input diagonal hom retains the original G inverse, prefix map and next G hom. -/
theorem rInputDiagonalNatIso_hom_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((rInputDiagonalNatIso m k).hom.app X).app n =
      (iterationGroupEvaluationNatIso n m k).inv.app (functor.obj X) ≫
        (piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((iteratePrefixNatIso n).inv.app X) m) ≫
            (iterationGroupEvaluationNatIso (n + 1) m k).hom.app X := rfl

/-- EVERY full R-input diagonal inv retains the original next G inverse, prefix hom and G hom. -/
theorem rInputDiagonalNatIso_inv_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((rInputDiagonalNatIso m k).inv.app X).app n =
      (iterationGroupEvaluationNatIso (n + 1) m k).inv.app X ≫
        (piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((iteratePrefixNatIso n).hom.app X) m) ≫
            (iterationGroupEvaluationNatIso n m k).hom.app (functor.obj X) := rfl

/-- The original R unit acts on the ONE complete original diagonal, at every original input. -/
def diagonalInputUnitNatTrans (m k : ℕ) : diagonalDiagramFunctor.{u, v} m k ⟶
    functor ⋙ diagonalDiagramFunctor m k :=
  Functor.whiskerRight PointedCGWH.SequentialSpectrum.OrderedLoop.unit
    (diagonalDiagramFunctor m k)

/-- Every ENTIRE original diagonal unit component is the actual positive homotopy unit map. -/
theorem diagonalInputUnitNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalInputUnitNatTrans m k).app X).app n = (piNPositiveFunctor (k + n)).map
      (PointedCGWH.SequentialSpectrum.levelMap
        (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X) (m + n)) := rfl

/-- The actual evaluated original input unit and prefix give the SAME full successor map. -/
theorem groupIterationPrefix_unit_transition_whole (m k : ℕ) :
    Functor.whiskerRight PointedCGWH.SequentialSpectrum.OrderedLoop.unit
        (groupIterationDiagramFunctor.{u, v} m k) ≫ (groupIterationPrefixNatIso m k).hom =
      Functor.whiskerLeft (groupIterationDiagramFunctor m k) successorTransitionNatTrans := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m ⋙ piNPositiveFunctor k
  have hp : (iterate n).map (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X) ≫
      (iteratePrefixNatIso n).inv.app X = (iterateUnit n).app X := by
    rw [iteratePrefixNatIso_inv_app, iterate_map_unit_prefix_cast, iterateUnit_app]
  have hu : E.map ((iterate n).map (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X)) ≫
      E.map ((iteratePrefixNatIso n).inv.app X) = E.map ((iterateUnit n).app X) :=
    (E.map_comp _ _).symm.trans (E.congr_map hp)
  have hs := groupIterationDiagram_map_succ X m k n
  have ht := successorTransitionNatTrans_app_app
    ((groupIterationDiagramFunctor m k).obj X) n
  exact hu.trans (hs.symm.trans ht.symm)

/-- The WHOLE original R-unit diagram square is the SAME entire diagonal successor transition. -/
theorem rInputDiagonal_unit_transition_whole (m k : ℕ) :
    diagonalInputUnitNatTrans.{u, v} m k ≫ (rInputDiagonalNatIso m k).hom =
      Functor.whiskerLeft (diagonalDiagramFunctor m k) successorTransitionNatTrans := by
  exact originalNatUnitConjugation functor (groupIterationDiagramFunctor m k)
    (diagonalDiagramFunctor m k) successorDiagramFunctor
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit
    (iterationDiagonalNatIso m k) (groupIterationPrefixNatIso m k)
    successorTransitionNatTrans (groupIterationPrefix_unit_transition_whole m k)

/-- The full original R-unit/prefix comparison is EXACTLY the actual diagonal successor map. -/
theorem rInputDiagonal_unit_transition (m k n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ((diagonalInputUnitNatTrans m k).app X).app n ≫
        ((rInputDiagonalNatIso m k).hom.app X).app n =
      (diagonalTransition n m k).app X := by
  have h := congr_app (congr_app (rInputDiagonal_unit_transition_whole m k) X) n
  exact h.trans ((successorTransitionNatTrans_app_app (diagonalDiagram X m k) n).trans
    (diagonalDiagram_map_succ X m k n))

/-- The ENTIRE original R-unit map is the actual successor map then original comparison inverse. -/
theorem diagonalInputUnitNatTrans_eq_transition_inv (m k : ℕ) :
    diagonalInputUnitNatTrans.{u, v} m k =
      Functor.whiskerLeft (diagonalDiagramFunctor m k) successorTransitionNatTrans ≫
        (rInputDiagonalNatIso m k).inv := by
  apply (cancel_mono (rInputDiagonalNatIso m k).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact rInputDiagonal_unit_transition_whole m k

/-- Every original spectrum Arrow retains the ENTIRE forward R-input diagonal comparison. -/
theorem rInputDiagonalNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (diagonalDiagramFunctor m k).map (functor.map f) ≫ (rInputDiagonalNatIso m k).hom.app Y =
      (rInputDiagonalNatIso m k).hom.app X ≫
        successorDiagramFunctor.map ((diagonalDiagramFunctor m k).map f) :=
  (rInputDiagonalNatIso m k).hom.naturality f

/-- Every original spectrum Arrow retains the ENTIRE inverse R-input diagonal comparison. -/
theorem rInputDiagonalNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    successorDiagramFunctor.map ((diagonalDiagramFunctor m k).map f) ≫
        (rInputDiagonalNatIso m k).inv.app Y =
      (rInputDiagonalNatIso m k).inv.app X ≫ (diagonalDiagramFunctor m k).map (functor.map f) :=
  (rInputDiagonalNatIso m k).inv.naturality f

end PointedCGWH.SequentialSpectrum.MappingTelescope.RUnitDiagonalGeometry
