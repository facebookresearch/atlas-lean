/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.DiagonalHomotopy

/-!
# Full original successor group evaluation and native loop-shift tail association

The actual original evaluation and loop-power group-shift defining clauses
give the ENTIRE successor evaluation map as the SAME native loop-group
shift followed by the actual previous comparison. BOTH simultaneous
original level and group-degree index maps are retained. The whole Iso
and its inverse functions remain. The true original iterate-unit cross-n
square then identifies actual R structure maps with the original diagonal
sigma/index transition. No requested tail/structure law, alternative
evaluation, loop power, source Arrow or model dictionary is assumed.
The full diagonal finite-index tail diagram identification and stable8.8
remain separate subsequent work.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

private theorem originalLoopGroupTailWord
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P L : C ⥤ C) (Q Q' T : C ⥤ D) {A B E : C} {Z : D}
    (p : A ⟶ P.obj B) (j : B ⟶ E)
    (sA : Q.obj (L.obj A) ⟶ Q'.obj A)
    (sB : Q.obj (L.obj (P.obj B)) ⟶ Q'.obj (P.obj B))
    (sE : Q.obj (L.obj (P.obj E)) ⟶ Q'.obj (P.obj E))
    (hB : Q'.obj (P.obj B) ⟶ T.obj B) (hE : Q'.obj (P.obj E) ⟶ T.obj E)
    (d : T.obj E ⟶ Z)
    (h₁ : Q.map (L.map (P.map j)) ≫ sE = sB ≫ Q'.map (P.map j))
    (h₂ : Q.map (L.map p) ≫ sB = sA ≫ Q'.map p)
    (h₃ : Q'.map (P.map j) ≫ hE = hB ≫ T.map j) :
    Q.map (L.map (p ≫ P.map j)) ≫ sE ≫ hE ≫ d =
      sA ≫ (Q'.map p ≫ hB) ≫ (T.map j ≫ d) := by
  rw [L.map_comp, Q.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Q.map (L.map (P.map j))) sE (hE ≫ d), h₁]
  simp only [Category.assoc]
  rw [← Category.assoc (Q.map (L.map p)) sB (Q'.map (P.map j) ≫ hE ≫ d), h₂]
  simp only [Category.assoc]
  rw [← Category.assoc (Q'.map (P.map j)) hE d, h₃]
  simp only [Category.assoc]

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.GroupEvaluationTailGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open CategoryTheory.Spectra.Sequential (evaluation)
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The whole original tail level reindex retains the original evaluation functors. -/
def levelTailIndexNatIso (n m : ℕ) : CategoryTheory.Spectra.Sequential.evaluation
  PointedCGWH.sphereOne.{u, v} (m + 1 + n) ≅
    CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + (n + 1)) :=
  eqToIso (congrArg (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (show m
    + 1 + n = m + (n + 1) by omega))

/-- The whole original tail group-degree reindex retains the actual original pi functors. -/
def groupTailDegreeNatIso (n k : ℕ) : piNPositiveFunctor.{u, v} (k + 1 + n) ≅
    piNPositiveFunctor (k + (n + 1)) :=
  eqToIso (congrArg piNPositiveFunctor (show k + 1 + n = k + (n + 1) by omega))

/-- BOTH complete actual original tail arithmetic maps form the full target NatIso. -/
def groupTailIndexNatIso (n m k : ℕ) :
    CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} (m + 1 + n) ⋙
      piNPositiveFunctor (k + 1 + n) ≅
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + (n + 1)) ⋙
        piNPositiveFunctor (k + (n + 1)) :=
  Functor.isoWhiskerRight (levelTailIndexNatIso n m) (piNPositiveFunctor (k + 1 + n)) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m
      + (n + 1))) (groupTailDegreeNatIso n k)

/-- The ENTIRE target hom retains both original level and original group-degree functions. -/
theorem groupTailIndexNatIso_hom_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupTailIndexNatIso n m k).hom.app X =
      (piNPositiveFunctor (k + 1 + n)).map ((levelTailIndexNatIso n m).hom.app X) ≫
        (groupTailDegreeNatIso n k).hom.app (X.level (m + (n + 1))) := rfl

/-- The ENTIRE target inv retains both original inverse group-degree and level functions. -/
theorem groupTailIndexNatIso_inv_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupTailIndexNatIso n m k).inv.app X =
      (groupTailDegreeNatIso n k).inv.app (X.level (m + (n + 1))) ≫
        (piNPositiveFunctor (k + 1 + n)).map ((levelTailIndexNatIso n m).inv.app X) := rfl

/-- The actual original evaluation successor keeps the entire previous map and level reindex. -/
theorem iterationEvaluationIso_succ_tail_hom (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationEvaluationIso (n + 1) m).hom.app X =
      PointedCGWH.loop.map ((iterationEvaluationIso n (m + 1)).hom.app X) ≫
        (loopPower n ⋙ PointedCGWH.loop).map ((levelTailIndexNatIso n m).hom.app X) := by
  change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
    PointedCGWH.loop.map ((iterationEvaluationIso n (m + 1)).hom.app X) ≫ 𝟙 _ ≫
      (loopPower n ⋙ PointedCGWH.loop).map ((levelTailIndexNatIso n m).hom.app X) = _
  simp only [Category.id_comp]

/-- The actual original loop-group shift successor retains its whole original defining maps. -/
theorem loopPowerGroupShiftNatIso_succ_tail_hom (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPowerGroupShiftNatIso (n + 1) k).hom.app X =
      (nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj X) ≫
        (loopPowerGroupShiftNatIso n (k + 1)).hom.app X ≫
          (groupTailDegreeNatIso n k).hom.app X := by
  change 𝟙 _ ≫ (nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj X) ≫
    (loopPowerGroupShiftNatIso n (k + 1)).hom.app X ≫
      (groupTailDegreeNatIso n k).hom.app X = _
  exact Category.id_comp _

/-- EVERY full original successor group evaluation is the actual native shift then previous map. -/
theorem iterationGroupEvaluation_succ_tail_hom (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationGroupEvaluationNatIso (n + 1) m k).hom.app X =
      (nativeLoopGroupShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)) ≫
        (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom.app X ≫
          (groupTailIndexNatIso n m k).hom.app X := by
  let A := ((iterate n).obj X).level (m + 1)
  let E := X.level (m + 1 + n)
  let E' := X.level (m + (n + 1))
  let p : A ⟶ (loopPower n).obj E := (iterationEvaluationIso n (m + 1)).hom.app X
  let j : E ⟶ E' := (levelTailIndexNatIso n m).hom.app X
  have hp : (iterationEvaluationIso (n + 1) m).hom.app X =
      PointedCGWH.loop.map (p ≫ (loopPower n).map j) :=
    (iterationEvaluationIso_succ_tail_hom n m X).trans (PointedCGWH.loop.map_comp p _).symm
  have hP := (piNPositiveFunctor k).congr_map hp
  have hS := loopPowerGroupShiftNatIso_succ_tail_hom n k E'
  have h := originalLoopGroupTailWord (loopPower n) PointedCGWH.loop
    (piNPositiveFunctor k) (piNPositiveFunctor (k + 1)) (piNPositiveFunctor (k + 1 + n))
    p j ((nativeLoopGroupShiftNatIso k).hom.app A)
    ((nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj E))
    ((nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj E'))
    ((loopPowerGroupShiftNatIso n (k + 1)).hom.app E)
    ((loopPowerGroupShiftNatIso n (k + 1)).hom.app E')
    ((groupTailDegreeNatIso n k).hom.app E')
    ((nativeLoopGroupShiftNatIso k).hom.naturality ((loopPower n).map j))
    ((nativeLoopGroupShiftNatIso k).hom.naturality p)
    ((loopPowerGroupShiftNatIso n (k + 1)).hom.naturality j)
  have hPrev := iterationGroupEvaluationNatIso_hom_app n (m + 1) (k + 1) X
  have hIndex := groupTailIndexNatIso_hom_app n m k X
  exact (iterationGroupEvaluationNatIso_hom_app (n + 1) m k X).trans
    ((congrArg₂ (fun f g => f ≫ g) hP hS).trans
      (h.trans (congrArg₂ (fun f g => (nativeLoopGroupShiftNatIso k).hom.app A ≫ f ≫ g)
        hPrev.symm hIndex.symm)))

/-- The full actual one-loop source comparison uses the SAME original evaluation and shift Iso. -/
def iterationNativeGroupShiftNatIso (n m k : ℕ) :
    iterate.{u, v} (n + 1) ⋙ CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m
      ⋙ piNPositiveFunctor k ≅
      iterate n ⋙ CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + 1) ⋙
        piNPositiveFunctor (k + 1) :=
  Functor.associator (iterate n) functor (CategoryTheory.Spectra.Sequential.evaluation
    PointedCGWH.sphereOne m ⋙ piNPositiveFunctor k) ≪≫
    Functor.isoWhiskerLeft (iterate n)
      ((Functor.associator functor (CategoryTheory.Spectra.Sequential.evaluation
        PointedCGWH.sphereOne m) (piNPositiveFunctor k)).symm ≪≫
        Functor.isoWhiskerRight (levelEvaluationIso m) (piNPositiveFunctor k) ≪≫
          Functor.associator (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne
            (m + 1)) PointedCGWH.loop
            (piNPositiveFunctor k) ≪≫
          Functor.isoWhiskerLeft (CategoryTheory.Spectra.Sequential.evaluation
            PointedCGWH.sphereOne (m + 1)) (nativeLoopGroupShiftNatIso k))

/-- The ENTIRE original one-loop comparison hom function is the SAME native group loop shift. -/
theorem iterationNativeGroupShiftNatIso_hom_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationNativeGroupShiftNatIso n m k).hom.app X =
      (nativeLoopGroupShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)) := by
  change 𝟙 _ ≫ (𝟙 _ ≫ (piNPositiveFunctor k).map (𝟙 _) ≫ 𝟙 _ ≫
    (nativeLoopGroupShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1))) = _
  simp only [Category.id_comp]
  have h := (piNPositiveFunctor.{u, v} k).map_id
    (PointedCGWH.loop.obj (((iterate n).obj X).level (m + 1)))
  exact (congrArg (fun f => f ≫
    (nativeLoopGroupShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1))) h).trans
      (Category.id_comp _)

/-- The WHOLE actual original successor comparison retains the same full tail association. -/
theorem iterationGroupEvaluation_succ_tail_whole (n m k : ℕ) :
    (iterationGroupEvaluationNatIso.{u, v} (n + 1) m k).hom =
      (iterationNativeGroupShiftNatIso n m k).hom ≫
        (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom ≫
          (groupTailIndexNatIso n m k).hom := by
  apply NatTrans.ext
  funext X
  have h := iterationGroupEvaluation_succ_tail_hom n m k X
  exact h.trans (congrArg (fun f => f ≫
    (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom.app X ≫
      (groupTailIndexNatIso n m k).hom.app X)
        (iterationNativeGroupShiftNatIso_hom_app n m k X).symm)

/-- The ENTIRE original successor Iso, including both functions and all laws, is retained. -/
theorem iterationGroupEvaluation_succ_tail_Iso (n m k : ℕ) :
    iterationGroupEvaluationNatIso.{u, v} (n + 1) m k =
      iterationNativeGroupShiftNatIso n m k ≪≫
        iterationGroupEvaluationNatIso n (m + 1) (k + 1) ≪≫ groupTailIndexNatIso n m k :=
  Iso.ext (iterationGroupEvaluation_succ_tail_whole n m k)

/-- The ENTIRE original inverse successor retains all actual original inverse source maps. -/
theorem iterationGroupEvaluation_succ_tail_inv_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationGroupEvaluationNatIso (n + 1) m k).inv.app X =
      (groupTailIndexNatIso n m k).inv.app X ≫
        (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).inv.app X ≫
          (iterationNativeGroupShiftNatIso n m k).inv.app X :=
  congrArg (fun i => i.inv.app X) (iterationGroupEvaluation_succ_tail_Iso n m k)

/-- ACTUAL original R structure maps are the SAME original diagonal sigma/index transitions. -/
theorem iteration_group_structure_diagonal_index_square (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupStructureNatTrans m k).app ((iterate n).obj X) ≫
        (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom.app X ≫
          (groupTailIndexNatIso n m k).hom.app X =
      (iterationGroupEvaluationNatIso n m k).hom.app X ≫ (diagonalTransition n m k).app X := by
  have h := iterationGroupEvaluation_unit_transition_hom n m k X
  have hG := iterationGroupEvaluation_succ_tail_hom n m k X
  have hS := iterateUnitGroupMap_then_shift n m k X
  have hword := congrArg (fun f => (piNPositiveFunctor k).map
    (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) ≫ f) hG
  have hfirst := congrArg (fun f => f ≫
    (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom.app X ≫
      (groupTailIndexNatIso n m k).hom.app X) hS
  exact hfirst.trans ((Category.assoc _ _ _).trans (hword.symm.trans h))

/-- The WHOLE actual original R sigma and original diagonal transition square is preserved. -/
theorem iteration_group_structure_diagonal_index_square_whole (n m k : ℕ) :
    Functor.whiskerLeft (iterate n) (groupStructureNatTrans m k) ≫
        (iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom ≫
          (groupTailIndexNatIso n m k).hom =
      (iterationGroupEvaluationNatIso n m k).hom ≫ diagonalTransition.{u, v} n m k := by
  apply NatTrans.ext
  funext X
  exact iteration_group_structure_diagonal_index_square n m k X

end PointedCGWH.SequentialSpectrum.MappingTelescope.GroupEvaluationTailGeometry
