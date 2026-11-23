/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.RightUnitCompatibility
public import MathlibExt.Topology.Category.CGWH.CompatibleMappingPaths
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationCofibrant

/-!
# The actual strict compatible right-unit stages

The ORIGINAL successor cofibrations and DERIVED whole right-unit path
comparisons feed the shared slice-model path construction. It returns
actual maps on the ORIGINAL finite BGL diagram, preserving both original
boundary maps and the strict constant zero stage. No compatible family,
CW model or homotopy witness enters this Ring theorem.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

universe u

namespace AlgebraicKTheory.StableGL

/-- The ORIGINAL right-unit path as its actual whole native interval map. -/
public abbrev independentBGLCanonicalRightUnitStage (R : Type u) [Ring R] (n : ℕ) :
    (finiteBGLDiagram.{u} R).obj n ⟶
      (ihom CGWH.nativeInterval.{u, u}).obj
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)) := by
  letI : T2Space ((finiteBGLDiagram.{u} R).obj n) :=
    SSet.realization_t2Space (nerve ((finiteClassifyingCategoryDiagram R).obj n))
  exact CGWH.nativeMappingPathCurry (independentBGLRightUnitMappingPath R n)

/-- The ORIGINAL whole right-unit paths derive a strict compatible cocone
on the ORIGINAL finite BGL diagram, over EVERY unchanged Ring. -/
public theorem exists_compatible_independentBGLRightUnitStages (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let E := (ihom CGWH.nativeInterval.{u, u}).obj M
    let r := (MonoidalClosed.pre CGWH.nativeIntervalBoundary).app M
    ∃ s : finiteBGLDiagram.{u} R ⟶ (Functor.const ℕ).obj E,
      s.app 0 = independentBGLCanonicalRightUnitStage R 0 ∧
      ∀ n, ∃ h : s.app n ≫ r = independentBGLCanonicalRightUnitStage R n ≫ r,
        RightHomotopyRel
          (Over.homMk (independentBGLCanonicalRightUnitStage R n) rfl :
            Over.mk (independentBGLCanonicalRightUnitStage R n ≫ r) ⟶ Over.mk r)
          (Over.homMk (s.app n) h) := by
  let F := finiteBGLDiagram.{u} R
  let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  letI : ∀ n, T2Space (F.obj n) := fun n =>
    SSet.realization_t2Space (nerve ((finiteClassifyingCategoryDiagram R).obj n))
  letI : IsFibrant M := CGWH.modelCategory.allObjectsFibrant M
  exact CGWH.exists_compatibleMappingPathCocone F M
    (fun n => SSet.toCGWH_obj_isCofibrant (nerve ((finiteClassifyingCategoryDiagram R).obj n)))
    (fun n => finiteBGLSuccessor_cofibration R n)
    (independentBGLFiniteMapToNativeModel R) (independentBGLFiniteRightBlockMapToNativeModel R)
    (independentBGLRightUnitMappingPath R) (independentBGLNextRightUnitMappingPath R)
    (independentBGLNextRightUnitMappingPath_restriction_apply R)
    (independentBGLRightUnitMappingPaths_homotopic R)

end AlgebraicKTheory.StableGL

end
