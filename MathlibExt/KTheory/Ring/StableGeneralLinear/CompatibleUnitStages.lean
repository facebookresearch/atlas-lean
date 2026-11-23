/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitCompatibility
public import MathlibExt.Topology.Category.CGWH.NativeMappingPath
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationCofibrant
public import MathlibExt.Topology.Category.CGWH.CompatibleMappingPaths

/-!
# Derived compatible original BGL unit stages

All original successor maps are proved cofibrations. The full original
unit-difference fillers and chain prisms supply whole homotopies over the
entire interval boundary. Slice-model homotopy extension then derives a
strictly compatible sequence on the ORIGINAL finite BGL diagram, preserving
both original endpoints at every stage and the whole original comparison
class. Neither a compatible family nor a product/CW/filler witness is a
caller input. Descent to the original stable BGL is a separate colimit step.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

universe u

namespace AlgebraicKTheory.StableGL

public local instance finiteNativeT2 (R : Type u) [Ring R] (n : ℕ) :
    T2Space ((finiteBGLDiagram.{u} R).obj n) :=
  SSet.realization_t2Space (nerve ((finiteClassifyingCategoryDiagram R).obj n))

public local instance finiteNativeGroupT2 (R : Type u) [Ring R] (n : ℕ) :
    T2Space (CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) := by
  letI : T2Space (CategoryTheory.groupClassifyingOrdinary
      (Matrix.GeneralLinearGroup (Fin n) R)) :=
    SSet.realization_t2Space
      (CategoryTheory.groupClassifyingNerve (Matrix.GeneralLinearGroup (Fin n) R))
  exact (TopCat.homeoOfIso (CategoryTheory.groupClassifyingToTopIso.{u, u}
    (Matrix.GeneralLinearGroup (Fin n) R))).symm.t2Space

private local instance finiteNativeCofibrant (R : Type u) [Ring R] (n : ℕ) :
    IsCofibrant ((finiteBGLDiagram.{u} R).obj n) :=
  SSet.toCGWH_obj_isCofibrant (nerve ((finiteClassifyingCategoryDiagram R).obj n))

/-- The original whole finite-stage unit path, now as an actual native
map into the interval internal Hom of the SAME independent target model. -/
public abbrev independentBGLCanonicalLeftUnitStage (R : Type u) [Ring R] (n : ℕ) :
    (finiteBGLDiagram.{u} R).obj n ⟶
      (ihom CGWH.nativeInterval.{u, u}).obj
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)) :=
  CGWH.nativeMappingPathCurry (independentBGLLeftUnitMappingPath R n)

private theorem canonicalLeftUnitStage_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLCanonicalLeftUnitStage R n =
      CGWH.nativeMappingPathCurry (independentBGLLeftUnitMappingPath R n) := rfl

/-- The next original stage restricts to the computed NEXT unit map on
the old stage, as an equality of ENTIRE native interval-homotopy maps. -/
public theorem independentBGLCanonicalLeftUnitStage_restriction (R : Type u) [Ring R] (n : ℕ) :
    CGWH.nativeMappingPathCurry (independentBGLNextLeftUnitMappingPath R n) =
      (finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_succ n)) ≫
        independentBGLCanonicalLeftUnitStage R (n + 1) :=
  CGWH.nativeMappingPathCurry_precomp
    ((finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_succ n)))
    (independentBGLNextLeftUnitMappingPath R n) (independentBGLLeftUnitMappingPath R (n + 1))
    (independentBGLNextLeftUnitMappingPath_restriction_apply R n)

/-- Actual whole finite-stage fillers derive a genuine compatible unit
cocone on the ORIGINAL diagram. The entire boundary and original stage
comparison classes are preserved. This is over EVERY unchanged ring and
every original stage, including zero, without a supplied stage family. -/
public theorem exists_compatible_independentBGLLeftUnitStages (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let E := (ihom CGWH.nativeInterval.{u, u}).obj M
    let r := (MonoidalClosed.pre CGWH.nativeIntervalBoundary).app M
    ∃ s : finiteBGLDiagram.{u} R ⟶ (Functor.const ℕ).obj E,
      s.app 0 = independentBGLCanonicalLeftUnitStage R 0 ∧
      ∀ n, ∃ h : s.app n ≫ r = independentBGLCanonicalLeftUnitStage R n ≫ r,
        RightHomotopyRel
          (Over.homMk (independentBGLCanonicalLeftUnitStage R n) rfl :
            Over.mk (independentBGLCanonicalLeftUnitStage R n ≫ r) ⟶ Over.mk r)
          (Over.homMk (s.app n) h) := by
  let F := finiteBGLDiagram.{u} R
  let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  letI : ∀ n, T2Space (F.obj n) := fun n => finiteNativeT2 R n
  letI : IsFibrant M := CGWH.modelCategory.allObjectsFibrant M
  let E := (ihom CGWH.nativeInterval.{u, u}).obj M
  let r := (MonoidalClosed.pre CGWH.nativeIntervalBoundary.{u, u}).app M
  let raw : ∀ n, F.obj n ⟶ E :=
    fun n => CGWH.nativeMappingPathCurry (independentBGLLeftUnitMappingPath R n)
  let named : ∀ n, F.obj n ⟶ E := independentBGLCanonicalLeftUnitStage R
  have hFamily : raw = named := by
    funext n
    exact (canonicalLeftUnitStage_recipe R n).symm
  let FamilyProperty (p : ∀ n, F.obj n ⟶ E) : Prop :=
    ∃ s : F ⟶ (Functor.const ℕ).obj E,
      s.app 0 = p 0 ∧
      ∀ n, ∃ h : s.app n ≫ r = p n ≫ r,
        RightHomotopyRel
          (Over.homMk (p n) rfl : Over.mk (p n ≫ r) ⟶ Over.mk r)
          (Over.homMk (s.app n) h)
  have hRaw : FamilyProperty raw := CGWH.exists_compatibleMappingPathCocone F M
    (fun n => finiteNativeCofibrant R n)
    (fun n => finiteBGLSuccessor_cofibration R n)
    (independentBGLFiniteMapToNativeModel R) (independentBGLFiniteLeftBlockMapToNativeModel R)
    (independentBGLLeftUnitMappingPath R) (independentBGLNextLeftUnitMappingPath R)
    (independentBGLNextLeftUnitMappingPath_restriction_apply R)
    (independentBGLLeftUnitMappingPaths_homotopic R)
  exact Eq.mp (congrArg FamilyProperty hFamily) hRaw

end AlgebraicKTheory.StableGL

end
