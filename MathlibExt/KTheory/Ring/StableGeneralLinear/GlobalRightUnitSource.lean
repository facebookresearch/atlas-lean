/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.CompatibleRightUnitStages
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingColimit
public import MathlibExt.Topology.Category.CGWH.NativeMappingPathColimit

/-!
# The GLOBAL original right-unit family in the SAME independent BGL plus

The actual complete right-unit paths descend through the ORIGINAL BGL
colimit. Both original global maps remain the endpoints. The strict zero
stage and its literal constant prism retain the ORIGINAL marked point at
every time. No global homotopy, compatible cocone, model or inverse is
supplied; the target is the native model of the SAME constructed cell plus.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped TopCat.modelCategory CGWH.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

private local instance independentCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

attribute [local instance] independentBGLCellPoint_cofibration

private theorem nativeRealization_map_comp {X Y Z : SSet.{u}}
    (k1 : X ⟶ Y) (k2 : Y ⟶ Z) :
    SSet.toCGWH.{u, u}.map (k1 ≫ k2) =
      SSet.toCGWH.{u, u}.map k1 ≫ SSet.toCGWH.{u, u}.map k2 :=
  (SSet.toCGWH.{u, u}).map_comp k1 k2

private theorem rightStage_zero_map (R : Type u) [Ring R] (n : ℕ) :
    ConcreteCategory.ofHom (independentBGLFiniteMapToNativeModel R n) =
      finiteBGLToBGL R n ≫ originalBGLToPlusNativeModel R
        (independentBGLCellInclusion R) (independentBGLCellPoint R) := by
  apply ConcreteCategory.hom_ext
  intro a
  rfl

private theorem rightStage_one_map (R : Type u) [Ring R] (n : ℕ) :
    ConcreteCategory.ofHom (independentBGLFiniteRightBlockMapToNativeModel R n) =
      finiteBGLToBGL R n ≫ blockSumRightBGLMap R ≫ originalBGLToPlusNativeModel R
        (independentBGLCellInclusion R) (independentBGLCellPoint R) := by
  let A : CGWH.{u, u} := (finiteBGLDiagram.{u} R).obj n
  let M : CGWH.{u, u} := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let q : BGL.{u} R ⟶ M := originalBGLToPlusNativeModel R
    (independentBGLCellInclusion R) (independentBGLCellPoint R)
  let m : A ⟶ BGL.{u} R := SSet.toCGWH.{u, u}.map (nerveMap
    ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R))
  let f : A ⟶ M := ConcreteCategory.ofHom (C := CGWH.{u, u})
    (X := A) (Y := M) (independentBGLFiniteRightBlockMapToNativeModel R n)
  have hm : m = finiteBGLToBGL R n ≫ blockSumRightBGLMap R := by
    let X : SSet.{u} := CategoryTheory.nerveFunctor.{u, 0}.obj
      ((finiteClassifyingCategoryDiagram R).obj n)
    let Y : SSet.{u} := CategoryTheory.nerveFunctor.{u, 0}.obj
      (Cat.of (ClassifyingCategory R))
    let k1 : X ⟶ Y := CategoryTheory.nerveFunctor.{u, 0}.map
      (finiteToStableCategoryMap R n)
    let k2 : Y ⟶ Y := CategoryTheory.nerveFunctor.{u, 0}.map
      (blockSumRightClassifyingFunctor R).toCatHom
    have hNerve :
        (nerveMap ((finiteToStableCategoryMap R n).toFunctor ⋙
          blockSumRightClassifyingFunctor R) : X ⟶ Y) = k1 ≫ k2 :=
      (CategoryTheory.nerveMap_comp (finiteToStableCategoryMap R n).toFunctor
        (blockSumRightClassifyingFunctor R)).symm
    have hFirst : SSet.toCGWH.{u, u}.map k1 = finiteBGLToBGL R n := rfl
    have hSecond : SSet.toCGWH.{u, u}.map k2 = blockSumRightBGLMap R := rfl
    have hRealization : SSet.toCGWH.{u, u}.map (k1 ≫ k2) =
        SSet.toCGWH.{u, u}.map k1 ≫ SSet.toCGWH.{u, u}.map k2 :=
      nativeRealization_map_comp k1 k2
    exact (congrArg (fun k : X ⟶ Y => SSet.toCGWH.{u, u}.map k) hNerve).trans
      (hRealization.trans (congrArg₂
        (fun (f : A ⟶ BGL.{u} R) (g : BGL.{u} R ⟶ BGL.{u} R) => f ≫ g)
        hFirst hSecond))
  have h0 : f = m ≫ q := by
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have h1 : m ≫ q = (finiteBGLToBGL R n ≫ blockSumRightBGLMap R) ≫ q :=
    congrArg (fun k : A ⟶ BGL.{u} R => k ≫ q) hm
  have h2 : (finiteBGLToBGL R n ≫ blockSumRightBGLMap R) ≫ q =
      finiteBGLToBGL R n ≫ blockSumRightBGLMap R ≫ q := Category.assoc _ _ _
  exact h0.trans (h1.trans h2)

/-- The DERIVED original whole right-unit paths construct a GLOBAL native
interval map with BOTH original endpoint maps and strict zero-stage restriction. -/
public theorem exists_independentBGLGlobalRightUnitMap (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    ∃ s : BGL.{u} R ⟶ (ihom CGWH.nativeInterval.{u, u}).obj M,
      s ≫ CGWH.nativeIntervalEvaluation 0 M = q ∧
      s ≫ CGWH.nativeIntervalEvaluation 1 M = blockSumRightBGLMap R ≫ q ∧
      finiteBGLToBGL R 0 ≫ s = independentBGLCanonicalRightUnitStage R 0 := by
  let F := finiteBGLDiagram.{u} R
  let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
    (independentBGLCellPoint R)
  letI : ∀ n, T2Space (F.obj n) := fun n =>
    SSet.realization_t2Space (nerve ((finiteClassifyingCategoryDiagram R).obj n))
  letI : IsFibrant M := CGWH.modelCategory.allObjectsFibrant M
  exact CGWH.exists_nativeMappingPath_on_colimit F (finiteBGLCocone.{u, u} R)
    (finiteBGLCoconeIsColimit.{u, u} R) M
    (fun n => SSet.toCGWH_obj_isCofibrant (nerve ((finiteClassifyingCategoryDiagram R).obj n)))
    (fun n => finiteBGLSuccessor_cofibration R n)
    q (blockSumRightBGLMap R ≫ q)
    (independentBGLFiniteMapToNativeModel R) (independentBGLFiniteRightBlockMapToNativeModel R)
    (independentBGLRightUnitMappingPath R) (independentBGLNextRightUnitMappingPath R)
    (independentBGLNextRightUnitMappingPath_restriction_apply R)
    (independentBGLRightUnitMappingPaths_homotopic R)
    (rightStage_zero_map R) (rightStage_one_map R)

/-- The GLOBAL original right-unit homotopy in the SAME independently
constructed plus model, retaining BOTH full endpoint maps and the strict
original zero-stage interval map. -/
public theorem exists_independentBGLGlobalRightUnitNativeHomotopy (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    ∃ H : CGWH.nativeInterval.{u, u} ⊗ BGL.{u} R ⟶ M,
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 0 ▷ BGL.{u} R) ≫ H = q ∧
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 1 ▷ BGL.{u} R) ≫ H =
        blockSumRightBGLMap R ≫ q ∧
      (CGWH.nativeInterval ◁ finiteBGLToBGL R 0) ≫ H =
        MonoidalClosed.uncurry (independentBGLCanonicalRightUnitStage R 0) := by
  obtain ⟨s, h₀, h₁, hs₀⟩ := exists_independentBGLGlobalRightUnitMap R
  refine ⟨MonoidalClosed.uncurry s, ?_, ?_, ?_⟩
  · exact (CGWH.nativeIntervalEvaluation_comp s 0).symm.trans h₀
  · exact (CGWH.nativeIntervalEvaluation_comp s 1).symm.trans h₁
  · rw [← MonoidalClosed.uncurry_natural_left, hs₀]

/-- The GLOBAL whole right-unit family fixes the ORIGINAL BGL point at
EVERY native interval value, by the strict literal constant zero stage. -/
public theorem exists_independentBGLGlobalRightUnitPointedNativeHomotopy
    (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    ∃ H : CGWH.nativeInterval.{u, u} ⊗ BGL.{u} R ⟶ M,
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 0 ▷ BGL.{u} R) ≫ H = q ∧
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 1 ▷ BGL.{u} R) ≫ H =
        blockSumRightBGLMap R ≫ q ∧
      ∀ s : CGWH.nativeInterval.{u, u}, H (CGWH.tensorMk s (BGLBasepoint R)) =
        TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  obtain ⟨H, h₀, h₁, hstage⟩ := exists_independentBGLGlobalRightUnitNativeHomotopy R
  letI : T2Space (CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)) :=
    CategoryTheory.groupClassifyingNative_t2Space.{u, u} _
  let a := CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)
  let m := TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R)
  have hconstant (s : CGWH.nativeInterval.{u, u}) :
      MonoidalClosed.uncurry (independentBGLCanonicalRightUnitStage R 0) (CGWH.tensorMk s a) = m := by
    have hpoint := finiteBGLToBGL_nativeGroupPoint R 0
    calc
      MonoidalClosed.uncurry (independentBGLCanonicalRightUnitStage R 0) (CGWH.tensorMk s a) =
          independentBGLRightUnitMappingPath R 0 (CGWH.nativeIntervalClock s) a :=
        CGWH.nativeMappingPathCurry_uncurry_apply _ s a
      _ = independentBGLFiniteMapToNativeModel R 0 a :=
        independentBGLRightUnitMappingPath_zero_stage_apply R _ a
      _ = originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R) (BGLBasepoint R) :=
        congrArg (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) hpoint
      _ = m := originalBGLToPlusNativeModel_point R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) (independentBGLCellInclusion_point R)
  exact ⟨H, h₀, h₁, CGWH.nativeIntervalHomotopy_point_of_stage (finiteBGLToBGL R 0)
    a (BGLBasepoint R) (finiteBGLToBGL_nativeGroupPoint R 0) H
    (independentBGLCanonicalRightUnitStage R 0) hstage m hconstant⟩

end AlgebraicKTheory.StableGL

end
