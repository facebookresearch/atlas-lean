/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.CompatibleUnitStages
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingColimit
public import MathlibExt.Topology.Category.CGWH.NativeIntervalEvaluation
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# The original global left unit family in the independent BGL plus model

The DERIVED compatible finite-stage maps descend through the ORIGINAL
stable BGL cofan. Their complete boundary equations identify both global
endpoints with the original inclusion and original first block embedding,
followed by the SAME independently constructed plus and its derived native
model inverse. The target is that same cell plus model, not a Q-model.
No global homotopy, compatible family, or colimit witness is a caller input.
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

attribute [local instance] independentBGLCellPoint_cofibration finiteNativeT2 finiteNativeGroupT2

private theorem canonicalLeftUnitStage_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLCanonicalLeftUnitStage R n =
      CGWH.nativeMappingPathCurry (independentBGLLeftUnitMappingPath R n) := rfl

private theorem finiteModelMap_composition_recipe (R : Type u) [Ring R] (n : ℕ) :
    (ConcreteCategory.ofHom (C := CGWH.{u, u})
      (X := (finiteBGLDiagram.{u} R).obj n)
      (Y := TopCat.nativeSingularSpace (independentBGLCellTarget R))
      (independentBGLFiniteMapToNativeModel R n)) =
      finiteBGLToBGL R n ≫ originalBGLToPlusNativeModel R
        (independentBGLCellInclusion R) (independentBGLCellPoint R) := by
  apply ConcreteCategory.hom_ext
  intro a
  rfl

private theorem finiteLeftBlockModelMap_composition_recipe (R : Type u) [Ring R] (n : ℕ) :
    (ConcreteCategory.ofHom (C := CGWH.{u, u})
      (X := (finiteBGLDiagram.{u} R).obj n)
      (Y := TopCat.nativeSingularSpace (independentBGLCellTarget R))
      (independentBGLFiniteLeftBlockMapToNativeModel R n)) =
      SSet.toCGWH.{u, u}.map (nerveMap
        ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R)) ≫
        originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R) := by
  apply ConcreteCategory.hom_ext
  intro a
  rfl

private theorem nativeRealization_map_comp {X Y Z : SSet.{u}}
    (k1 : X ⟶ Y) (k2 : Y ⟶ Z) :
    SSet.toCGWH.{u, u}.map (k1 ≫ k2) =
      SSet.toCGWH.{u, u}.map k1 ≫ SSet.toCGWH.{u, u}.map k2 :=
  (SSet.toCGWH.{u, u}).map_comp k1 k2

private theorem canonicalLeftUnitStage_zero (R : Type u) [Ring R] (n : ℕ) :
    independentBGLCanonicalLeftUnitStage R n ≫ CGWH.nativeIntervalEvaluation 0
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)) =
      finiteBGLToBGL R n ≫ originalBGLToPlusNativeModel R
        (independentBGLCellInclusion R) (independentBGLCellPoint R) := by
  have h := CGWH.nativeMappingPathCurry_evaluation_zero (independentBGLLeftUnitMappingPath R n)
  have hStage := congrArg (fun s : (finiteBGLDiagram.{u} R).obj n ⟶
      (ihom CGWH.nativeInterval.{u, u}).obj
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)) =>
    s ≫ CGWH.nativeIntervalEvaluation.{u, u} 0
      (TopCat.nativeSingularSpace (independentBGLCellTarget R)))
    (canonicalLeftUnitStage_recipe R n)
  calc
    independentBGLCanonicalLeftUnitStage R n ≫ CGWH.nativeIntervalEvaluation 0
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)) =
      ConcreteCategory.ofHom (C := CGWH.{u, u})
        (X := (finiteBGLDiagram.{u} R).obj n)
        (Y := TopCat.nativeSingularSpace (independentBGLCellTarget R))
        (independentBGLFiniteMapToNativeModel R n) := hStage.trans h
    _ = finiteBGLToBGL R n ≫ originalBGLToPlusNativeModel R
        (independentBGLCellInclusion R) (independentBGLCellPoint R) :=
      finiteModelMap_composition_recipe R n

private theorem canonicalLeftUnitStage_one (R : Type u) [Ring R] (n : ℕ) :
    independentBGLCanonicalLeftUnitStage R n ≫ CGWH.nativeIntervalEvaluation 1
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)) =
      finiteBGLToBGL R n ≫ blockSumLeftBGLMap R ≫ originalBGLToPlusNativeModel R
        (independentBGLCellInclusion R) (independentBGLCellPoint R) := by
  let A : CGWH.{u, u} := (finiteBGLDiagram.{u} R).obj n
  let M : CGWH.{u, u} := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let q : BGL.{u} R ⟶ M := originalBGLToPlusNativeModel R
    (independentBGLCellInclusion R) (independentBGLCellPoint R)
  let m : A ⟶ BGL.{u} R := SSet.toCGWH.{u, u}.map (nerveMap
    ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R))
  let f : A ⟶ M := ConcreteCategory.ofHom (C := CGWH.{u, u})
    (X := A) (Y := M) (independentBGLFiniteLeftBlockMapToNativeModel R n)
  have hm : m = finiteBGLToBGL R n ≫ blockSumLeftBGLMap R := by
    let X : SSet.{u} := CategoryTheory.nerveFunctor.{u, 0}.obj
      ((finiteClassifyingCategoryDiagram R).obj n)
    let Y : SSet.{u} := CategoryTheory.nerveFunctor.{u, 0}.obj
      (Cat.of (ClassifyingCategory R))
    let k1 : X ⟶ Y := CategoryTheory.nerveFunctor.{u, 0}.map
      (finiteToStableCategoryMap R n)
    let k2 : Y ⟶ Y := CategoryTheory.nerveFunctor.{u, 0}.map
      (blockSumLeftClassifyingFunctor R).toCatHom
    have hNerve :
        (nerveMap ((finiteToStableCategoryMap R n).toFunctor ⋙
          blockSumLeftClassifyingFunctor R) : X ⟶ Y) = k1 ≫ k2 :=
      (CategoryTheory.nerveMap_comp (finiteToStableCategoryMap R n).toFunctor
        (blockSumLeftClassifyingFunctor R)).symm
    have hFirst : SSet.toCGWH.{u, u}.map k1 = finiteBGLToBGL R n := rfl
    have hSecond : SSet.toCGWH.{u, u}.map k2 = blockSumLeftBGLMap R := rfl
    have hRealization : SSet.toCGWH.{u, u}.map (k1 ≫ k2) =
        SSet.toCGWH.{u, u}.map k1 ≫ SSet.toCGWH.{u, u}.map k2 :=
      nativeRealization_map_comp k1 k2
    exact (congrArg (fun k : X ⟶ Y => SSet.toCGWH.{u, u}.map k) hNerve).trans
      (hRealization.trans (congrArg₂
        (fun (f : A ⟶ BGL.{u} R) (g : BGL.{u} R ⟶ BGL.{u} R) => f ≫ g)
        hFirst hSecond))
  have h := CGWH.nativeMappingPathCurry_evaluation_one (independentBGLLeftUnitMappingPath R n)
  have hStage := congrArg (fun s : A ⟶ (ihom CGWH.nativeInterval.{u, u}).obj M =>
    s ≫ CGWH.nativeIntervalEvaluation.{u, u} 1 M) (canonicalLeftUnitStage_recipe R n)
  have h0 : independentBGLCanonicalLeftUnitStage R n ≫
      CGWH.nativeIntervalEvaluation.{u, u} 1 M = f := hStage.trans h
  have h1 : f = m ≫ q := finiteLeftBlockModelMap_composition_recipe R n
  have h2 : m ≫ q = (finiteBGLToBGL R n ≫ blockSumLeftBGLMap R) ≫ q :=
    congrArg (fun k : A ⟶ BGL.{u} R => k ≫ q) hm
  have h3 : (finiteBGLToBGL R n ≫ blockSumLeftBGLMap R) ≫ q =
      finiteBGLToBGL R n ≫ blockSumLeftBGLMap R ≫ q := Category.assoc _ _ _
  exact h0.trans (h1.trans (h2.trans h3))

/-- The actual original finite-stage family descends to a GLOBAL native
interval map on BGL(R). Both ORIGINAL global endpoints and the strict
zero-stage restriction are derived, over every unchanged ring. -/
public theorem exists_independentBGLGlobalLeftUnitMap (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    ∃ s : BGL.{u} R ⟶ (ihom CGWH.nativeInterval.{u, u}).obj M,
      s ≫ CGWH.nativeIntervalEvaluation 0 M = q ∧
      s ≫ CGWH.nativeIntervalEvaluation 1 M = blockSumLeftBGLMap R ≫ q ∧
      finiteBGLToBGL R 0 ≫ s = independentBGLCanonicalLeftUnitStage R 0 := by
  let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let E := (ihom CGWH.nativeInterval.{u, u}).obj M
  let r := (MonoidalClosed.pre CGWH.nativeIntervalBoundary).app M
  let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
    (independentBGLCellPoint R)
  obtain ⟨c, hc₀, hc⟩ := exists_compatible_independentBGLLeftUnitStages R
  let C := finiteBGLCocone.{u, u} R
  let hC := finiteBGLCoconeIsColimit.{u, u} R
  let s := hC.desc (Cocone.mk E c)
  have hs (n : ℕ) : finiteBGLToBGL R n ≫ s = c.app n := hC.fac (Cocone.mk E c) n
  have hboundary (n : ℕ) :
      (finiteBGLToBGL R n ≫ s) ≫ r = independentBGLCanonicalLeftUnitStage R n ≫ r := by
    obtain ⟨hn, _⟩ := hc n
    exact (congrArg (fun f => f ≫ r) (hs n)).trans hn
  have hzero : s ≫ CGWH.nativeIntervalEvaluation 0 M = q := by
    apply hC.hom_ext
    intro n
    calc
      C.ι.app n ≫ s ≫ CGWH.nativeIntervalEvaluation 0 M =
          (finiteBGLToBGL R n ≫ s) ≫ CGWH.nativeIntervalEvaluation 0 M :=
        (Category.assoc _ _ _).symm
      _ = independentBGLCanonicalLeftUnitStage R n ≫ CGWH.nativeIntervalEvaluation 0 M :=
        CGWH.nativeIntervalEvaluation_eq_of_boundary _ _ (hboundary n) 0
      _ = C.ι.app n ≫ q := canonicalLeftUnitStage_zero R n
  have hone : s ≫ CGWH.nativeIntervalEvaluation 1 M = blockSumLeftBGLMap R ≫ q := by
    apply hC.hom_ext
    intro n
    calc
      C.ι.app n ≫ s ≫ CGWH.nativeIntervalEvaluation 1 M =
          (finiteBGLToBGL R n ≫ s) ≫ CGWH.nativeIntervalEvaluation 1 M :=
        (Category.assoc _ _ _).symm
      _ = independentBGLCanonicalLeftUnitStage R n ≫ CGWH.nativeIntervalEvaluation 1 M :=
        CGWH.nativeIntervalEvaluation_eq_of_boundary _ _ (hboundary n) 1
      _ = C.ι.app n ≫ blockSumLeftBGLMap R ≫ q := canonicalLeftUnitStage_one R n
  exact ⟨s, hzero, hone, (hs 0).trans hc₀⟩

/-- A genuine GLOBAL original left-unit homotopy in the SAME independent
target model. Both endpoint equations are complete morphism equations,
and the original zero-stage family remains strict. -/
public theorem exists_independentBGLGlobalLeftUnitNativeHomotopy (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    ∃ H : CGWH.nativeInterval.{u, u} ⊗ BGL.{u} R ⟶ M,
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 0 ▷ BGL.{u} R) ≫ H = q ∧
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 1 ▷ BGL.{u} R) ≫ H =
        blockSumLeftBGLMap R ≫ q ∧
      (CGWH.nativeInterval ◁ finiteBGLToBGL R 0) ≫ H =
        MonoidalClosed.uncurry (independentBGLCanonicalLeftUnitStage R 0) := by
  obtain ⟨s, h₀, h₁, hs₀⟩ := exists_independentBGLGlobalLeftUnitMap R
  refine ⟨MonoidalClosed.uncurry s, ?_, ?_, ?_⟩
  · exact (CGWH.nativeIntervalEvaluation_comp s 0).symm.trans h₀
  · exact (CGWH.nativeIntervalEvaluation_comp s 1).symm.trans h₁
  · rw [← MonoidalClosed.uncurry_natural_left, hs₀]

private theorem zeroStagePoint_image (R : Type u) [Ring R] :
    finiteBGLToBGL R 0
        (CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)) =
      BGLBasepoint R := by
  rw [CategoryTheory.groupClassifyingNativePoint_eq_categoryPoint.{u, u}]
  exact CategoryTheory.classifyingSpaceCGWH_map_point
    (finiteToStableCategoryMap R 0).toFunctor
    (SingleObj.star (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ)

/-- The GLOBAL original left-unit family fixes the ORIGINAL marked point
at EVERY native interval value. This follows from its strict zero-stage
restriction and the literal constant zero-stage prism, rather than a
pointwise fundamental-group nullity assertion. -/
public theorem exists_independentBGLGlobalLeftUnitPointedNativeHomotopy
    (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    ∃ H : CGWH.nativeInterval.{u, u} ⊗ BGL.{u} R ⟶ M,
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 0 ▷ BGL.{u} R) ≫ H = q ∧
      (λ_ (BGL.{u} R)).inv ≫ (CGWH.nativeIntervalEndpoint 1 ▷ BGL.{u} R) ≫ H =
        blockSumLeftBGLMap R ≫ q ∧
      ∀ s : CGWH.nativeInterval.{u, u}, H (CGWH.tensorMk s (BGLBasepoint R)) =
        TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  obtain ⟨H, h₀, h₁, hs₀⟩ := exists_independentBGLGlobalLeftUnitNativeHomotopy R
  letI : T2Space (CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)) :=
    CategoryTheory.groupClassifyingNative_t2Space.{u, u} _
  refine ⟨H, h₀, h₁, ?_⟩
  intro s
  let a := CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)
  have hstage := ConcreteCategory.congr_hom hs₀ (CGWH.tensorMk s a)
  have hWhisker : (CGWH.nativeInterval.{u, u} ◁ finiteBGLToBGL R 0)
      (CGWH.tensorMk s a) = CGWH.tensorMk s (finiteBGLToBGL R 0 a) :=
    CGWH.tensorMk_whiskerLeft _ s a
  have hStageEvaluation :
      ((CGWH.nativeInterval.{u, u} ◁ finiteBGLToBGL R 0) ≫ H) (CGWH.tensorMk s a) =
        H (CGWH.tensorMk s (finiteBGLToBGL R 0 a)) :=
    (ConcreteCategory.comp_apply _ _ _).trans (congrArg H hWhisker)
  have hStageUncurry := ConcreteCategory.congr_hom
    (congrArg (fun k : (finiteBGLDiagram.{u} R).obj 0 ⟶
        (ihom CGWH.nativeInterval.{u, u}).obj
          (TopCat.nativeSingularSpace (independentBGLCellTarget R)) =>
      MonoidalClosed.uncurry k) (canonicalLeftUnitStage_recipe R 0)) (CGWH.tensorMk s a)
  have hp := zeroStagePoint_image R
  have hvalue : H (CGWH.tensorMk s (BGLBasepoint R)) =
      independentBGLFiniteMapToNativeModel R 0 a := by
    calc
      H (CGWH.tensorMk s (BGLBasepoint R)) =
          H (CGWH.tensorMk s (finiteBGLToBGL R 0 a)) :=
        congrArg (fun b => H (CGWH.tensorMk s b)) hp.symm
      _ = MonoidalClosed.uncurry (independentBGLCanonicalLeftUnitStage R 0)
          (CGWH.tensorMk s a) := by
        exact hStageEvaluation.symm.trans hstage
      _ = independentBGLLeftUnitMappingPath R 0 (CGWH.nativeIntervalClock s) a :=
        hStageUncurry.trans (CGWH.nativeMappingPathCurry_uncurry_apply _ s a)
      _ = independentBGLFiniteMapToNativeModel R 0 a :=
        independentBGLLeftUnitMappingPath_zero_stage_apply R _ a
  have hmap : independentBGLFiniteMapToNativeModel R 0 a =
      originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) (BGLBasepoint R) :=
    (ConcreteCategory.congr_hom (finiteModelMap_composition_recipe R 0) a).trans
      (congrArg (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R)) hp)
  exact hvalue.trans (hmap.trans (originalBGLToPlusNativeModel_point R
    (independentBGLCellInclusion R) (independentBGLCellPoint R)
    (independentBGLCellInclusion_point R)))

end AlgebraicKTheory.StableGL

end
