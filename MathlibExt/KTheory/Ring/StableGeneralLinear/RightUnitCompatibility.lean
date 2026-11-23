/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteRightUnitDifferenceNaturalLoop
public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactiveMappingPath

/-!
# Complete consecutive right-unit families in the SAME cell plus model

The actual consecutive right-unit difference has a computed perfect
inactive image. The shared whole inactive-family theorem contracts its
ORIGINAL mapping-space loop. Original natural-transformation chain prisms
then compare the two ENTIRE original right-unit paths. Their literal
successor restriction and constant zero stage are retained.
-/

noncomputable section

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory Simplicial

universe u

namespace AlgebraicKTheory.StableGL

private local instance independentCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

attribute [local instance] independentBGLCellPoint_cofibration

/-- The ORIGINAL second block map on the same finite source and target. -/
public abbrev independentBGLFiniteRightBlockMapToNativeModel
    (R : Type u) [Ring R] (n : ℕ) :
    C(CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R),
      TopCat.nativeSingularSpace (independentBGLCellTarget R)) :=
  (ConcreteCategory.hom (C := CGWH.{u, u})
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))).comp
    (ConcreteCategory.hom (C := CGWH.{u, u})
      (SSet.toCGWH.map (nerveMap
        ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R))))

/-- The entire ORIGINAL finite right-unit path in its RAW mapping space. -/
public abbrev independentBGLRightUnitMappingPath (R : Type u) [Ring R] (n : ℕ) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteRightBlockMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteRightBlockUnitIso R n).hom
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

/-- The ORIGINAL next right-unit comparison on the whole old source. -/
public abbrev independentBGLNextRightUnitMappingPath (R : Type u) [Ring R] (n : ℕ) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteRightBlockMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteNextRightBlockUnitIso R n).hom
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

/-- The ORIGINAL right-unit difference path, retaining its entire active source. -/
public abbrev independentBGLRightUnitDifferenceMappingPath
    (R : Type u) [Ring R] (n : ℕ) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteRightUnitDifferenceLoop R n)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

private theorem rightUnitPath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLRightUnitMappingPath R n =
      NatTrans.nativeNerveMappingPathPostcomp (finiteRightBlockUnitIso R n).hom
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem nextRightUnitPath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLNextRightUnitMappingPath R n =
      NatTrans.nativeNerveMappingPathPostcomp (finiteNextRightBlockUnitIso R n).hom
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem rightDifferencePath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLRightUnitDifferenceMappingPath R n =
      NatTrans.nativeNerveMappingPathPostcomp (finiteRightUnitDifferenceLoop R n)
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem rightInactivePath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLInactiveNaturalLoopMappingPath R (rightUnitCommonRank_bound.{u} n)
        (rightUnitDifferencePerfectFactor R n) =
      NatTrans.nativeNerveMappingPathPostcomp
        (finiteInactiveClassifyingLoop R (rightUnitCommonRank_bound.{u} n)
          (rightUnitDifferencePerfectFactor R n))
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem finiteModelMap_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLFiniteMapToNativeModel R n =
      (ConcreteCategory.hom (C := CGWH.{u, u})
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R))).comp
        (ConcreteCategory.hom (C := CGWH.{u, u})
          (SSet.toCGWH.{u, u}.map (nerveMap (finiteToStableCategoryMap R n).toFunctor))) := rfl

private theorem finiteNativeSuccessorMap_recipe (R : Type u) [Ring R] (n : ℕ) :
    (finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) =
      SSet.toCGWH.{u, u}.map (nerveMap
        (((finiteClassifyingCategoryDiagram R).map
          (homOfLE (Nat.le_add_right n 1))).toFunctor)) := rfl

/-- The WHOLE original right-unit difference is null by its DERIVED perfect
inactive family. No pointwise contraction or chosen factor is supplied. -/
public theorem independentBGLRightUnitDifferenceMappingPath_null
    (R : Type u) [Ring R] (n : ℕ) :
    (independentBGLRightUnitDifferenceMappingPath R n).Homotopic
      (Path.refl (independentBGLFiniteMapToNativeModel R n)) := by
  have hpath : independentBGLRightUnitDifferenceMappingPath R n =
      independentBGLInactiveNaturalLoopMappingPath R (rightUnitCommonRank_bound.{u} n)
        (rightUnitDifferencePerfectFactor R n) := by
    apply Path.ext
    funext t
    apply ContinuousMap.ext
    intro a
    have hRight := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R n)
        (independentBGLFiniteMapToNativeModel R n) => p t a) (rightDifferencePath_recipe R n)
    have hInactive := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R n)
        (independentBGLFiniteMapToNativeModel R n) => p t a) (rightInactivePath_recipe R n)
    have hNative := NatTrans.nativeNerveMappingPathPostcomp_congr_apply
      (finiteRightUnitDifferenceLoop R n)
      (finiteInactiveClassifyingLoop R (rightUnitCommonRank_bound.{u} n)
        (rightUnitDifferencePerfectFactor R n))
      (congrArg NatTrans.nerveHomotopyMap (finiteRightUnitDifferenceLoop_eq_inactive R n))
      (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R)) t a
    exact hRight.trans (hNative.trans hInactive.symm)
  obtain ⟨H⟩ := independentBGLInactiveNaturalLoopMappingPath_null R
    (rightUnitCommonRank_bound.{u} n) (rightUnitDifferencePerfectFactor R n)
  exact ⟨Path.Homotopy.cast H hpath.symm rfl⟩

/-- Both COMPLETE consecutive original right-unit paths are homotopic
with BOTH original endpoint maps fixed. -/
public theorem independentBGLRightUnitMappingPaths_homotopic
    (R : Type u) [Ring R] (n : ℕ) :
    (independentBGLRightUnitMappingPath R n).Homotopic
      (independentBGLNextRightUnitMappingPath R n) := by
  obtain ⟨HNull⟩ := independentBGLRightUnitDifferenceMappingPath_null R n
  have hTarget : Path.refl (independentBGLFiniteMapToNativeModel R n) =
      Path.refl ((ConcreteCategory.hom (C := CGWH.{u, u})
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R))).comp
        (ConcreteCategory.hom (C := CGWH.{u, u})
          (SSet.toCGWH.{u, u}.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)))) := by
    apply Path.ext
    funext t
    exact finiteModelMap_recipe R n
  have hNull :
      (NatTrans.nativeNerveMappingPathPostcomp
        ((finiteRightBlockUnitIso R n).hom ≫ (finiteNextRightBlockUnitIso R n).inv)
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R))).Homotopic
        (Path.refl ((ConcreteCategory.hom (C := CGWH.{u, u})
          (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
            (independentBGLCellPoint R))).comp
          (ConcreteCategory.hom (C := CGWH.{u, u})
            (SSet.toCGWH.{u, u}.map (nerveMap (finiteToStableCategoryMap R n).toFunctor))))) :=
    ⟨Path.Homotopy.cast HNull (rightDifferencePath_recipe R n) hTarget⟩
  obtain ⟨H⟩ := NatTrans.nativeNerveMappingPathPostcomp_homotopic_of_difference_null
    (finiteRightBlockUnitIso R n).hom (finiteNextRightBlockUnitIso R n)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)) hNull
  exact ⟨Path.Homotopy.cast H (rightUnitPath_recipe R n).symm
    (nextRightUnitPath_recipe R n).symm⟩

/-- The actual next right-unit family is the LITERAL restriction of its
original next-stage family, at EVERY clock and original source point. -/
public theorem independentBGLNextRightUnitMappingPath_restriction_apply
    (R : Type u) [Ring R] (n : ℕ) (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) :
    independentBGLNextRightUnitMappingPath R n t a =
      independentBGLRightUnitMappingPath R (n + 1) t
        ((finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) a) := by
  let I := ((finiteClassifyingCategoryDiagram R).map
    (homOfLE (Nat.le_add_right n 1))).toFunctor
  let α := (finiteRightBlockUnitIso R (n + 1)).hom
  let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
    (independentBGLCellPoint R)
  have hc : NatTrans.nerveHomotopyMap (finiteNextRightBlockUnitIso R n).hom =
      NatTrans.nerveHomotopyMap (Functor.whiskerLeft I α) :=
    (finiteNextRightBlockUnitIso_nerveHomotopyMap_restriction R n).trans
      (NatTrans.nerveHomotopyMap_precomp I α)
  have hNext := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteRightBlockMapToNativeModel R n) => p t a) (nextRightUnitPath_recipe R n)
  have hSuccessor : (finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) a =
      SSet.toCGWH.{u, u}.map (nerveMap I) a :=
    ConcreteCategory.congr_hom (finiteNativeSuccessorMap_recipe R n) a
  have hNative := (NatTrans.nativeNerveMappingPathPostcomp_congr_apply
    (finiteNextRightBlockUnitIso R n).hom (Functor.whiskerLeft I α) hc q t a).trans
      (NatTrans.nativeNerveMappingPathPostcomp_precomp_apply I α q t a)
  have hPath := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R (n + 1))
      (independentBGLFiniteRightBlockMapToNativeModel R (n + 1)) =>
    p t (SSet.toCGWH.{u, u}.map (nerveMap I) a)) (rightUnitPath_recipe R (n + 1))
  exact hNext.trans (hNative.trans (hPath.symm.trans
    (congrArg (fun b : CategoryTheory.groupClassifyingNative.{u, u}
        (Matrix.GeneralLinearGroup (Fin (n + 1)) R) =>
      independentBGLRightUnitMappingPath R (n + 1) t b) hSuccessor.symm)))

/-- The ENTIRE original zero-stage right-unit path is literally constant
at every original active point and every time. -/
public theorem independentBGLRightUnitMappingPath_zero_stage_apply
    (R : Type u) [Ring R] (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)) :
    independentBGLRightUnitMappingPath R 0 t a = independentBGLFiniteMapToNativeModel R 0 a := by
  have hPath := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R 0)
      (independentBGLFiniteRightBlockMapToNativeModel R 0) => p t a) (rightUnitPath_recipe R 0)
  have hNative := NatTrans.nativeNerveMappingPathPostcomp_apply_of_fst_cylinder
    (finiteRightBlockUnitIso R 0).hom (finiteRightUnitZeroCylinder_eq R)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)) t a
  have hMap := congrArg (fun F : C(CategoryTheory.groupClassifyingNative.{u, u}
      (Matrix.GeneralLinearGroup (Fin 0) R),
        TopCat.nativeSingularSpace (independentBGLCellTarget R)) => F a)
    (finiteModelMap_recipe R 0)
  exact hPath.trans (hNative.trans hMap.symm)

end AlgebraicKTheory.StableGL

end
