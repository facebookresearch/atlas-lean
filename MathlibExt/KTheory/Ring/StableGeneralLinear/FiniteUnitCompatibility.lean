/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentInactiveFamily
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingCofibration
public import MathlibExt.CategoryTheory.NerveCGWHMappingPath
public import MathlibExt.Topology.Category.CGWH.CompactOpenPathHomotopy

/-!
# Whole consecutive finite unit homotopies in the independent plus target

The original consecutive comparison difference has already been placed
in its computed perfect inactive group. Its one whole filled square now
gives nullity in the RAW mapping space. The original chain two-simplices
and the actual next natural isomorphism then identify the two complete
unit paths. This returns a jointly continuous square on every original
finite classifying source, with all four original faces, for every ring.
It does not yet assert that a compatible infinite-stage family was chosen.
-/

set_option autoImplicit false

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

private local instance finiteNativeSourceHausdorff (R : Type u) [Ring R] (n : ℕ) :
    T2Space (CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) := by
  letI : T2Space (CategoryTheory.groupClassifyingOrdinary
      (Matrix.GeneralLinearGroup (Fin n) R)) :=
    SSet.realization_t2Space
      (CategoryTheory.groupClassifyingNerve (Matrix.GeneralLinearGroup (Fin n) R))
  exact (TopCat.homeoOfIso (CategoryTheory.groupClassifyingToTopIso.{u, u}
    (Matrix.GeneralLinearGroup (Fin n) R))).symm.t2Space

/-- The original finite-stage inclusion followed by the SAME independent
cell plus and its derived pointed native model inverse. -/
public abbrev independentBGLFiniteMapToNativeModel (R : Type u) [Ring R] (n : ℕ) :
    C(CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R),
      TopCat.nativeSingularSpace (independentBGLCellTarget R)) :=
  (ConcreteCategory.hom (C := CGWH.{u, u})
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))).comp
    (ConcreteCategory.hom (C := CGWH.{u, u})
      (SSet.toCGWH.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)))

/-- The original first block map on the same finite stage and target. -/
public abbrev independentBGLFiniteLeftBlockMapToNativeModel
    (R : Type u) [Ring R] (n : ℕ) :
    C(CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R),
      TopCat.nativeSingularSpace (independentBGLCellTarget R)) :=
  (ConcreteCategory.hom (C := CGWH.{u, u})
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))).comp
    (ConcreteCategory.hom (C := CGWH.{u, u})
      (SSet.toCGWH.map (nerveMap
        ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R))))

/-- The entire old original finite unit comparison as one mapping-space path. -/
public abbrev independentBGLLeftUnitMappingPath (R : Type u) [Ring R] (n : ℕ) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteLeftBlockMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteLeftBlockUnitIso R n).hom
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

/-- The entire NEXT comparison, restricted to the original finite stage. -/
public abbrev independentBGLNextLeftUnitMappingPath (R : Type u) [Ring R] (n : ℕ) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteLeftBlockMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteNextLeftBlockUnitIso R n).hom
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

/-- The original whole comparison difference, in the SAME mapping space. -/
public abbrev independentBGLLeftUnitDifferenceMappingPath
    (R : Type u) [Ring R] (n : ℕ) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteLeftUnitDifferenceLoop R n)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

private theorem finiteModelMap_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLFiniteMapToNativeModel R n =
      (ConcreteCategory.hom (C := CGWH.{u, u})
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R))).comp
        (ConcreteCategory.hom (C := CGWH.{u, u})
          (SSet.toCGWH.{u, u}.map (nerveMap (finiteToStableCategoryMap R n).toFunctor))) := rfl

private theorem leftUnitMappingPath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLLeftUnitMappingPath R n =
      NatTrans.nativeNerveMappingPathPostcomp (finiteLeftBlockUnitIso R n).hom
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem nextLeftUnitMappingPath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLNextLeftUnitMappingPath R n =
      NatTrans.nativeNerveMappingPathPostcomp (finiteNextLeftBlockUnitIso R n).hom
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem differenceMappingPath_recipe (R : Type u) [Ring R] (n : ℕ) :
    independentBGLLeftUnitDifferenceMappingPath R n =
      NatTrans.nativeNerveMappingPathPostcomp (finiteLeftUnitDifferenceLoop R n)
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem finiteNativeSuccessorMap_recipe (R : Type u) [Ring R] (n : ℕ) :
    (finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) =
      SSet.toCGWH.{u, u}.map (nerveMap
        (((finiteClassifyingCategoryDiagram R).map
          (homOfLE (Nat.le_add_right n 1))).toFunctor)) := rfl

/-- The complete original zero-stage unit path is constant at EVERY
original source point and EVERY time, by the empty doubled conjugator. -/
public theorem independentBGLLeftUnitMappingPath_zero_stage_apply
    (R : Type u) [Ring R] (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin 0) R)) :
    independentBGLLeftUnitMappingPath R 0 t a = independentBGLFiniteMapToNativeModel R 0 a := by
  have hPath := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R 0)
      (independentBGLFiniteLeftBlockMapToNativeModel R 0) => p t a)
    (leftUnitMappingPath_recipe R 0)
  have hCylinder := NatTrans.nativeNerveMappingPathPostcomp_apply_of_fst_cylinder
    (finiteLeftBlockUnitIso R 0).hom (finiteLeftUnitZeroCylinder_eq R)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)) t a
  have hMap := congrArg (fun F : C(CategoryTheory.groupClassifyingNative.{u, u}
      (Matrix.GeneralLinearGroup (Fin 0) R),
        TopCat.nativeSingularSpace (independentBGLCellTarget R)) => F a)
    (finiteModelMap_recipe R 0)
  exact hPath.trans (hCylinder.trans hMap.symm)

/-- The mapping-space loop retains the entire ORIGINAL difference cylinder,
at every original parameter and every original active point. -/
public theorem independentBGLLeftUnitDifferenceMappingPath_apply
    (R : Type u) [Ring R] (n : ℕ) (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) :
    independentBGLLeftUnitDifferenceMappingPath R n t a =
      independentBGLLeftUnitDifferenceNativeCylinder R n
        (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)) := by
  let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
    (independentBGLCellPoint R)
  let e := (SSet.realizationTensorIsoCGWH.{u, u}
    (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
      (Δ[1] : SSet.{u})).inv
  let p := SSet.toCGWH.{u, u}.map
    (NatTrans.nerveHomotopyMap (finiteLeftUnitDifferenceLoop R n))
  let z := CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)
  have hPath := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteMapToNativeModel R n) => p t a)
    (differenceMappingPath_recipe R n)
  calc
    independentBGLLeftUnitDifferenceMappingPath R n t a = q ((e ≫ p) z) :=
      hPath.trans
        (NatTrans.nativeNerveMappingPathPostcomp_apply (finiteLeftUnitDifferenceLoop R n) q t a)
    _ = ((e ≫ p) ≫ q) z := (ConcreteCategory.comp_apply _ _ _).symm
    _ = independentBGLLeftUnitDifferenceNativeCylinder R n z :=
      ConcreteCategory.congr_hom (Category.assoc e p q) z

/-- The DERIVED one whole perfect-family filler makes the ORIGINAL entire
unit difference null in its compact-open mapping space. No filler or
pointwise nullity witness is a caller input. -/
public theorem independentBGLLeftUnitDifferenceMappingPath_null
    (R : Type u) [Ring R] (n : ℕ) :
    (independentBGLLeftUnitDifferenceMappingPath R n).Homotopic
      (Path.refl (independentBGLFiniteMapToNativeModel R n)) := by
  obtain ⟨K, h₀, h₁, hsource, htarget⟩ :=
    exists_independentBGLLeftUnitDifferenceNativeCylinder_filler R n
  have hfixed (a : CategoryTheory.groupClassifyingNative.{u, u}
      (Matrix.GeneralLinearGroup (Fin n) R)) :
      independentBGLInactiveFamilyToNativeModel R (leftUnitCommonRank_bound.{u} n)
        (CGWH.tensorMk a (CategoryTheory.groupClassifyingNativePoint.{u, u}
          (LeftUnitDifferencePerfectGroup R n))) =
        independentBGLFiniteMapToNativeModel R n a := by
    have hp := independentBGLLeftUnitDifferenceMappingPath_apply R n 0 a
    have hs := congrArg (fun f : C(CategoryTheory.groupClassifyingNative.{u, u}
      (Matrix.GeneralLinearGroup (Fin n) R),
        TopCat.nativeSingularSpace (independentBGLCellTarget R)) => f a)
          (independentBGLLeftUnitDifferenceMappingPath R n).source
    exact (hsource 0 a).symm.trans ((h₀ 0 a).trans (hp.symm.trans hs))
  apply CGWH.mappingSpaceLoop_homotopic_refl_of_square (independentBGLLeftUnitDifferenceMappingPath R n) K
  · intro s a
    exact (h₀ s a).trans (independentBGLLeftUnitDifferenceMappingPath_apply R n s a).symm
  · intro s a
    exact (h₁ s a).trans (hfixed a)
  · intro t a
    exact (hsource t a).trans (hfixed a)
  · intro t a
    exact (htarget t a).trans (hfixed a)

/-- The two complete original consecutive unit paths are endpoint-fixed
homotopic on the WHOLE finite source, over every unchanged ring. -/
public theorem independentBGLLeftUnitMappingPaths_homotopic
    (R : Type u) [Ring R] (n : ℕ) :
    (independentBGLLeftUnitMappingPath R n).Homotopic
      (independentBGLNextLeftUnitMappingPath R n) := by
  obtain ⟨HNull⟩ := independentBGLLeftUnitDifferenceMappingPath_null R n
  have hNullTarget : Path.refl (independentBGLFiniteMapToNativeModel R n) =
      Path.refl ((ConcreteCategory.hom (C := CGWH.{u, u})
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R))).comp
        (ConcreteCategory.hom (C := CGWH.{u, u})
          (SSet.toCGWH.{u, u}.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)))) :=
    by
      apply Path.ext
      funext t
      exact finiteModelMap_recipe R n
  have hNull :
      (NatTrans.nativeNerveMappingPathPostcomp
        ((finiteLeftBlockUnitIso R n).hom ≫ (finiteNextLeftBlockUnitIso R n).inv)
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R))).Homotopic
        (Path.refl ((ConcreteCategory.hom (C := CGWH.{u, u})
          (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
            (independentBGLCellPoint R))).comp
          (ConcreteCategory.hom (C := CGWH.{u, u})
            (SSet.toCGWH.{u, u}.map (nerveMap (finiteToStableCategoryMap R n).toFunctor))))) :=
    ⟨Path.Homotopy.cast HNull (differenceMappingPath_recipe R n) hNullTarget⟩
  obtain ⟨H⟩ := NatTrans.nativeNerveMappingPathPostcomp_homotopic_of_difference_null
    (finiteLeftBlockUnitIso R n).hom (finiteNextLeftBlockUnitIso R n)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))
    hNull
  exact ⟨Path.Homotopy.cast H (leftUnitMappingPath_recipe R n).symm
    (nextLeftUnitMappingPath_recipe R n).symm⟩

/-- The next comparison is the LITERAL restriction of the actual next
stage path along the ORIGINAL native successor map, at every source point. -/
public theorem independentBGLNextLeftUnitMappingPath_restriction_apply
    (R : Type u) [Ring R] (n : ℕ) (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) :
    independentBGLNextLeftUnitMappingPath R n t a =
      independentBGLLeftUnitMappingPath R (n + 1) t
        ((finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) a) := by
  let I := ((finiteClassifyingCategoryDiagram R).map
    (homOfLE (Nat.le_add_right n 1))).toFunctor
  let α := (finiteLeftBlockUnitIso R (n + 1)).hom
  let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
    (independentBGLCellPoint R)
  have hc : NatTrans.nerveHomotopyMap (finiteNextLeftBlockUnitIso R n).hom =
      NatTrans.nerveHomotopyMap (Functor.whiskerLeft I α) :=
    (finiteNextLeftBlockUnitIso_nerveHomotopyMap_restriction R n).trans
      (NatTrans.nerveHomotopyMap_precomp I α)
  have hNext := congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteLeftBlockMapToNativeModel R n) => p t a)
    (nextLeftUnitMappingPath_recipe R n)
  have hSuccessor :
      (finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) a =
        SSet.toCGWH.{u, u}.map (nerveMap I) a :=
    ConcreteCategory.congr_hom (finiteNativeSuccessorMap_recipe R n) a
  calc
    independentBGLNextLeftUnitMappingPath R n t a =
        NatTrans.nativeNerveMappingPathPostcomp (Functor.whiskerLeft I α) q t a :=
      hNext.trans (NatTrans.nativeNerveMappingPathPostcomp_congr_apply
        (finiteNextLeftBlockUnitIso R n).hom (Functor.whiskerLeft I α) hc q t a)
    _ = NatTrans.nativeNerveMappingPathPostcomp α q t (SSet.toCGWH.map (nerveMap I) a) :=
      NatTrans.nativeNerveMappingPathPostcomp_precomp_apply I α q t a
    _ = independentBGLLeftUnitMappingPath R (n + 1) t
        (SSet.toCGWH.{u, u}.map (nerveMap I) a) :=
      (congrArg (fun p : Path (independentBGLFiniteMapToNativeModel R (n + 1))
          (independentBGLFiniteLeftBlockMapToNativeModel R (n + 1)) =>
        p t (SSet.toCGWH.{u, u}.map (nerveMap I) a))
        (leftUnitMappingPath_recipe R (n + 1))).symm
    _ = independentBGLLeftUnitMappingPath R (n + 1) t
        ((finiteBGLDiagram.{u} R).map (homOfLE (Nat.le_add_right n 1)) a) :=
      congrArg (fun x : CategoryTheory.groupClassifyingNative.{u, u}
          (Matrix.GeneralLinearGroup (Fin (n + 1)) R) =>
        independentBGLLeftUnitMappingPath R (n + 1) t x) hSuccessor.symm

/-- One actual jointly continuous square compares the two WHOLE finite
unit families, fixing both ORIGINAL source/target maps at every time and
every active point. The square is derived, rather than supplied. -/
public theorem exists_independentBGLLeftUnitComparisonSquare
    (R : Type u) [Ring R] (n : ℕ) :
    ∃ K : C((unitInterval × unitInterval) ×
        CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R),
          TopCat.nativeSingularSpace (independentBGLCellTarget R)),
      (∀ s a, K ((0, s), a) = independentBGLLeftUnitMappingPath R n s a) ∧
      (∀ s a, K ((1, s), a) = independentBGLNextLeftUnitMappingPath R n s a) ∧
      (∀ t a, K ((t, 0), a) = independentBGLFiniteMapToNativeModel R n a) ∧
      (∀ t a, K ((t, 1), a) = independentBGLFiniteLeftBlockMapToNativeModel R n a) := by
  obtain ⟨H⟩ := independentBGLLeftUnitMappingPaths_homotopic R n
  refine ⟨CGWH.compactOpenPathHomotopyEvaluation H, ?_, ?_, ?_, ?_⟩
  · exact CGWH.compactOpenPathHomotopyEvaluation_zero H
  · exact CGWH.compactOpenPathHomotopyEvaluation_one H
  · exact CGWH.compactOpenPathHomotopyEvaluation_source H
  · exact CGWH.compactOpenPathHomotopyEvaluation_target H

end AlgebraicKTheory.StableGL

end
