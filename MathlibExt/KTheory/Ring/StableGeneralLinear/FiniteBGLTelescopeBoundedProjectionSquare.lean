/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeBoundedRowFamily
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescopeFundamentalGroup

/-!
# The original bounded telescope projection square

The original finite-to-stable cocone retains the target-rank matrix label
of every bounded telescope arrow. The original bounded projection followed
by rank-n stable inclusion is therefore the original telescope projection.
The strict ordinary square identifies the actual terminal map of the whole
bounded row family with that same original projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial

universe u

namespace AlgebraicKTheory.StableGL

section Semiring

variable (R : Type u) [Semiring R]

/-- Every original bounded arrow has the same actual stable finite-stage
label under the original bounded and telescope projections. -/
public theorem finiteBGLTelescopeBoundedProjectionToStableFunctor (n : ℕ) :
    finiteBGLTelescopeBoundedInclusion R n ⋙ finiteBGLTelescopeToStableCategory R =
      finiteBGLTelescopeBoundedProjection R n ⋙ (finiteToStableCategoryMap R n).toFunctor := by
  let L := finiteBGLTelescopeBoundedInclusion R n ⋙ finiteBGLTelescopeToStableCategory R
  let M := finiteBGLTelescopeBoundedProjection R n ⋙ (finiteToStableCategoryMap R n).toFunctor
  have hObj (X : FiniteBGLTelescopeBoundedCategory R n) : L.obj X = M.obj X := rfl
  refine Functor.hext hObj ?_
  intro X Y a
  apply heq_of_eq
  let q : Y.obj.base ⟶ n := homOfLE Y.property
  let D := finiteClassifyingCategoryDiagram R
  have hNat := congrArg Cat.Hom.toFunctor (finiteToStableCategoryMap_naturality R q)
  let hSource := Functor.congr_obj hNat
    ((D.map a.hom.base).toFunctor.obj X.obj.fiber)
  let hTarget := Functor.congr_obj hNat Y.obj.fiber
  have hMap := Functor.congr_hom hNat a.hom.fiber
  have hRaw : HEq
      ((D.map q ≫ finiteToStableCategoryMap R n).toFunctor.map a.hom.fiber)
      ((finiteToStableCategoryMap R Y.obj.base).toFunctor.map a.hom.fiber) :=
    (conj_eqToHom_iff_heq _ _ hSource hTarget).1 hMap
  have hRaw' : HEq
      ((finiteToStableCategoryMap R n).toFunctor.map
        ((D.map q).toFunctor.map a.hom.fiber))
      ((finiteToStableCategoryMap R Y.obj.base).toFunctor.map a.hom.fiber) := hRaw
  have hDiagram : (D.map q).toFunctor.map a.hom.fiber =
      (finiteOppositeMonoidDiagram R).map q a.hom.fiber :=
    (finiteClassifyingCategoryDiagram_map_map R q a.hom.fiber).trans
      (finiteOppositeMonoidDiagram_map_apply R q a.hom.fiber).symm
  have hLeft : L.map a =
      (finiteToStableCategoryMap R Y.obj.base).toFunctor.map
        (X := ((D.map a.hom.base).toFunctor.obj X.obj.fiber))
        (Y := Y.obj.fiber) a.hom.fiber := by rfl
  have hRight : M.map a =
      (finiteToStableCategoryMap R n).toFunctor.map
        (X := (finiteBGLTelescopeBoundedProjection R n).obj X)
        (Y := (finiteBGLTelescopeBoundedProjection R n).obj Y)
        ((finiteOppositeMonoidDiagram R).map q a.hom.fiber) :=
    congrArg (fun z : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ =>
      (finiteToStableCategoryMap R n).toFunctor.map
        (X := (finiteBGLTelescopeBoundedProjection R n).obj X)
        (Y := (finiteBGLTelescopeBoundedProjection R n).obj Y) z)
      (finiteBGLTelescopeBoundedProjection_map_label R n a)
  have hValues :
      (finiteToStableCategoryMap R Y.obj.base).toFunctor.map
        (X := ((D.map a.hom.base).toFunctor.obj X.obj.fiber))
        (Y := Y.obj.fiber) a.hom.fiber =
      (finiteToStableCategoryMap R n).toFunctor.map
        (X := (finiteBGLTelescopeBoundedProjection R n).obj X)
        (Y := (finiteBGLTelescopeBoundedProjection R n).obj Y)
        ((finiteOppositeMonoidDiagram R).map q a.hom.fiber) :=
    (eq_of_heq hRaw').symm.trans
      (congrArg (fun z : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ =>
        (finiteToStableCategoryMap R n).toFunctor.map
          (X := (finiteBGLTelescopeBoundedProjection R n).obj X)
          (Y := (finiteBGLTelescopeBoundedProjection R n).obj Y) z) hDiagram)
  exact hLeft.trans (hValues.trans hRight.symm)

/-- The same original bounded functor square is literal on the whole nerves. -/
public theorem finiteBGLTelescopeBoundedProjectionToStableNerve (n : ℕ) :
    nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
        finiteBGLTelescopeNerveToStableNerve R =
      nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
        nerveMap (finiteToStableCategoryMap R n).toFunctor := by
  calc
    _ = nerveMap (finiteBGLTelescopeBoundedInclusion R n ⋙
        finiteBGLTelescopeToStableCategory R) :=
      nerveMap_comp (finiteBGLTelescopeBoundedInclusion R n)
        (finiteBGLTelescopeToStableCategory R)
    _ = nerveMap (finiteBGLTelescopeBoundedProjection R n ⋙
        (finiteToStableCategoryMap R n).toFunctor) :=
      congrArg nerveMap (finiteBGLTelescopeBoundedProjectionToStableFunctor R n)
    _ = _ := (nerveMap_comp (finiteBGLTelescopeBoundedProjection R n)
      (finiteToStableCategoryMap R n).toFunctor).symm

/-- The strict ordinary square uses the actual original telescope
projection and the actual original bounded and finite-stage maps. -/
public theorem finiteBGLTelescopeBoundedProjectionToStableTop (n : ℕ) :
    SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) ≫
        ordinaryFiniteBGLTelescopeToBGL R =
      SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) ≫
        SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) := by
  let a := nerveMap (finiteBGLTelescopeBoundedInclusion R n)
  let b := nerveMap (finiteBGLTelescopeBoundedProjection R n)
  let p := finiteBGLTelescopeNerveToStableNerve R
  let i := nerveMap (finiteToStableCategoryMap R n).toFunctor
  change SSet.toTop.map a ≫ SSet.toTop.map p = SSet.toTop.map b ≫ SSet.toTop.map i
  exact (SSet.toTop.map_comp a p).symm.trans
    ((congrArg (fun f => SSet.toTop.map f)
      (finiteBGLTelescopeBoundedProjectionToStableNerve R n)).trans
        (SSet.toTop.map_comp b i))

end Semiring

section Ring

variable (R : Type u) [Ring R]

/-- The whole original bounded row map reaches the original telescope
projection followed by the same original stable-row comparison. -/
public def finiteBGLTelescopeBoundedOriginalStableRowHomotopy (n : ℕ) :
    TopCat.Homotopy
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) ≫
        finiteBGLTelescopeToRowZeroComponentTop R)
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) ≫
        ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R) := by
  let H := finiteBGLTelescopeBoundedStableRowHomotopy R n
  have hEnd :
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) ≫
        SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
          finiteFreeRowStableZeroComparison R).hom =
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) ≫
        ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (finiteFreeRowStableZeroComparison R)
      (ConcreteCategory.congr_hom (finiteBGLTelescopeBoundedProjectionToStableTop R n).symm x)
  exact H.cast rfl hEnd

end Ring

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The WHOLE ORIGINAL bounded initial telescope/stable family is fixed
on the SAME original rank-zero row vertex for EVERY interval time. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowHomotopy_zero_root
    (t : unitInterval) :
    let c : FiniteBGLTelescopeBoundedCategory R 0 :=
      ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
    (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R 0).toContinuousMap
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _))) := by
  change
    (finiteBGLTelescopeBoundedStableRowHomotopy R 0).toContinuousMap
        (t, SSet.realizedVertex (ComposableArrows.mk₀
          (⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩ :
            FiniteBGLTelescopeBoundedCategory R 0))) = _
  exact finiteBGLTelescopeBoundedStableRowHomotopy_zero_root R t

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The WHOLE original204 telescope/stable comparison families retain
their actual endpoint casts while the COMPLETE original adjacent stable
prism/backtrack family fixes BOTH entire original endpoint faces. -/
public def finiteBGLTelescopeBoundedOriginalStableRowPrismHomotopy (n : ℕ) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun X hX => hX.trans (Nat.le_succ n))
    ContinuousMap.HomotopyRel
      ((finiteBGLTelescopeBoundedOriginalStableRowHomotopy R (n + 1)).compContinuousMap
         (SSet.toTop.map (nerveMap B)).hom).toContinuousMap
      (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R n).toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R n)) => z.1 = 0 ∨ z.1 = 1)) := by
  change
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun X hX => hX.trans (Nat.le_succ n))
    ContinuousMap.HomotopyRel
      ((finiteBGLTelescopeBoundedStableRowHomotopy R (n + 1)).compContinuousMap
        (SSet.toTop.map (nerveMap B)).hom).toContinuousMap
      (finiteBGLTelescopeBoundedStableRowHomotopy R n).toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R n)) => z.1 = 0 ∨ z.1 = 1))
  exact finiteBGLTelescopeBoundedStableRowPrismHomotopy R n

end AlgebraicKTheory.StableGL

end
