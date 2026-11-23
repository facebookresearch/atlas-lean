/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentNativePlus
public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeBlockSum
public import MathlibExt.KTheory.Ring.StableGeneralLinear.GlobalLeftUnitSource
public import MathlibExt.KTheory.Ring.StableGeneralLinear.GlobalRightUnitSource
public import MathlibExt.Topology.Category.CGWH.NativeIntervalHomotopy
public import MathlibExt.AlgebraicTopology.PlusConstruction.NativeMultiplication

/-!
# Actual multiplication on the native model of the independent BGL plus

The original whole block-sum multiplication is extended along the
DERIVED actual product-plus inclusion. Its killing condition comes
from the original perfect product subgroup and the derived target
fundamental-group commutativity. Both original global stage-compatible
unit families supply the axis triangles. Plus uniqueness then derives
both whole target unit families, fixing the original marked point.
The ring and the independently constructed cell plus are unchanged.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory Simplicial

universe u

namespace AlgebraicKTheory.StableGL

private local instance originalCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

private theorem nativeLeftAxis_sourceFamily (R : Type u) [Ring R] :
    Nonempty (ContinuousMap.HomotopyRel
      (CGWH.cgwhToTop.map (independentBGLNativeInclusion R)).hom
      (CGWH.cgwhToTop.map
        (CGWH.hspaceLeftUnitMap (BGL.{u} R) (nativeBGLBlockSum R) (BGLBasepoint R) ≫
          independentBGLNativeInclusion R)).hom {BGLBasepoint R}) := by
  let q := independentBGLNativeInclusion R
  obtain ⟨H, h0, h1, hp⟩ := exists_independentBGLGlobalRightUnitPointedNativeHomotopy R
  let K := CGWH.ordinaryPointRelativeHomotopyOfNativeInterval q
    (blockSumRightBGLMap R ≫ q) H h0 h1 (BGLBasepoint R)
    (fun s => (hp s).trans (independentBGLNativeInclusion_point R).symm)
  exact ⟨K.cast rfl (congrArg
    (fun k : BGL.{u} R ⟶ BGL.{u} R => (CGWH.cgwhToTop.map (k ≫ q)).hom)
      (nativeBGLBlockSum_leftUnitMap R).symm)⟩

private theorem nativeRightAxis_sourceFamily (R : Type u) [Ring R] :
    Nonempty (ContinuousMap.HomotopyRel
      (CGWH.cgwhToTop.map (independentBGLNativeInclusion R)).hom
      (CGWH.cgwhToTop.map
        (CGWH.hspaceRightUnitMap (BGL.{u} R) (nativeBGLBlockSum R) (BGLBasepoint R) ≫
          independentBGLNativeInclusion R)).hom {BGLBasepoint R}) := by
  let q := independentBGLNativeInclusion R
  obtain ⟨H, h0, h1, hp⟩ := exists_independentBGLGlobalLeftUnitPointedNativeHomotopy R
  let K := CGWH.ordinaryPointRelativeHomotopyOfNativeInterval q
    (blockSumLeftBGLMap R ≫ q) H h0 h1 (BGLBasepoint R)
    (fun s => (hp s).trans (independentBGLNativeInclusion_point R).symm)
  exact ⟨K.cast rfl (congrArg
    (fun k : BGL.{u} R ⟶ BGL.{u} R => (CGWH.cgwhToTop.map (k ≫ q)).hom)
      (nativeBGLBlockSum_rightUnitMap R).symm)⟩

/-- Over EVERY original ring, the SAME independently constructed BGL
plus has a derived native multiplication with BOTH whole point-relative
unit families and the ORIGINAL full block-sum source triangle. Neither
the multiplication, its killing condition, nor any comparison/model/unit
family is a caller premise. -/
public theorem exists_independentBGLNativeMultiplication (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let m := TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R)
    let q := independentBGLNativeInclusion R
    ∃ H : CGWH.HSpaceData M, H.e = m ∧
      Nonempty (ContinuousMap.HomotopyRel
        (CGWH.cgwhToTop.map ((q ⊗ₘ q) ≫ H.mul)).hom
        (CGWH.cgwhToTop.map (nativeBGLBlockSum R ≫ q)).hom
          {CGWH.tensorMk (BGLBasepoint R) (BGLBasepoint R)}) := by
  let K : SSet.{u} := classifyingNerve R
  letI : K.IsConnected := CategoryTheory.groupClassifyingNerve_isConnected (StableGL R)
  letI : PathConnectedSpace (SSet.toCGWH.{u, u}.obj K) :=
    SSet.pathConnectedSpace_realization_of_isConnected K
  letI : PathConnectedSpace (BGL.{u} R) := independentBGLNativeSource_pathConnected R
  letI : PathConnectedSpace (TopCat.nativeSingularSpace (independentBGLCellTarget R)) :=
    independentBGLNativeTarget_pathConnected R
  letI : IsMulCommutative (FundamentalGroup
      (TopCat.nativeSingularSpace (independentBGLCellTarget R))
      (TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R))) :=
    independentBGLNativeTarget_fundamentalGroup_isMulCommutative R
  obtain ⟨hN, hP, hq⟩ := independentBGLNativeInclusion_isPlus R
  letI : (independentBGLNativeSubgroup R).Normal := hN
  letI : Group.IsPerfect (independentBGLNativeSubgroup R) := hP
  exact @CGWH.exists_hSpaceData_of_realized_plus.{u}
    (classifyingNerve R) (TopCat.toSSet.obj (independentBGLCellTarget R))
    (inferInstance : PathConnectedSpace (SSet.toCGWH.{u, u}.obj (classifyingNerve R)))
    (inferInstance : PathConnectedSpace
      (SSet.toCGWH.{u, u}.obj (TopCat.toSSet.obj (independentBGLCellTarget R))))
    (ComposableArrows.mk₀ (SingleObj.star ((StableGL R)ᵐᵒᵖ)))
    (TopCat.toSSetObj₀Equiv.symm (independentBGLCellPoint R))
    (independentBGLNativeInclusion R) (independentBGLNativeInclusion_point.{u, u} R)
    (independentBGLNativeSubgroup R) hN hP hq
    (inferInstance : IsMulCommutative (FundamentalGroup
      (SSet.toCGWH.{u, u}.obj (TopCat.toSSet.obj (independentBGLCellTarget R)))
      (SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm (independentBGLCellPoint R)))))
    (nativeBGLBlockSum R) (nativeBGLBlockSum_point R)
    (nativeLeftAxis_sourceFamily.{u, u, u} R) (nativeRightAxis_sourceFamily.{u, u, u} R)

end AlgebraicKTheory.StableGL

end
