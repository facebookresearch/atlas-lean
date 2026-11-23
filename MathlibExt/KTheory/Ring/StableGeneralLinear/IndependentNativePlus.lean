/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeInactiveFamily
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusPoint
public import MathlibExt.AlgebraicTopology.PlusConstruction.HomotopyEquivSquare
public import MathlibExt.AlgebraicTopology.PlusConstruction.NativeProduct

/-!
# The ORIGINAL independent BGL plus map in its actual native model

The original cell inclusion is followed by its DERIVED pointed singular
inverse. The actual source Iso, actual inverse family and actual point
triangle transfer its all-integer comparison and exact kernel. Normality
and perfectness of the original pulled subgroup are derived. No native
plus or target H-space data is input.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace AlgebraicKTheory.StableGL

private local instance actualCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

attribute [local instance] independentBGLCellPoint_cofibration

/-- The SAME original cell inclusion followed by its DERIVED pointed native inverse. -/
public abbrev independentBGLNativeInclusion (R : Type u) [Ring R] :
    BGL.{u} R ⟶ TopCat.nativeSingularSpace (independentBGLCellTarget R) :=
  originalBGLToPlusNativeModel R (independentBGLCellInclusion R) (independentBGLCellPoint R)

private theorem independentBGLNativeInclusion_eq_recipe (R : Type u) [Ring R] :
    independentBGLNativeInclusion R =
      originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) := rfl

private theorem independentBGLNativeSourcePointCofibration_eq_native (R : Type u) [Ring R] :
    Cofibration (TopCat.const (BGLBasepoint.{u} R) :
      TopCat.of PUnit.{u + 1} ⟶ (BGL.{u} R).toTop) =
    Cofibration (TopCat.const (CategoryTheory.groupClassifyingNativePoint.{u, u} (StableGL R)) :
      TopCat.of PUnit.{u + 1} ⟶
        (CategoryTheory.groupClassifyingNative.{u, u} (StableGL R)).toTop) := by
  rw [CategoryTheory.groupClassifyingNativePoint_eq_categoryPoint.{u, u}]
  rfl

private theorem independentBGLNativeInclusion_top_formula (R : Type u) [Ring R] :
    (CGWH.cgwhToTop.map (independentBGLNativeInclusion R)).hom =
      (TopCat.nativeSingularPointModelOfCofibrantPoint
        (independentBGLCellTarget R) (independentBGLCellPoint R)).equiv.invFun.comp
          ((BGLToOrdinaryTopIso.{u} R).hom ≫ independentBGLCellInclusion R).hom := by
  rw [independentBGLNativeInclusion_eq_recipe]
  rfl

/-- The ORIGINAL native BGL point has a structural point cofibration. -/
public theorem independentBGLNativeSourcePoint_cofibration (R : Type u) [Ring R] :
    Cofibration (TopCat.const (BGLBasepoint.{u} R) :
      TopCat.of PUnit.{u + 1} ⟶ (BGL.{u} R).toTop) := by
  exact Eq.mp (independentBGLNativeSourcePointCofibration_eq_native R).symm
    (CategoryTheory.groupClassifyingNative_pointMap_cofibration.{u, u} (StableGL R))

/-- The actual native source remains path connected. -/
public theorem independentBGLNativeSource_pathConnected (R : Type u) [Ring R] :
    PathConnectedSpace (BGL.{u} R) :=
  CategoryTheory.groupClassifyingNative_pathConnected.{u, u} (StableGL R)

/-- The native model of the SAME constructed target is actually path connected. -/
public theorem independentBGLNativeTarget_pathConnected (R : Type u) [Ring R] :
    PathConnectedSpace (TopCat.nativeSingularSpace (independentBGLCellTarget R)) := by
  letI := independentBGLCellTarget_pathConnected R
  exact TopCat.nativeSingularSpace_pathConnected (independentBGLCellTarget R) (independentBGLCellPoint R)

/-- The original marked source point maps to the SAME original native model vertex. -/
public theorem independentBGLNativeInclusion_point (R : Type u) [Ring R] :
    independentBGLNativeInclusion R (BGLBasepoint R) =
      TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  rw [independentBGLNativeInclusion_eq_recipe]
  exact originalBGLToPlusNativeModel_point R (independentBGLCellInclusion R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)

/-- The original prescribed subgroup pulled through the ORIGINAL native/ordinary source Iso. -/
public abbrev independentBGLNativeSubgroup (R : Type u) [Ring R] :
    Subgroup (FundamentalGroup (BGL.{u} R) (BGLBasepoint R)) :=
  (BGLPlusSubgroup R).comap (FundamentalGroup.mapOfEq
    (BGLToOrdinaryTopIso.{u} R).hom.hom (BGLToOrdinaryTopIso_hom_basepoint R))

/-- The actual native map is PLUS on its ORIGINAL pulled prescribed subgroup.
Its normality, perfectness, all-integer comparison and exact kernel follow
from the original cell plus and the ACTUAL point-relative inverse family. -/
public theorem independentBGLNativeInclusion_isPlus (R : Type u) [Ring R] :
    let P := independentBGLNativeSubgroup R
    ∃ hN : P.Normal, ∃ hP : Group.IsPerfect P,
      letI := hN
      letI := hP
      @TopCat.IsPlusConstructionAt.{u} (BGL.{u} R).toTop
        (TopCat.nativeSingularSpace (independentBGLCellTarget R)).toTop
        (CGWH.cgwhToTop.map (independentBGLNativeInclusion R))
        (BGLBasepoint R)
        (TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R))
        (independentBGLNativeInclusion_point R) P hN hP := by
  let Y := independentBGLCellTarget R
  let y := independentBGLCellPoint R
  let i := independentBGLCellInclusion R
  let N := TopCat.nativeSingularPointModelOfCofibrantPoint Y y
  let q := independentBGLNativeInclusion R
  let F := CGWH.cgwhToTop.map q
  let S := (BGLToOrdinaryTopIso.{u} R).hom
  let T := TopCat.ofHom N.equiv.toFun
  letI : PathConnectedSpace Y := independentBGLCellTarget_pathConnected R
  letI : PathConnectedSpace (TopCat.nativeSingularSpace Y) := independentBGLNativeTarget_pathConnected R
  have hF : F.hom = N.equiv.invFun.comp (S ≫ i).hom :=
    independentBGLNativeInclusion_top_formula R
  have hT : T.hom = N.equiv.toFun := TopCat.hom_ofHom N.equiv.toFun
  have hAssoc : N.equiv.toFun.comp (N.equiv.invFun.comp (S ≫ i).hom) =
      (N.equiv.toFun.comp N.equiv.invFun).comp (S ≫ i).hom := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hFT : (F ≫ T).hom =
      (N.equiv.toFun.comp N.equiv.invFun).comp (S ≫ i).hom :=
    (TopCat.hom_comp F T).trans
      ((congrArg₂ ContinuousMap.comp hT hF).trans hAssoc)
  let H : ContinuousMap.Homotopy (F ≫ T).hom (S ≫ i).hom :=
    (N.rightFamily.toHomotopy.compContinuousMap (S ≫ i).hom).cast
      hFT.symm
      (by apply ContinuousMap.ext; intro z; rfl)
  exact (independentBGLCellInclusion_isPlus R).of_sourceIso_targetEquiv_homotopySquare
    (BGLToOrdinaryTopIso.{u} R) N.equiv H
    (BGLBasepoint R) (TopCat.nativeSingularPoint Y y) (ordinaryBGLBasepoint R) y
    (independentBGLNativeInclusion_point R) (BGLToOrdinaryTopIso_hom_basepoint R)
    N.forwardPoint (independentBGLCellInclusion_point R) (BGLPlusSubgroup R)

/-- The native target fundamental group at the ORIGINAL unit is commutative,
derived from the original plus quotient before any multiplication is constructed. -/
public theorem independentBGLNativeTarget_fundamentalGroup_isMulCommutative
    (R : Type u) [Ring R] :
    IsMulCommutative (FundamentalGroup
      (TopCat.nativeSingularSpace (independentBGLCellTarget R))
      (TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R))) := by
  letI : IsMulCommutative (FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R)) :=
    ordinaryBGL_plus_fundamentalGroup_isMulCommutative R (independentBGLCellInclusion_isPlus R)
  exact (TopCat.nativeSingularPointModelOfCofibrantPoint
    (independentBGLCellTarget R) (independentBGLCellPoint R)).fundamentalGroup_isMulCommutative

end AlgebraicKTheory.StableGL

end
