/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.Group
public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMappingGeometry
public import MathlibExt.Topology.CWComplex.NativeSingularModel
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatWeakLocalCoefficients
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalence
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality

/-!
# A genuine auxiliary plus map for a perfect inactive group

The original ordinary group classifying space receives the independently
constructed two/three-cell plus map on its whole perfect fundamental group.
Its actual inclusion and vertex Cofibrations derive the selected point
Cofibration of the target. The existing pointed singular-model inverse then
provides a native CW target, with both original point-relative families.

The native plus map is the original canonical source comparison followed
by the SAME cell inclusion and that derived inverse. Its all-integer
comparison and exact whole-group kernel are proved for this literal map.
No plus, model, inverse, acyclicity or kernel witness is a caller input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra AlgebraicTopology
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace CategoryTheory

public local instance perfectPlusNativeFundamentalPerfect
    (G : Type u) [Group G] [Group.IsPerfect G] :
    Group.IsPerfect (FundamentalGroup (groupClassifyingNative.{u, u} G)
      (groupClassifyingNativePoint.{u, u} G)) :=
  groupClassifyingNativeFundamental_isPerfect.{u, u} G

public local instance perfectPlusNativeTopNormal (G : Type u) [Group G] :
    (⊤ : Subgroup (FundamentalGroup (groupClassifyingNative.{u, u} G)
      (groupClassifyingNativePoint.{u, u} G))).Normal :=
  Subgroup.normal_top

/-- A perfect group internally supplies an actual native CW plus target
for its original classifying space, with derived point cofibrancy and the
literal original whole-group kernel. This is the inactive auxiliary used
by the whole native-family filler. -/
public theorem exists_groupClassifying_native_perfectPlus
    (G : Type u) [Group G] [Group.IsPerfect G] :
    ∃ D : CGWH.{u, u}, ∃ j : groupClassifyingNative.{u, u} G ⟶ D,
      PathConnectedSpace D ∧
      Cofibration (TopCat.const (j (groupClassifyingNativePoint.{u, u} G)) :
        TopCat.of PUnit.{u + 1} ⟶ D.toTop) ∧
      @TopCat.IsPlusConstructionAt.{u}
        (groupClassifyingNative.{u, u} G).toTop D.toTop (CGWH.cgwhToTop.map j)
        (groupClassifyingNativePoint.{u, u} G) (j (groupClassifyingNativePoint.{u, u} G)) rfl
        (⊤ : Subgroup (FundamentalGroup (groupClassifyingNative.{u, u} G)
          (groupClassifyingNativePoint.{u, u} G)))
        _root_.Subgroup.normal_top
        ((Group.IsPerfect.top_iff
          (G := FundamentalGroup (groupClassifyingNative.{u, u} G)
            (groupClassifyingNativePoint.{u, u} G))).mpr
          (groupClassifyingNativeFundamental_isPerfect.{u, u} G)) := by
  let X := groupClassifyingOrdinary G
  let x : X := groupClassifyingOrdinaryPoint G
  let Xn := groupClassifyingNative.{u, u} G
  let xn : Xn := groupClassifyingNativePoint.{u, u} G
  let eX := groupClassifyingToTopIso.{u, u} G
  letI : T2Space X := SSet.realization_t2Space (groupClassifyingNerve G)
  letI : Topology.CWComplex (Set.univ : Set X) :=
    SSet.instCWComplexToTop (groupClassifyingNerve G)
  letI : PathConnectedSpace X := groupClassifyingOrdinary_pathConnected G
  letI : Group.IsPerfect (FundamentalGroup X x) :=
    groupClassifyingOrdinaryFundamental_isPerfect G
  let P : Subgroup (FundamentalGroup X x) := ⊤
  letI : P.Normal := inferInstance
  letI : Group.IsPerfect P := inferInstance
  let Z := LoopCellRegularThreeComparison.originalThree X x P
  let i : X ⟶ Z := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let z : Z := LoopCellRegularThreeComparison.originalThreeBasePoint X x P
  have hi : i x = z := rfl
  let h := LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P
  have hp : TopCat.IsPlusConstructionAt i x z hi P := h.1
  have hl : TopCat.IsLocalCoefficientHomologyEquivalence i := h.2.1
  letI : PathConnectedSpace Z := h.2.2.2.2.2.1
  letI : Cofibration i := LoopCellIndependentPlus.originalInclusion_cofibration X x P
  letI : Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X) :=
    SSet.realizedVertex_pointMap_cofibration (groupClassifyingNerve G) (groupClassifyingVertex G)
  letI : Cofibration (TopCat.const z : TopCat.of PUnit.{u + 1} ⟶ Z) := by
    have hz : (TopCat.const z : TopCat.of PUnit.{u + 1} ⟶ Z) = TopCat.const x ≫ i := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      exact hi.symm
    rw [hz]
    infer_instance
  let M := TopCat.nativeSingularPointModelOfCofibrantPoint Z z
  let D : CGWH.{u, u} := TopCat.nativeSingularSpace Z
  let r : Z ⟶ D.toTop := TopCat.ofHom M.equiv.invFun
  let f₂ : Xn.toTop ⟶ Z := eX.hom ≫ i
  let jt : Xn.toTop ⟶ D.toTop := f₂ ≫ r
  let j : Xn ⟶ D := ConcreteCategory.ofHom jt.hom
  have hjt : CGWH.cgwhToTop.map j = jt := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rfl
  have hrw : TopCat.weakHomotopyEquivalences r :=
    TopCat.homotopyEquiv_toFun_mem M.equiv.symm
  have hxl : TopCat.IsLocalCoefficientHomologyEquivalence eX.hom :=
    TopCat.weakHomotopyEquivalences.isLocalCoefficientHomologyEquivalence_allComponents
      eX.hom (TopCat.weakHomotopyEquivalences.of_isIso eX.hom)
  have hrl : TopCat.IsLocalCoefficientHomologyEquivalence r :=
    TopCat.weakHomotopyEquivalences.isLocalCoefficientHomologyEquivalence_allComponents r hrw
  have hjl : TopCat.IsLocalCoefficientHomologyEquivalence (CGWH.cgwhToTop.map j) := by
    rw [hjt]
    exact TopCat.IsLocalCoefficientHomologyEquivalence.comp (f := f₂) (g := r)
      (TopCat.IsLocalCoefficientHomologyEquivalence.comp (f := eX.hom) (g := i) hxl hl) hrl
  have hxp : eX.hom xn = x := groupClassifyingNativePoint_toTop.{u, u} G
  have hjp : j xn = TopCat.nativeSingularPoint Z z := by
    change r (i (eX.hom xn)) = TopCat.nativeSingularPoint Z z
    rw [hxp, hi]
    exact M.backwardPoint
  have hpoint : Cofibration (TopCat.const (j xn) : TopCat.of PUnit.{u + 1} ⟶ D.toTop) := by
    rw [hjp]
    exact TopCat.nativeSingularPoint_cofibration Z z
  letI : PathConnectedSpace D := TopCat.nativeSingularSpace_pathConnected Z z
  letI : Group.IsPerfect (FundamentalGroup Xn xn) :=
    groupClassifyingNativeFundamental_isPerfect.{u, u} G
  have hiπ (p : FundamentalGroup X x) : FundamentalGroup.mapOfEq i.hom rfl p = 1 := by
    apply (FundamentalGroup.mapOfEq_eq_one_iff i.hom hi p).mp
    apply MonoidHom.mem_ker.mp
    rw [hp.kernel_eq]
    exact Subgroup.mem_top p
  have hf₂π (p : FundamentalGroup Xn xn) : FundamentalGroup.mapOfEq f₂.hom rfl p = 1 := by
    have hx₂ : f₂ xn = i x := congrArg i hxp
    apply (FundamentalGroup.mapOfEq_eq_one_iff f₂.hom hx₂ p).mp
    change FundamentalGroup.mapOfEq (i.hom.comp eX.hom.hom) hx₂ p = 1
    rw [FundamentalGroup.mapOfEq_comp eX.hom.hom i.hom hxp rfl hx₂]
    change FundamentalGroup.mapOfEq i.hom rfl
      (FundamentalGroup.mapOfEq eX.hom.hom hxp p) = 1
    exact hiπ _
  have hjπ (p : FundamentalGroup Xn xn) :
      FundamentalGroup.mapOfEq (CGWH.cgwhToTop.map j).hom rfl p = 1 := by
    rw [hjt]
    change FundamentalGroup.mapOfEq (r.hom.comp f₂.hom) rfl p = 1
    rw [FundamentalGroup.mapOfEq_comp f₂.hom r.hom rfl rfl rfl]
    change FundamentalGroup.mapOfEq r.hom rfl
      (FundamentalGroup.mapOfEq f₂.hom rfl p) = 1
    exact (congrArg (FundamentalGroup.mapOfEq r.hom rfl) (hf₂π p)).trans
      (map_one (FundamentalGroup.mapOfEq r.hom rfl))
  have hkernel : MonoidHom.ker
      (FundamentalGroup.mapOfEq (CGWH.cgwhToTop.map j).hom rfl) =
        (⊤ : Subgroup (FundamentalGroup Xn xn)) :=
    Iff.mpr (Subgroup.eq_top_iff' _) (fun p => MonoidHom.mem_ker.mpr (hjπ p))
  refine ⟨D, j, inferInstance, hpoint, ?_⟩
  exact
    { acyclic := TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence
        (CGWH.cgwhToTop.map j) hjl (j xn)
      kernel_eq := hkernel }

end CategoryTheory

end
