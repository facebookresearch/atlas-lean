/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.PointedCGWH
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveCounitEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidEquivalence
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import MathlibExt.Topology.Category.CGWH.RealizedInterval
public import Mathlib.GroupTheory.IsPerfect

/-!
# The original pointed classifying space of a group

The classifying nerve retains the original opposite-group convention.
Its fundamental-group comparison is the existing realization comparison,
nerve counit and inverse normalization. The native point is the inverse
image of the actual realized vertex under the canonical underlying-Top
Iso. Perfectness, connectedness and point cofibrancy are derived for the
actual spaces; no model or fundamental-group witness is assumed.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial TopCat.modelCategory

universe u w

namespace CategoryTheory

variable (G : Type u) [Group G]

/-- The actual one-object opposite category, with the original group carrier. -/
public abbrev groupClassifyingCategory := SingleObj Gᵐᵒᵖ

/-- The original nerve of the group category. -/
public abbrev groupClassifyingNerve : SSet.{u} := nerve (groupClassifyingCategory G)

/-- Its unique original vertex. -/
public abbrev groupClassifyingVertex : (groupClassifyingNerve G) _⦋0⦌ :=
  CategoryTheory.nerveEquiv.symm (SingleObj.star Gᵐᵒᵖ)

/-- Ordinary realization of the same nerve. -/
public abbrev groupClassifyingOrdinary : TopCat.{u} :=
  SSet.toTop.obj (groupClassifyingNerve G)

/-- The ordinary marked point is the actual unique realized vertex. -/
public abbrev groupClassifyingOrdinaryPoint : groupClassifyingOrdinary G :=
  SSet.realizedVertex (groupClassifyingVertex G)

/-- Native CGWH realization of the SAME nerve with an independent compact-probe
universe; the original group carrier and nerve value universe remain unchanged. -/
public abbrev groupClassifyingNative : CGWH.{w, u} :=
  classifyingSpaceCGWH.{w, u, 0}.obj (Cat.of (groupClassifyingCategory G))

/-- The existing canonical native/ordinary realization Iso. -/
public abbrev groupClassifyingToTopIso :
    (groupClassifyingNative.{u, w} G).toTop ≅ groupClassifyingOrdinary G :=
  classifyingSpaceCGWHToTopIso.{w, u, 0}.app (Cat.of (groupClassifyingCategory G))

/-- The native marked point is calibrated to the original ordinary vertex. -/
public abbrev groupClassifyingNativePoint : groupClassifyingNative.{u, w} G :=
  (groupClassifyingToTopIso.{u, w} G).inv (groupClassifyingOrdinaryPoint G)

/-- The literal canonical comparison sends the native point to the original vertex. -/
public theorem groupClassifyingNativePoint_toTop :
    (groupClassifyingToTopIso.{u, w} G).hom (groupClassifyingNativePoint.{u, w} G) =
      groupClassifyingOrdinaryPoint G :=
  (groupClassifyingToTopIso.{u, w} G).inv_hom_id_apply _

/-- The inverse-calibrated point is the original categorical native point. -/
public theorem groupClassifyingNativePoint_eq_categoryPoint :
    groupClassifyingNativePoint.{u, w} G =
      classifyingSpaceCGWHPoint.{w} (SingleObj.star Gᵐᵒᵖ) := by
  apply (ConcreteCategory.bijective_of_isIso (groupClassifyingToTopIso.{u, w} G).hom).1
  rw [groupClassifyingNativePoint_toTop.{u, w} G]
  exact (classifyingSpaceCGWHPoint_toTop.{w, u, 0} (SingleObj.star Gᵐᵒᵖ)).symm

/-- The normalized original opposite edge representing a group element. -/
public abbrev groupClassifyingNormalizedEdge (g : G) :
    (groupClassifyingNerve G).Edge (groupClassifyingVertex G) (groupClassifyingVertex G) :=
  CategoryTheory.nerve.edgeMk (MulOpposite.op g⁻¹)

/-- The actual realized normalized edge loop in the ordinary group space. -/
public def groupClassifyingOrdinaryLoop (g : G) :
    Path (groupClassifyingOrdinaryPoint G) (groupClassifyingOrdinaryPoint G) :=
  TopCat.pathEquiv (SSet.realizedEdgePath (groupClassifyingNormalizedEdge G g))

/-- The SAME original normalized loop in native realization, through the
canonical inverse native/ordinary Iso and its original marked point. -/
public def groupClassifyingNativeLoop (g : G) :
    Path (groupClassifyingNativePoint.{u, w} G) (groupClassifyingNativePoint.{u, w} G) :=
  (groupClassifyingOrdinaryLoop G g).map (groupClassifyingToTopIso.{u, w} G).inv.hom.continuous

private theorem groupClassifyingNativeLoop_apply_computed (g : G) (t : unitInterval) :
    groupClassifyingNativeLoop.{u, w} G g t =
      (groupClassifyingToTopIso.{u, w} G).inv (groupClassifyingOrdinaryLoop G g t) := rfl

/-- Its full actual path value uses the original ordinary loop. -/
public theorem groupClassifyingNativeLoop_apply (g : G) (t : unitInterval) :
    groupClassifyingNativeLoop.{u, w} G g t =
      (groupClassifyingToTopIso.{u, w} G).inv (groupClassifyingOrdinaryLoop G g t) :=
  groupClassifyingNativeLoop_apply_computed.{u, w} G g t

/-- The canonical native comparison sends the entire actual native loop
to the SAME original ordinary edge loop at every time. -/
public theorem groupClassifyingNativeLoop_toTop (g : G) (t : unitInterval) :
    (groupClassifyingToTopIso.{u, w} G).hom (groupClassifyingNativeLoop.{u, w} G g t) =
      groupClassifyingOrdinaryLoop G g t := by
  rw [groupClassifyingNativeLoop_apply.{u, w} G g t]
  exact (groupClassifyingToTopIso.{u, w} G).inv_hom_id_apply _

private theorem groupClassifyingNativeLoop_realized_edge_computed
    (g : G) (t : unitInterval) :
    groupClassifyingNativeLoop.{u, w} G g t =
      SSet.toCGWH.{w, u}.map (SSet.yonedaEquiv.symm
        (groupClassifyingNormalizedEdge G g).edge)
          (CGWH.nativeIntervalHomeomorph.{w, u}.symm t) := by
  apply (ConcreteCategory.bijective_of_isIso (groupClassifyingToTopIso.{u, w} G).hom).1
  rw [groupClassifyingNativeLoop_toTop.{u, w} G g t]
  change groupClassifyingOrdinaryLoop G g t =
    SSet.toTop.map (SSet.yonedaEquiv.symm (groupClassifyingNormalizedEdge G g).edge)
      (CGWH.nativeIntervalHomeomorph.{w, u}.symm t)
  rw [CGWH.nativeIntervalHomeomorph_symm_apply.{w, u} t]
  change (SSet.realizedEdgePath (groupClassifyingNormalizedEdge G g)).hom
    (TopCat.I.homeomorph.{u}.symm t) = _
  rw [SSet.realizedEdgePath_hom]
  rfl

/-- The ENTIRE actual native loop is the realized ORIGINAL normalized
edge evaluated at the SAME original interval parameter. -/
public theorem groupClassifyingNativeLoop_realized_edge
    (g : G) (t : unitInterval) :
    groupClassifyingNativeLoop.{u, w} G g t =
      SSet.toCGWH.{w, u}.map (SSet.yonedaEquiv.symm
        (groupClassifyingNormalizedEdge G g).edge)
          (CGWH.nativeIntervalHomeomorph.{w, u}.symm t) :=
  groupClassifyingNativeLoop_realized_edge_computed.{u, w} G g t

/-- The comparison of the ORIGINAL ordinary fundamental group with G,
using only the existing realization and nerve-counit equivalences. -/
public def groupClassifyingOrdinaryFundamentalMulEquiv :
    FundamentalGroup (groupClassifyingOrdinary G) (groupClassifyingOrdinaryPoint G) ≃* G :=
  (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
      (groupClassifyingNerve G) (groupClassifyingVertex G)).symm.trans
    ((SSet.fundamentalGroupoidNerveCounit_endMulEquiv
      (groupClassifyingCategory G) (SingleObj.star Gᵐᵒᵖ)).trans
        ((SingleObj.toEnd Gᵐᵒᵖ).symm.trans (MulEquiv.inv' G).symm))

/-- The native fundamental group is compared by the ORIGINAL canonical
native/ordinary Iso and the same group-normalization comparison. -/
public def groupClassifyingNativeFundamentalMulEquiv :
    FundamentalGroup (groupClassifyingNative.{u, w} G)
      (groupClassifyingNativePoint.{u, w} G) ≃* G :=
  (FundamentalGroup.mulEquivOfIsoAt (groupClassifyingToTopIso.{u, w} G)
    (groupClassifyingNativePoint.{u, w} G) (groupClassifyingOrdinaryPoint G)
      (groupClassifyingNativePoint_toTop.{u, w} G)).trans
    (groupClassifyingOrdinaryFundamentalMulEquiv G)

/-- A perfect group has perfect original ordinary classifying fundamental group. -/
public theorem groupClassifyingOrdinaryFundamental_isPerfect [Group.IsPerfect G] :
    Group.IsPerfect (FundamentalGroup (groupClassifyingOrdinary G)
      (groupClassifyingOrdinaryPoint G)) :=
  Group.IsPerfect.ofSurjective
    (f := (groupClassifyingOrdinaryFundamentalMulEquiv G).symm.toMonoidHom)
    (groupClassifyingOrdinaryFundamentalMulEquiv G).symm.surjective

/-- The original native classifying fundamental group is perfect as well. -/
public theorem groupClassifyingNativeFundamental_isPerfect [Group.IsPerfect G] :
    Group.IsPerfect (FundamentalGroup (groupClassifyingNative.{u, w} G)
      (groupClassifyingNativePoint.{u, w} G)) :=
  Group.IsPerfect.ofSurjective
    (f := (groupClassifyingNativeFundamentalMulEquiv.{u, w} G).symm.toMonoidHom)
    (groupClassifyingNativeFundamentalMulEquiv.{u, w} G).symm.surjective

/-- The unique actual vertex derives simplicial connectedness. -/
public theorem groupClassifyingNerve_isConnected : (groupClassifyingNerve G).IsConnected := by
  let e : (groupClassifyingNerve G) _⦋0⦌ ≃ groupClassifyingCategory G :=
    CategoryTheory.nerveEquiv
  let : Subsingleton ((groupClassifyingNerve G) _⦋0⦌) := e.injective.subsingleton
  have hπ : Subsingleton (SSet.π₀ (groupClassifyingNerve G)) :=
    (SSet.π₀.mk_surjective (X := groupClassifyingNerve G)).subsingleton
  exact (SSet.isConnected_iff (X := groupClassifyingNerve G)).mpr
    ⟨hπ, ⟨groupClassifyingVertex G⟩⟩

/-- The actual ordinary group classifying space is path connected. -/
public theorem groupClassifyingOrdinary_pathConnected :
    PathConnectedSpace (groupClassifyingOrdinary G) := by
  let := groupClassifyingNerve_isConnected G
  exact SSet.pathConnectedSpace_realization_of_isConnected (groupClassifyingNerve G)

/-- The native classifying space retains actual path connectedness. -/
public theorem groupClassifyingNative_pathConnected :
    PathConnectedSpace (groupClassifyingNative.{u, w} G) := by
  let := groupClassifyingOrdinary_pathConnected G
  exact (TopCat.homeoOfIso (groupClassifyingToTopIso.{u, w} G)).symm.pathConnectedSpace

/-- The native classifying space is Hausdorff by its actual realization Iso. -/
public theorem groupClassifyingNative_t2Space : T2Space (groupClassifyingNative.{u, w} G) := by
  let : T2Space (groupClassifyingOrdinary G) :=
    SSet.realization_t2Space (groupClassifyingNerve G)
  exact (TopCat.homeoOfIso (groupClassifyingToTopIso.{u, w} G)).symm.t2Space

/-- The marked native point Cofibration is derived from the SAME realized
vertex point Cofibration and canonical native/ordinary Iso. -/
public theorem groupClassifyingNative_pointMap_cofibration :
    Cofibration (TopCat.const (groupClassifyingNativePoint.{u, w} G) :
      TopCat.of PUnit.{u + 1} ⟶ (groupClassifyingNative.{u, w} G).toTop) := by
  let e := groupClassifyingToTopIso.{u, w} G
  let := SSet.realizedVertex_pointMap_cofibration
    (groupClassifyingNerve G) (groupClassifyingVertex G)
  have h : (TopCat.const (groupClassifyingNativePoint.{u, w} G) :
      TopCat.of PUnit.{u + 1} ⟶ (groupClassifyingNative.{u, w} G).toTop) =
      TopCat.const (groupClassifyingOrdinaryPoint G) ≫ e.inv := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  rw [h]
  infer_instance

end CategoryTheory

end

noncomputable section

open CategoryTheory

universe u w

namespace CategoryTheory

variable (G : Type u) [Group G]

private theorem singleObjConj_asHom {M : Type u} [Monoid M]
    {x y : SingleObj M} (h : x = y) (a : CategoryTheory.End x) :
    ((eqToIso h).conj a).asHom = a.asHom := by
  cases h
  rw [Iso.conj_apply_asHom]
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id]

/-- The original normalized edge carries exactly the opposite inverse label. -/
public theorem groupClassifyingNormalizedEdge_homEquiv (g : G) :
    CategoryTheory.nerve.homEquiv (groupClassifyingNormalizedEdge G g) =
      MulOpposite.op g⁻¹ := by
  let star : groupClassifyingCategory G := SingleObj.star Gᵐᵒᵖ
  let f : star ⟶ star := MulOpposite.op g⁻¹
  change CategoryTheory.nerve.homEquiv
    (CategoryTheory.nerve.edgeMk (C := groupClassifyingCategory G)
      (x := star) (y := star) f) = f
  exact CategoryTheory.nerve.homEquiv_edgeMk
    (C := groupClassifyingCategory G) (x := star) (y := star) f

private theorem groupClassifyingOrdinaryFundamentalMulEquiv_loop_computed (g : G) :
    groupClassifyingOrdinaryFundamentalMulEquiv G
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (groupClassifyingOrdinaryLoop G g))) = g := by
  let e := groupClassifyingNormalizedEdge G g
  let c := CategoryTheory.End.of (SSet.FundamentalGroupoid.homMk e)
  let real := SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
    (groupClassifyingNerve G) (groupClassifyingVertex G)
  let q := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (groupClassifyingOrdinaryLoop G g))
  let star := SingleObj.star Gᵐᵒᵖ
  let counit := SSet.fundamentalGroupoidNerveCounit (groupClassifyingCategory G)
  let counitEnd := SSet.fundamentalGroupoidNerveCounit_endMulEquiv
    (groupClassifyingCategory G) star
  have hReal : real c = q :=
    congrArg
      (fun f : (SSet.realizationFundamentalGroupoidFunctor (groupClassifyingNerve G)).obj
          (SSet.FundamentalGroupoid.mk (groupClassifyingVertex G)) ⟶
        (SSet.realizationFundamentalGroupoidFunctor (groupClassifyingNerve G)).obj
          (SSet.FundamentalGroupoid.mk (groupClassifyingVertex G)) =>
        CategoryTheory.End.of f)
      (SSet.realizationFundamentalGroupoidFunctor_map_homMk (groupClassifyingNerve G) e)
  have hInv : real.symm q = c :=
    (congrArg real.symm hReal.symm).trans (real.symm_apply_apply c)
  have hCounit : counit.mapEnd (SSet.FundamentalGroupoid.mk (groupClassifyingVertex G)) c =
      CategoryTheory.End.of (CategoryTheory.nerve.homEquiv e) := by
    apply CategoryTheory.End.ext
    exact SSet.fundamentalGroupoidNerveCounit_map_homMk (groupClassifyingCategory G) e
  have hCounitLabel : (counitEnd c).asHom = MulOpposite.op g⁻¹ :=
    (congrArg CategoryTheory.End.asHom
      (SSet.fundamentalGroupoidNerveCounit_endMulEquiv_apply
        (groupClassifyingCategory G) star c)).trans
      ((singleObjConj_asHom
        (CategoryTheory.nerveEquiv.apply_symm_apply star)
        (counit.mapEnd (SSet.FundamentalGroupoid.mk (groupClassifyingVertex G)) c)).trans
          ((congrArg CategoryTheory.End.asHom hCounit).trans
            (groupClassifyingNormalizedEdge_homEquiv G g)))
  have hSingle : (SingleObj.toEnd Gᵐᵒᵖ).symm (counitEnd c) = MulOpposite.op g⁻¹ :=
    hCounitLabel
  have hRecipe : groupClassifyingOrdinaryFundamentalMulEquiv G q =
      (MulEquiv.inv' G).symm ((SingleObj.toEnd Gᵐᵒᵖ).symm (counitEnd (real.symm q))) :=
    rfl
  have hRetain :
      (MulEquiv.inv' G).symm ((SingleObj.toEnd Gᵐᵒᵖ).symm (counitEnd (real.symm q))) =
        (MulEquiv.inv' G).symm ((SingleObj.toEnd Gᵐᵒᵖ).symm (counitEnd c)) :=
    congrArg (fun a => (MulEquiv.inv' G).symm
      ((SingleObj.toEnd Gᵐᵒᵖ).symm (counitEnd a))) hInv
  have hNormalize : (MulEquiv.inv' G).symm (MulOpposite.op g⁻¹) = g := by
    simp only [MulEquiv.inv'_symm_apply, Function.comp_apply,
      MulOpposite.unop_op, inv_inv]
  exact hRecipe.trans (hRetain.trans
    ((congrArg (MulEquiv.inv' G).symm hSingle).trans hNormalize))

/-- The generic ordinary comparison sends the loop labelled by `g` to `g`. -/
@[simp]
public theorem groupClassifyingOrdinaryFundamentalMulEquiv_loop (g : G) :
    groupClassifyingOrdinaryFundamentalMulEquiv G
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (groupClassifyingOrdinaryLoop G g))) = g :=
  groupClassifyingOrdinaryFundamentalMulEquiv_loop_computed G g

private theorem groupClassifyingNormalizedLoop_comparison_computed (g : G) :
    ((SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
        (groupClassifyingNerve G) (groupClassifyingVertex G)).symm.trans
      ((SSet.fundamentalGroupoidNerveCounit_endMulEquiv
        (groupClassifyingCategory G) (SingleObj.star Gᵐᵒᵖ)).trans
          ((SingleObj.toEnd Gᵐᵒᵖ).symm.trans (MulEquiv.inv' G).symm)))
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (MulOpposite.op g⁻¹)))))) = g :=
  groupClassifyingOrdinaryFundamentalMulEquiv_loop_computed G g

/-- The same normalization in the original realization/counit recipe.
This characteristic lets specialized consumers delegate without unfolding
the opaque generic comparison or changing their original maps. -/
public theorem groupClassifyingNormalizedLoop_comparison (g : G) :
    ((SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
        (groupClassifyingNerve G) (groupClassifyingVertex G)).symm.trans
      ((SSet.fundamentalGroupoidNerveCounit_endMulEquiv
        (groupClassifyingCategory G) (SingleObj.star Gᵐᵒᵖ)).trans
          ((SingleObj.toEnd Gᵐᵒᵖ).symm.trans (MulEquiv.inv' G).symm)))
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (MulOpposite.op g⁻¹)))))) = g :=
  groupClassifyingNormalizedLoop_comparison_computed G g

private theorem groupClassifyingNativeFundamentalMulEquiv_loop_computed (g : G) :
    groupClassifyingNativeFundamentalMulEquiv.{u, w} G
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (groupClassifyingNativeLoop.{u, w} G g))) = g := by
  let e := groupClassifyingToTopIso.{u, w} G
  let x := groupClassifyingNativePoint.{u, w} G
  let y := groupClassifyingOrdinaryPoint G
  let p := groupClassifyingNativeLoop.{u, w} G g
  let q := groupClassifyingOrdinaryLoop G g
  let hxy := groupClassifyingNativePoint_toTop.{u, w} G
  let f := e.hom.hom
  have hPath : (p.map f.continuous).cast hxy.symm hxy.symm = q := by
    apply _root_.Path.ext
    funext t
    exact groupClassifyingNativeLoop_toTop.{u, w} G g t
  have hClass :
      (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk p) f).cast
        hxy.symm hxy.symm = Path.Homotopic.Quotient.mk q :=
    (congrArg (fun a : Path.Homotopic.Quotient (f x) (f x) =>
      a.cast hxy.symm hxy.symm) (Path.Homotopic.Quotient.mk_map p f).symm).trans
      ((Path.Homotopic.Quotient.mk_cast (p.map f.continuous)
        hxy.symm hxy.symm).symm.trans (congrArg Path.Homotopic.Quotient.mk hPath))
  have hMap :
      FundamentalGroup.mapOfEq f hxy
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) :=
    (FundamentalGroup.mapOfEq_apply f hxy
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))).trans
        (congrArg FundamentalGroup.fromPath hClass)
  have hRecipe :
      groupClassifyingNativeFundamentalMulEquiv.{u, w} G
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
        groupClassifyingOrdinaryFundamentalMulEquiv G
          (FundamentalGroup.mulEquivOfIsoAt e x y hxy
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) := rfl
  have hIso := FundamentalGroup.mulEquivOfIsoAt_apply e x y hxy
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
  exact hRecipe.trans ((congrArg (groupClassifyingOrdinaryFundamentalMulEquiv G)
    (hIso.trans hMap)).trans (groupClassifyingOrdinaryFundamentalMulEquiv_loop G g))

/-- For every independent probe universe, the native comparison sends the
original loop labelled by `g` to `g`. -/
@[simp]
public theorem groupClassifyingNativeFundamentalMulEquiv_loop (g : G) :
    groupClassifyingNativeFundamentalMulEquiv.{u, w} G
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (groupClassifyingNativeLoop.{u, w} G g))) = g :=
  groupClassifyingNativeFundamentalMulEquiv_loop_computed G g

end CategoryTheory

end
