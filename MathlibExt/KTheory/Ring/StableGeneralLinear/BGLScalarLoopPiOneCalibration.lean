/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarClassifyingSource
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarClassifyingArrow
public import MathlibExt.KTheory.Ring.StableElementary.ScalarMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusUniverseLift

/-!
# The actual mixed-world BGL loop and elementary-subgroup dictionary

The scalar map is the original continuous source map from the scalar
functor. Its normalized loop is compared using the actual functor-edge
homotopy and the two original point transports. The original fundamental
comparison then computes the induced map on every element. Elementary
preservation comes from the existing intrinsic scalar subgroup theorem.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe uR uS uG

namespace AlgebraicKTheory.StableGL

private theorem singleObjLoopEdge_eq
    {G : Type uG} [Monoid G] {a b : SingleObj G}
    (p : a ⟶ a) (q : b ⟶ b) (h : a = b)
    (hp : (show G from p) = (show G from q)) :
    (nerve.edgeMk (C := SingleObj G) (x := a) (y := a) p).edge =
      (nerve.edgeMk (C := SingleObj G) (x := b) (y := b) q).edge := by
  cases h
  cases hp
  rfl

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The SAME original normalized loop is mapped to its actual scalar loop
up to a homotopy at the original target basepoint. -/
public theorem ordinaryBGLScalarMap_loop (f : R →+* S) (g : StableGL R) :
    (((ordinaryBGLLoop g).map (ordinaryBGLScalarMap f).continuous).cast
      (ordinaryBGLScalarMap_point f).symm (ordinaryBGLScalarMap_point f).symm).Homotopic
        (ordinaryBGLLoop (scalarMap f g)) := by
  let F := classifyingCategoryScalarMap f
  let x : ClassifyingCategory R := SingleObj.star (StableGL R)ᵐᵒᵖ
  let y : ClassifyingCategory S := SingleObj.star (StableGL S)ᵐᵒᵖ
  let k : x ⟶ x := MulOpposite.op g⁻¹
  let eTarget := nerve.edgeMk (C := ClassifyingCategory S)
    (x := F.obj x) (y := F.obj x) (F.map k)
  let eScalar := normalizedClassifyingEdge (scalarMap f g)
  have hObject : F.obj x = y := classifyingCategoryScalarMap_star f
  have hVertex : SSet.realizedVertex (X := nerve (ClassifyingCategory S))
      (ComposableArrows.mk₀ (F.obj x)) = ordinaryBGLBasepoint S :=
    congrArg (fun z : ClassifyingCategory S =>
      SSet.realizedVertex (X := nerve (ClassifyingCategory S)) (ComposableArrows.mk₀ z))
      hObject
  have hArrow : F.map k = (MulOpposite.op (scalarMap f g)⁻¹ : F.obj x ⟶ F.obj x) :=
    classifyingCategoryScalarMap_map_normalized f g
  have hEdge : eTarget.edge = eScalar.edge :=
    singleObjLoopEdge_eq (G := (StableGL S)ᵐᵒᵖ)
      (F.map k) (MulOpposite.op (scalarMap f g)⁻¹ : y ⟶ y) hObject hArrow
  have hHom : (SSet.realizedEdgePath eTarget).hom = (SSet.realizedEdgePath eScalar).hom :=
    (SSet.realizedEdgePath_hom eTarget).trans
      ((congrArg (fun z : (classifyingNerve S) _⦋1⦌ =>
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.yonedaEquiv.symm z)) hEdge).trans
          (SSet.realizedEdgePath_hom eScalar).symm)
  have hRaw := CategoryTheory.realizedNerveFunctorMap_edge_homotopic F k
  have h := hRaw.pathCast hVertex.symm hVertex.symm
  have hLeft :
      ((((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ClassifyingCategory R) (x := x) (y := x) k))).map
          (CategoryTheory.realizedNerveFunctorMap F).continuous).cast
            (CategoryTheory.realizedNerveFunctorMap_vertex F x).symm
            (CategoryTheory.realizedNerveFunctorMap_vertex F x).symm).cast
              hVertex.symm hVertex.symm) =
      (((ordinaryBGLLoop g).map (ordinaryBGLScalarMap f).continuous).cast
        (ordinaryBGLScalarMap_point f).symm (ordinaryBGLScalarMap_point f).symm) := by
    apply Path.ext
    funext t
    change CategoryTheory.realizedNerveFunctorMap F (ordinaryBGLLoop g t) =
      ordinaryBGLScalarMap f (ordinaryBGLLoop g t)
    exact (congrArg (fun m : C(ordinaryBGL R, ordinaryBGL S) => m (ordinaryBGLLoop g t))
      (ordinaryBGLScalarMap_eq_realizedFunctorMap f)).symm
  have hRight :
      ((TopCat.pathEquiv (SSet.realizedEdgePath eTarget)).cast
        hVertex.symm hVertex.symm) = ordinaryBGLLoop (scalarMap f g) := by
    apply Path.ext
    funext t
    change (SSet.realizedEdgePath eTarget).hom (TopCat.I.homeomorph.{uS}.symm t) =
      (SSet.realizedEdgePath eScalar).hom (TopCat.I.homeomorph.{uS}.symm t)
    exact ConcreteCategory.congr_hom hHom (TopCat.I.homeomorph.{uS}.symm t)
  obtain ⟨H⟩ := h
  exact ⟨Path.Homotopy.cast H hLeft hRight⟩

private theorem ordinaryBGLScalarMap_fromLoop (f : R →+* S) (g : StableGL R) :
    FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))) =
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (ordinaryBGLLoop (scalarMap f g))) := by
  apply End.ext
  rw [FundamentalGroup.mapOfEq_apply]
  change ((Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)).map
      (ordinaryBGLScalarMap f)).cast
        (ordinaryBGLScalarMap_point f).symm (ordinaryBGLScalarMap_point f).symm =
    Path.Homotopic.Quotient.mk (ordinaryBGLLoop (scalarMap f g))
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  exact Quotient.sound (ordinaryBGLScalarMap_loop f g)

/-- The original fundamental-group dictionary computes the actual mixed-ring
source map on every fundamental-group element. -/
public theorem ordinaryBGLScalarMap_fundamental (f : R →+* S)
    (p : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R)) :
    ordinaryBGLFundamentalMulEquiv S
      (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f) p) =
      scalarMap f (ordinaryBGLFundamentalMulEquiv R p) := by
  let g := ordinaryBGLFundamentalMulEquiv R p
  have hp : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)) = p :=
    (ordinaryBGLFundamentalMulEquiv R).injective (ordinaryBGLFundamentalMulEquiv_loop g)
  calc
    ordinaryBGLFundamentalMulEquiv S
      (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f) p) =
      ordinaryBGLFundamentalMulEquiv S
        (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)))) :=
      congrArg (fun q => ordinaryBGLFundamentalMulEquiv S
        (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f) q))
        hp.symm
    _ = ordinaryBGLFundamentalMulEquiv S
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (ordinaryBGLLoop (scalarMap f g)))) :=
      congrArg (ordinaryBGLFundamentalMulEquiv S) (ordinaryBGLScalarMap_fromLoop f g)
    _ = scalarMap f g := ordinaryBGLFundamentalMulEquiv_loop _

/-- The actual mixed-world BGL map carries the prescribed original plus
subgroup into the target prescribed subgroup. -/
public theorem ordinaryBGLScalarMap_preservesPlusSubgroup (f : R →+* S)
    (p : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R))
    (hp : p ∈ BGLPlusSubgroup R) :
    FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f) p ∈
      BGLPlusSubgroup S := by
  change ordinaryBGLFundamentalMulEquiv S
      (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f) p) ∈
    stableElementarySubgroup S
  rw [ordinaryBGLScalarMap_fundamental]
  exact scalarMap_mem_stableElementarySubgroup f hp

end AlgebraicKTheory.StableGL

end
