/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.SquarePerimeterCircle
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PointedHomeomorph

/-!
# The original square perimeter generates its based fundamental group

The actual perimeter homeomorphism carries the original based perimeter to
the period-one circle loop of winding number one. The resulting
multiplicative equivalence retains the original `End` convention at every
carrier universe and proves that every original square-boundary class is
an integer power of this same perimeter class.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u

namespace Topology.CWComplex

/-- The same original four-edge perimeter class in the original based End group. -/
def classicalCellSquarePerimeterClass :
    FundamentalGroup classicalCellSquareBoundary.{u} classicalCellSquareBottomLeft.{u} :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u})

/-- Mapping the original perimeter through the actual inverse homeomorphism
is exactly the circle loop of winding one, with its actual endpoint casts. -/
theorem classicalCellSquarePerimeter_map_circle :
    (classicalCellSquarePerimeter.{u}.map
        classicalCellSquarePerimeterCircleHomeomorph.{u}.symm.continuous).cast
        classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft.{u}.symm
        classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft.{u}.symm =
      AddCircle.zsmulLoop (1 : ℝ) 0 (1 : ℤ) := by
  apply Path.ext
  funext t
  change classicalCellSquarePerimeterCircleHomeomorph.{u}.symm
      (classicalCellSquarePerimeter.{u} t) = AddCircle.zsmulLoop (1 : ℝ) 0 (1 : ℤ) t
  have hLoop : AddCircle.zsmulLoop (1 : ℝ) (0 : ℝ) (1 : ℤ) t =
      ((t : ℝ) : AddCircle (1 : ℝ)) := by
    have hEval := AddCircle.zsmulLoop_apply (1 : ℝ) (0 : ℝ) (1 : ℤ) t
    simpa only [one_zsmul, mul_one, AddCircle.coe_zero, add_zero] using hEval
  exact (classicalCellSquarePerimeterCircleHomeomorph_symm_perimeter.{u} t).trans hLoop.symm

/-- The original based map sends the same perimeter class to the canonical circle generator. -/
theorem classicalCellSquarePerimeterClass_map :
    FundamentalGroup.mapOfEq
        classicalCellSquarePerimeterCircleHomeomorph.{u}.symm.toHomotopyEquiv.toFun
        classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft.{u}
        classicalCellSquarePerimeterClass.{u} =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop (1 : ℝ) 0 (1 : ℤ))) := by
  let f := classicalCellSquarePerimeterCircleHomeomorph.{u}.symm.toHomotopyEquiv.toFun
  have hFun : f classicalCellSquareBottomLeft.{u} =
      classicalCellSquarePerimeterCircleHomeomorph.{u}.symm
        classicalCellSquareBottomLeft.{u} :=
    congrFun (Homeomorph.coe_toHomotopyEquiv
      classicalCellSquarePerimeterCircleHomeomorph.{u}.symm)
      classicalCellSquareBottomLeft.{u}
  have hPoint : f classicalCellSquareBottomLeft.{u} = 0 :=
    hFun.trans classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft.{u}
  have hPath : (classicalCellSquarePerimeter.{u}.map f.continuous).cast
      hPoint.symm hPoint.symm = AddCircle.zsmulLoop (1 : ℝ) 0 (1 : ℤ) := by
    exact classicalCellSquarePerimeter_map_circle
  have hClass :
      (Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u}) f).cast
          hPoint.symm hPoint.symm =
        Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop (1 : ℝ) 0 (1 : ℤ)) :=
    (congrArg
      (fun q : Path.Homotopic.Quotient
          (f classicalCellSquareBottomLeft.{u}) (f classicalCellSquareBottomLeft.{u}) =>
        q.cast hPoint.symm hPoint.symm)
      (Path.Homotopic.Quotient.mk_map classicalCellSquarePerimeter.{u} f).symm).trans
        ((Path.Homotopic.Quotient.mk_cast
          (classicalCellSquarePerimeter.{u}.map f.continuous) hPoint.symm hPoint.symm).symm.trans
            (congrArg Path.Homotopic.Quotient.mk hPath))
  exact (FundamentalGroup.mapOfEq_apply f hPoint classicalCellSquarePerimeterClass.{u}).trans
    (congrArg (fun q : Path.Homotopic.Quotient (0 : AddCircle (1 : ℝ)) 0 =>
      FundamentalGroup.fromPath q) hClass)

/-- The original square-boundary based group is cyclic by the actual perimeter homeomorphism. -/
def classicalCellSquareWindingIso :
    FundamentalGroup classicalCellSquareBoundary.{u} classicalCellSquareBottomLeft.{u} ≃*
      Multiplicative ℤ := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (FundamentalGroup.mulEquivOfHomeomorphAt
    classicalCellSquarePerimeterCircleHomeomorph.{u}.symm
    classicalCellSquareBottomLeft.{u} 0
    classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft.{u}).trans
      (AddCircle.windingNumberIso 0)

/-- The exact original perimeter has winding one under the constructed based equivalence. -/
theorem classicalCellSquareWindingIso_perimeter :
    classicalCellSquareWindingIso.{u} classicalCellSquarePerimeterClass.{u} =
      Multiplicative.ofAdd (1 : ℤ) := by
  change @AddCircle.windingNumberIso (1 : ℝ) ⟨zero_lt_one⟩ 0
      (FundamentalGroup.mulEquivOfHomeomorphAt
        classicalCellSquarePerimeterCircleHomeomorph.{u}.symm
        classicalCellSquareBottomLeft.{u} 0
        classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft.{u}
        classicalCellSquarePerimeterClass.{u}) = Multiplicative.ofAdd (1 : ℤ)
  rw [FundamentalGroup.mulEquivOfHomeomorphAt_apply, classicalCellSquarePerimeterClass_map]
  have h := @AddCircle.windingNumber_zsmulLoop (1 : ℝ) ⟨zero_lt_one⟩ (0 : ℝ) (1 : ℤ)
  exact (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ).injective h

/-- Every original based boundary loop class is an integer power of the same original perimeter. -/
theorem classicalCellSquare_exists_perimeter_zpow
    (q : FundamentalGroup classicalCellSquareBoundary.{u} classicalCellSquareBottomLeft.{u}) :
    ∃ n : ℤ, q = classicalCellSquarePerimeterClass.{u} ^ n := by
  refine ⟨(classicalCellSquareWindingIso.{u} q).toAdd, ?_⟩
  apply classicalCellSquareWindingIso.{u}.injective
  rw [map_zpow, classicalCellSquareWindingIso_perimeter]
  exact (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ).injective (by
    simp only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one, Int.cast_id])

end Topology.CWComplex

end

end
