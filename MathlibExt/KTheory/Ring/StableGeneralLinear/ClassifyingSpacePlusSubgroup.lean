/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
public import MathlibExt.KTheory.Ring.K1.WhiteheadQuotient
public import MathlibExt.KTheory.Ring.K2.StableElementaryPerfect
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpaceFundamentalGroup

/-!
# The plus subgroup of algebraic stable `BGL`

The fundamental-group equivalence

`π₁(BGL(R)) ≃ StableGL R`

pulls the stable elementary subgroup back to a canonical perfect normal
subgroup of `π₁(BGL(R))`. This is the subgroup killed by Quillen's plus
construction. It is named independently of any chosen plus-construction
target.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The perfect normal subgroup of `π₁(BGL(R))` corresponding to the stable
elementary subgroup under `ordinaryBGLFundamentalMulEquiv`. -/
noncomputable def BGLPlusSubgroup (R : Type u) [Ring R] :
    Subgroup
      (FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R)) :=
  (stableElementarySubgroup R).comap
    (ordinaryBGLFundamentalMulEquiv R).toMonoidHom

noncomputable instance BGLPlusSubgroup.instNormal
    (R : Type u) [Ring R] : (BGLPlusSubgroup R).Normal := by
  unfold BGLPlusSubgroup
  infer_instance

/-- The plus subgroup is multiplicatively equivalent to `StableE R`. -/
noncomputable def BGLPlusSubgroup.mulEquivStableE
    (R : Type u) [Ring R] : BGLPlusSubgroup R ≃* StableE R where
  toFun x := ⟨ordinaryBGLFundamentalMulEquiv R x, x.property⟩
  invFun x := ⟨(ordinaryBGLFundamentalMulEquiv R).symm x, by
    change ordinaryBGLFundamentalMulEquiv R
        ((ordinaryBGLFundamentalMulEquiv R).symm x) ∈
      stableElementarySubgroup R
    rw [(ordinaryBGLFundamentalMulEquiv R).apply_symm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (ordinaryBGLFundamentalMulEquiv R).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (ordinaryBGLFundamentalMulEquiv R).apply_symm_apply x
  map_mul' x y := by
    apply Subtype.ext
    exact (ordinaryBGLFundamentalMulEquiv R).map_mul x y

noncomputable instance BGLPlusSubgroup.instIsPerfect
    (R : Type u) [Ring R] : Group.IsPerfect (BGLPlusSubgroup R) :=
  Group.IsPerfect.ofSurjective
    (f := (BGLPlusSubgroup.mulEquivStableE R).symm.toMonoidHom)
    (BGLPlusSubgroup.mulEquivStableE R).symm.surjective

/-- The perfect normal plus subgroup on the canonical native CGWH
`BGL(R)`. -/
noncomputable def BGLPlusSubgroupCGWH (R : Type u) [Ring R] :
    Subgroup
      (FundamentalGroup (CGWH.cgwhToTop.obj (BGL.{w} R))
        (BGLBasepoint.{w} R)) :=
  (stableElementarySubgroup R).comap
    (BGLFundamentalMulEquiv.{w} R).toMonoidHom

noncomputable instance BGLPlusSubgroupCGWH.instNormal
    (R : Type u) [Ring R] : (BGLPlusSubgroupCGWH.{w} R).Normal := by
  unfold BGLPlusSubgroupCGWH
  infer_instance

/-- The native-CGWH plus subgroup is multiplicatively equivalent to
`StableE R`. -/
noncomputable def BGLPlusSubgroupCGWH.mulEquivStableE
    (R : Type u) [Ring R] : BGLPlusSubgroupCGWH.{w} R ≃* StableE R where
  toFun x := ⟨BGLFundamentalMulEquiv.{w} R x, x.property⟩
  invFun x := ⟨(BGLFundamentalMulEquiv.{w} R).symm x, by
    change BGLFundamentalMulEquiv.{w} R
        ((BGLFundamentalMulEquiv.{w} R).symm x) ∈
      stableElementarySubgroup R
    rw [(BGLFundamentalMulEquiv.{w} R).apply_symm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (BGLFundamentalMulEquiv.{w} R).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (BGLFundamentalMulEquiv.{w} R).apply_symm_apply x
  map_mul' x y := by
    apply Subtype.ext
    exact (BGLFundamentalMulEquiv.{w} R).map_mul x y

noncomputable instance BGLPlusSubgroupCGWH.instIsPerfect
    (R : Type u) [Ring R] :
    Group.IsPerfect (BGLPlusSubgroupCGWH.{w} R) :=
  Group.IsPerfect.ofSurjective
    (f := (BGLPlusSubgroupCGWH.mulEquivStableE.{w} R).symm.toMonoidHom)
    (BGLPlusSubgroupCGWH.mulEquivStableE.{w} R).symm.surjective

/-- A normalized loop lies in the plus subgroup exactly when its stable
matrix lies in the stable elementary subgroup. -/
theorem ordinaryBGLLoop_mem_BGLPlusSubgroup_iff
    {R : Type u} [Ring R] (g : StableGL R) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)) ∈
        BGLPlusSubgroup R ↔
      g ∈ stableElementarySubgroup R := by
  change ordinaryBGLFundamentalMulEquiv R
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))) ∈
        stableElementarySubgroup R ↔ _
  rw [ordinaryBGLFundamentalMulEquiv_loop]

/-- Every normalized stable elementary loop belongs to the plus subgroup. -/
theorem ordinaryBGLLoop_mem_BGLPlusSubgroup
    {R : Type u} [Ring R] (g : StableE R) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (ordinaryBGLLoop (g : StableGL R))) ∈ BGLPlusSubgroup R :=
  (ordinaryBGLLoop_mem_BGLPlusSubgroup_iff (g : StableGL R)).2 g.property

end StableGL
end AlgebraicKTheory

end
