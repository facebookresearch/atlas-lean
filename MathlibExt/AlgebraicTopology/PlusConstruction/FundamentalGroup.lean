/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fundamental group of a plus-construction target

For plus-construction data whose induced fundamental-group map is
surjective, Noether's first isomorphism theorem identifies the target
fundamental group with the source fundamental group modulo the specified
perfect normal subgroup.

Surjectivity is an explicit hypothesis here. Classically it follows from
acyclicity of the homotopy fiber via the long exact homotopy sequence; that
topological implication is intentionally not assumed without proof.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace TopCat
namespace IsPlusConstructionAt

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup X x)}
  [P.Normal] [Group.IsPerfect P]

/-- A plus-construction target has fundamental group equal to the source
fundamental group modulo the killed subgroup, provided the induced map on
fundamental groups is surjective. -/
noncomputable def fundamentalGroupQuotientMulEquiv
    (h : IsPlusConstructionAt f x y hxy P)
    (hsurj : Function.Surjective
      (FundamentalGroup.mapOfEq f.hom hxy)) :
    FundamentalGroup X x ⧸ P ≃* FundamentalGroup Y y := by
  let φ := FundamentalGroup.mapOfEq f.hom hxy
  exact (QuotientGroup.quotientMulEquivOfEq h.kernel_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

/-- The quotient comparison sends a source class to its image in the target
fundamental group. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_mk
    (h : IsPlusConstructionAt f x y hxy P)
    (hsurj : Function.Surjective
      (FundamentalGroup.mapOfEq f.hom hxy))
    (q : FundamentalGroup X x) :
    h.fundamentalGroupQuotientMulEquiv hsurj
        (QuotientGroup.mk q) =
      FundamentalGroup.mapOfEq f.hom hxy q := by
  unfold fundamentalGroupQuotientMulEquiv
  dsimp only [MulEquiv.trans_apply]
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  change QuotientGroup.kerLift
      (FundamentalGroup.mapOfEq f.hom hxy)
      (QuotientGroup.mk q) = _
  rw [QuotientGroup.kerLift_mk]

/-- Inverse formula for an element represented by a source loop. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_symm_map
    (h : IsPlusConstructionAt f x y hxy P)
    (hsurj : Function.Surjective
      (FundamentalGroup.mapOfEq f.hom hxy))
    (q : FundamentalGroup X x) :
    (h.fundamentalGroupQuotientMulEquiv hsurj).symm
        (FundamentalGroup.mapOfEq f.hom hxy q) =
      QuotientGroup.mk q := by
  apply (h.fundamentalGroupQuotientMulEquiv hsurj).injective
  rw [(h.fundamentalGroupQuotientMulEquiv hsurj).apply_symm_apply,
    fundamentalGroupQuotientMulEquiv_mk]

end IsPlusConstructionAt
end TopCat

namespace CGWH
namespace IsPlusConstructionAt

variable {X Y : CGWH.{w, u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x)}
  [P.Normal] [Group.IsPerfect P]

/-- The fundamental group of a CGWH plus-construction target is the source
fundamental group modulo the killed subgroup, assuming surjectivity. -/
noncomputable def fundamentalGroupQuotientMulEquiv
    (h : CGWH.IsPlusConstructionAt f x y hxy P)
    (hsurj : Function.Surjective
      (FundamentalGroup.mapOfEq (cgwhToTop.map f).hom hxy)) :
    FundamentalGroup (cgwhToTop.obj X) x ⧸ P ≃*
      FundamentalGroup (cgwhToTop.obj Y) y :=
  TopCat.IsPlusConstructionAt.fundamentalGroupQuotientMulEquiv h hsurj

/-- The CGWH quotient comparison sends a source class to its image. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_mk
    (h : CGWH.IsPlusConstructionAt f x y hxy P)
    (hsurj : Function.Surjective
      (FundamentalGroup.mapOfEq (cgwhToTop.map f).hom hxy))
    (q : FundamentalGroup (cgwhToTop.obj X) x) :
    h.fundamentalGroupQuotientMulEquiv hsurj (QuotientGroup.mk q) =
      FundamentalGroup.mapOfEq (cgwhToTop.map f).hom hxy q :=
  TopCat.IsPlusConstructionAt.fundamentalGroupQuotientMulEquiv_mk
    h hsurj q

/-- Inverse formula for the image of a represented source loop. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_symm_map
    (h : CGWH.IsPlusConstructionAt f x y hxy P)
    (hsurj : Function.Surjective
      (FundamentalGroup.mapOfEq (cgwhToTop.map f).hom hxy))
    (q : FundamentalGroup (cgwhToTop.obj X) x) :
    (h.fundamentalGroupQuotientMulEquiv hsurj).symm
        (FundamentalGroup.mapOfEq (cgwhToTop.map f).hom hxy q) =
      QuotientGroup.mk q :=
  TopCat.IsPlusConstructionAt.fundamentalGroupQuotientMulEquiv_symm_map
    h hsurj q

end IsPlusConstructionAt
end CGWH

end
