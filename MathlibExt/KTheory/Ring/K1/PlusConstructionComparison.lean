/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroup
public import MathlibExt.KTheory.Ring.K1.ClassifyingSpaceComparison

/-!
# Classical `K₁` of a stable-`BGL` plus model

Any verified plus construction on algebraic stable `BGL(R)`, relative to the
canonical stable-elementary subgroup, has fundamental group additively
equivalent to classical `K₁(R)`. The normalized loop of `g : StableGL R`
maps to `K1.proj g`.

This theorem is parameterized by an actual target and plus-construction
evidence. It neither postulates nor manufactures a plus target.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicKTheory
namespace StableGL

variable {R : Type u} [Ring R]
variable {Y : TopCat.{u}} (f : ordinaryBGL R ⟶ Y)
  (y : Y) (hbase : f (ordinaryBGLBasepoint R) = y)
  (hplus : TopCat.IsPlusConstructionAt f
    (ordinaryBGLBasepoint R) y hbase (BGLPlusSubgroup R))
  (hsurj : Function.Surjective
    (FundamentalGroup.mapOfEq f.hom hbase))

/-- The target fundamental group of a stable-`BGL` plus construction is
classical `K₁(R)`. -/
noncomputable def plusTargetFundamentalAddEquivK1 :
    Additive (FundamentalGroup Y y) ≃+ K1 R :=
  (hplus.fundamentalGroupQuotientMulEquiv hsurj).symm.toAdditive.trans
    (BGLPlusQuotient.addEquivK1 R)

/-- The image of the normalized stable-`GL` loop represents its classical
`K₁` class in every verified plus target. -/
@[simp]
theorem plusTargetFundamentalAddEquivK1_loop (g : StableGL R) :
    plusTargetFundamentalAddEquivK1 f y hbase hplus hsurj
        (Additive.ofMul
          (FundamentalGroup.mapOfEq f.hom hbase
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))))) =
      K1.proj g := by
  change BGLPlusQuotient.addEquivK1 R
      (Additive.ofMul
        ((hplus.fundamentalGroupQuotientMulEquiv hsurj).symm
          (FundamentalGroup.mapOfEq f.hom hbase
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)))))) = _
  rw [TopCat.IsPlusConstructionAt.fundamentalGroupQuotientMulEquiv_symm_map,
    BGLPlusQuotient.addEquivK1_loop]

section CGWH

variable {YCGWH : CGWH.{w, u}} (fCGWH : BGL.{w} R ⟶ YCGWH)
  (yCGWH : YCGWH) (hbaseCGWH : fCGWH (BGLBasepoint.{w} R) = yCGWH)
  (hplusCGWH : CGWH.IsPlusConstructionAt fCGWH
    (BGLBasepoint.{w} R) yCGWH hbaseCGWH
      (BGLPlusSubgroupCGWH.{w} R))
  (hsurjCGWH : Function.Surjective
    (FundamentalGroup.mapOfEq
      (CGWH.cgwhToTop.map fCGWH).hom hbaseCGWH))

/-- The target fundamental group of a native-CGWH stable-`BGL` plus
construction is classical `K₁(R)`. -/
noncomputable def plusTargetCGWHFundamentalAddEquivK1 :
    Additive
        (FundamentalGroup (CGWH.cgwhToTop.obj YCGWH) yCGWH) ≃+
      K1 R :=
  (CGWH.IsPlusConstructionAt.fundamentalGroupQuotientMulEquiv
      hplusCGWH hsurjCGWH).symm.toAdditive.trans
    (BGLPlusQuotientCGWH.addEquivK1.{w} R)

end CGWH

end StableGL
end AlgebraicKTheory

end
