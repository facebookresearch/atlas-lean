/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveCounitEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidEquivalence
public import
  MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpace
public import MathlibExt.CategoryTheory.ClassifyingSpace.Group
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Fundamental group of algebraic stable `BGL`

This file identifies the fundamental group of the ordinary realization
underlying algebraic `BGL(R)` with `StableGL R`. The comparison first inverts
the realization equivalence on fundamental groupoids, then applies the nerve
counit, and finally removes the deliberate opposite-group convention by
inversion.

The normalized loop associated to `g : StableGL R` is the realized edge
labelled by `op g⁻¹`; under the comparison it maps to `g`. The native CGWH
classifying space is related to this ordinary realization by the canonical
forgetful isomorphism supplied by `classifyingSpaceCGWHToTopIso`.

No plus construction or `Q`-construction comparison is asserted here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The nerve used to define algebraic stable `BGL`. -/
noncomputable abbrev classifyingNerve (R : Type u) [Semiring R] : SSet.{u} :=
  CategoryTheory.nerve (ClassifyingCategory R)

/-- The unique vertex of the stable-`GL` classifying nerve. -/
noncomputable def classifyingVertex (R : Type u) [Semiring R] :
    classifyingNerve R _⦋0⦌ :=
  CategoryTheory.nerveEquiv.symm
    (SingleObj.star (StableGL R)ᵐᵒᵖ)

/-- The nerve loop normalized so that the fundamental-group comparison sends
it to `g`, rather than to `g⁻¹`. -/
noncomputable def normalizedClassifyingEdge {R : Type u} [Semiring R]
    (g : StableGL R) :
    (classifyingNerve R).Edge
      (classifyingVertex R) (classifyingVertex R) :=
  CategoryTheory.nerve.edgeMk (MulOpposite.op g⁻¹)

/-- Ordinary topological realization of the classifying nerve. The canonical
algebraic `BGL` object itself remains the CGWH realization `BGL R`. -/
noncomputable abbrev ordinaryBGL (R : Type u) [Semiring R] : TopCat.{u} :=
  SSet.toTop.obj (classifyingNerve R)

/-- Basepoint of the ordinary realization represented by the unique vertex. -/
noncomputable def ordinaryBGLBasepoint (R : Type u) [Semiring R] :
    ordinaryBGL R :=
  SSet.realizedVertex (classifyingVertex R)

/-- Basepoint of the canonical native CGWH algebraic `BGL`. -/
noncomputable def BGLBasepoint (R : Type u) [Semiring R] : BGL.{w} R :=
  CategoryTheory.classifyingSpaceCGWHPoint.{w}
    (SingleObj.star (StableGL R)ᵐᵒᵖ)

/-- The normalized realized loop associated to a stable invertible matrix. -/
noncomputable def ordinaryBGLLoop {R : Type u} [Semiring R]
    (g : StableGL R) :
    Path (ordinaryBGLBasepoint R) (ordinaryBGLBasepoint R) :=
  TopCat.pathEquiv
    (SSet.realizedEdgePath (normalizedClassifyingEdge g))

/-- Canonical multiplicative equivalence from the fundamental group of the
ordinary realization of algebraic `BGL(R)` to `StableGL R`. -/
noncomputable def ordinaryBGLFundamentalMulEquiv
    (R : Type u) [Semiring R] :
    FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) ≃*
      StableGL R :=
  (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
      (classifyingNerve R) (classifyingVertex R)).symm.trans
    ((SSet.fundamentalGroupoidNerveCounit_endMulEquiv
      (ClassifyingCategory R)
      (SingleObj.star (StableGL R)ᵐᵒᵖ)).trans
        ((SingleObj.toEnd ((StableGL R)ᵐᵒᵖ)).symm.trans
          (MulEquiv.inv' (StableGL R)).symm))

/-- The normalized realized edge loop represents the given stable matrix. -/
@[simp]
theorem ordinaryBGLFundamentalMulEquiv_loop
    {R : Type u} [Semiring R] (g : StableGL R) :
    ordinaryBGLFundamentalMulEquiv R
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))) = g := by
  exact CategoryTheory.groupClassifyingNormalizedLoop_comparison (StableGL R) g

/-- Forgetting the canonical CGWH classifying space recovers the ordinary
realization used above. -/
noncomputable def BGLToOrdinaryTopIso (R : Type u) [Semiring R] :
    CGWH.cgwhToTop.obj (BGL.{w} R) ≅ ordinaryBGL R :=
  CategoryTheory.classifyingSpaceCGWHToTopIso.{w, u, 0}.app
    (Cat.of (ClassifyingCategory R))

/-- The forgetful comparison sends the CGWH basepoint to the ordinary
realized vertex. -/
theorem BGLToOrdinaryTopIso_hom_basepoint
    (R : Type u) [Semiring R] :
    (BGLToOrdinaryTopIso.{w} R).hom
        (BGLBasepoint.{w} R) =
      ordinaryBGLBasepoint R :=
  CategoryTheory.classifyingSpaceCGWHPoint_toTop
    (SingleObj.star (StableGL R)ᵐᵒᵖ)

/-- Canonical multiplicative equivalence from the fundamental group of the
native CGWH algebraic `BGL(R)` to `StableGL R`. -/
noncomputable def BGLFundamentalMulEquiv
    (R : Type u) [Semiring R] :
    FundamentalGroup (CGWH.cgwhToTop.obj (BGL.{w} R))
        (BGLBasepoint.{w} R) ≃* StableGL R :=
  (FundamentalGroup.mulEquivOfIsoAt
      (BGLToOrdinaryTopIso.{w} R)
      (BGLBasepoint.{w} R) (ordinaryBGLBasepoint R)
      (BGLToOrdinaryTopIso_hom_basepoint R)).trans
    (ordinaryBGLFundamentalMulEquiv R)


/-- Canonical carrier presentation of the original realized-basepoint computation. -/
@[simp]
theorem BGLToOrdinaryTopIso_hom_basepoint_simp
    (R : Type u) [Semiring R] :
    @DFunLike.coe
      (ContinuousMap (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (BGL.{w} R)))
        (ordinaryBGL R))
      (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (BGL.{w} R)))
      (fun _ => ordinaryBGL R) _
      (TopCat.Hom.hom
        (X := CGWH.cgwhToTop.obj (BGL.{w} R)) (Y := ordinaryBGL R)
        ((BGLToOrdinaryTopIso.{w} R).hom))
      (BGLBasepoint.{w} R) =
      ordinaryBGLBasepoint R := by
  simpa only [Functor.comp_obj] using (BGLToOrdinaryTopIso_hom_basepoint.{w} R)

end StableGL
end AlgebraicKTheory

end
