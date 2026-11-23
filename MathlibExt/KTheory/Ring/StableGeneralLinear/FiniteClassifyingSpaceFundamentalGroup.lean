/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpace
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.Stabilization

/-!
# Fundamental groups of finite algebraic `BGL`

This file identifies the fundamental group of the ordinary realization of
`BGLₙ(R)` with `GLₙ(R)`.  As for stable `BGL`, the classifying category uses
the opposite group because Mathlib's `SingleObj` composition reverses
multiplication.  The normalized edge labelled by `op g⁻¹` therefore maps to
`g` under the final multiplicative equivalence.

The native finite classifying space remains CGWH-valued; a canonical
forgetful isomorphism relates it to the ordinary realization used to define
the fundamental group.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The nerve used at the `n`th finite general-linear stage. -/
noncomputable abbrev finiteClassifyingNerve
    (R : Type u) [Semiring R] (n : ℕ) : SSet.{u} :=
  CategoryTheory.nerve
    (SingleObj
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)

/-- The unique vertex of the `n`th finite classifying nerve. -/
noncomputable def finiteClassifyingVertex
    (R : Type u) [Semiring R] (n : ℕ) :
    finiteClassifyingNerve R n _⦋0⦌ :=
  CategoryTheory.nerveEquiv.symm
    (SingleObj.star
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)

/-- The finite-stage nerve loop normalized to represent `g` under the
fundamental-group comparison. -/
noncomputable def finiteNormalizedClassifyingEdge
    {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (finiteClassifyingNerve R n).Edge
      (finiteClassifyingVertex R n)
      (finiteClassifyingVertex R n) :=
  CategoryTheory.nerve.edgeMk (MulOpposite.op g⁻¹)

/-- The finite-to-stable classifying functor sends a normalized finite arrow
to the normalized stable arrow. -/
@[simp↓]
theorem finiteToStableCategoryMap_map_normalized
    {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (finiteToStableCategoryMap R n).toFunctor.mapEnd
        (SingleObj.star
          (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
        (End.of (MulOpposite.op g⁻¹) : CategoryTheory.End
          (SingleObj.star
            (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) =
      (End.of (MulOpposite.op (StableGL.of g)⁻¹) : CategoryTheory.End
        (SingleObj.star (StableGL R)ᵐᵒᵖ)) := by
  apply End.ext
  change MulOpposite.op (StableGL.of g⁻¹) =
    MulOpposite.op (StableGL.of g)⁻¹
  rw [StableGL.of_inv]

/-- Ordinary realization of `BGLₙ(R)`. -/
noncomputable abbrev ordinaryFiniteBGL
    (R : Type u) [Semiring R] (n : ℕ) : TopCat.{u} :=
  SSet.toTop.obj (finiteClassifyingNerve R n)

/-- Canonical basepoint of the ordinary finite-stage realization. -/
noncomputable def ordinaryFiniteBGLBasepoint
    (R : Type u) [Semiring R] (n : ℕ) :
    ordinaryFiniteBGL R n :=
  SSet.realizedVertex (finiteClassifyingVertex R n)

/-- The normalized realized loop associated to a finite invertible matrix. -/
noncomputable def ordinaryFiniteBGLLoop
    {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Path (ordinaryFiniteBGLBasepoint R n)
      (ordinaryFiniteBGLBasepoint R n) :=
  TopCat.pathEquiv
    (SSet.realizedEdgePath (finiteNormalizedClassifyingEdge g))

/-- Canonical multiplicative equivalence from the fundamental group of
ordinary `BGLₙ(R)` to `GLₙ(R)`. -/
noncomputable def ordinaryFiniteBGLFundamentalMulEquiv
    (R : Type u) [Semiring R] (n : ℕ) :
    FundamentalGroup (ordinaryFiniteBGL R n)
        (ordinaryFiniteBGLBasepoint R n) ≃*
      Matrix.GeneralLinearGroup (Fin n) R :=
  (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
      (finiteClassifyingNerve R n)
      (finiteClassifyingVertex R n)).symm.trans
    ((SSet.fundamentalGroupoidNerveCounit_endMulEquiv
      (SingleObj
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).trans
      ((SingleObj.toEnd ((Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).symm.trans
        (MulEquiv.inv'
          (Matrix.GeneralLinearGroup (Fin n) R)).symm))

/-- The normalized finite-stage edge loop represents the given matrix. -/
@[simp]
theorem ordinaryFiniteBGLFundamentalMulEquiv_loop
    {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    ordinaryFiniteBGLFundamentalMulEquiv R n
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (ordinaryFiniteBGLLoop g))) = g := by
  exact CategoryTheory.groupClassifyingNormalizedLoop_comparison
    (Matrix.GeneralLinearGroup (Fin n) R) g


/-- Forgetting the native finite-stage CGWH realization recovers the
ordinary realization. -/
noncomputable def finiteBGLToOrdinaryTopIso
    (R : Type u) [Semiring R] (n : ℕ) :
    CGWH.cgwhToTop.obj (FiniteBGL.{w} R n) ≅
      ordinaryFiniteBGL R n :=
  CategoryTheory.classifyingSpaceCGWHToTopIso.{w, u, 0}.app
    (Cat.of (SingleObj
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))

/-- The finite-stage forgetful comparison preserves the selected
basepoint. -/
@[simp↓]
theorem finiteBGLToOrdinaryTopIso_hom_basepoint
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLToOrdinaryTopIso.{w} R n).hom
        (CategoryTheory.classifyingSpaceCGWHPoint.{w}
          (SingleObj.star
            (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) =
      ordinaryFiniteBGLBasepoint R n :=
  CategoryTheory.classifyingSpaceCGWHPoint_toTop
    (SingleObj.star
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)


/-- The actual finite arrow functor acts on every opposite-group element. -/
theorem finiteToStableCategoryMap_map_normalized_simp
    {R : Type u} [Semiring R] {n : ℕ}
    (r : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteToStableCategoryMap R n).toFunctor.mapEnd
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
        ({ asHom := r } : CategoryTheory.End
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) =
      ({ asHom := MulOpposite.op (StableGL.of (MulOpposite.unop r)) } : CategoryTheory.End
        (SingleObj.star (StableGL R)ᵐᵒᵖ)) := by
  simpa only [inv_inv, MulOpposite.op_unop, StableGL.of_inv]
    using finiteToStableCategoryMap_map_normalized (MulOpposite.unop r)⁻¹

/-- Inverting a finite representative gives the inverse of its actual stable image. -/
@[simp]
theorem finiteStableRepresentative_inv_simp
    {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (GrpCat.FilteredColimits.G.mk
      (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⁻¹⟩ : StableGL R) =
      (GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩ : StableGL R)⁻¹ :=
  StableGL.of_inv g

/-- The finite realization comparison is its original identity continuous map. -/
@[simp]
theorem finiteBGLToOrdinaryTopIso_hom_basepoint_simp
    (R : Type u) [Semiring R] (n : ℕ)
    (p : CompactlyGenerated.compactlyGeneratedToTop.obj
      (CGWH.cgwhToCompactlyGenerated.obj (FiniteBGL.{w} R n))) :
    @DFunLike.coe
      (ContinuousMap (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (FiniteBGL.{w} R n)))
        (ordinaryFiniteBGL R n))
      (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (FiniteBGL.{w} R n)))
      (fun _ => ordinaryFiniteBGL R n) _
      (ConcreteCategory.hom (C := TopCat.{u})
        (X := CGWH.cgwhToTop.obj (FiniteBGL.{w} R n)) (Y := ordinaryFiniteBGL R n)
        ((finiteBGLToOrdinaryTopIso.{w} R n).hom)) p =
      (show ordinaryFiniteBGL R n from p) := rfl

/-- The actual finite native point has the original ordinary vertex value. -/
@[simp]
theorem finiteBGLPoint_ordinary_value_simp
    (R : Type u) [Semiring R] (n : ℕ) :
    (show ordinaryFiniteBGL R n from
      @CategoryTheory.classifyingSpaceCGWHPoint.{w, u, 0}
        (SingleObj ((Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
        (SingleObj.category ((Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
        (SingleObj.star ((Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))) =
      ordinaryFiniteBGLBasepoint R n := rfl

end StableGL
end AlgebraicKTheory

end
