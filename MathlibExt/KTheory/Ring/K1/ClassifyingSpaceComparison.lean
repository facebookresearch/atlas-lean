/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpacePlusSubgroup

/-!
# Stable-`BGL` quotient and classical `K₁`

Quotienting `π₁(BGL(R))` by the canonical plus subgroup gives the Whitehead
quotient `StableGL(R)/StableE(R)`, and hence classical `K₁(R)`.

This is the algebraic fundamental-group consequence required of any future
plus-construction target. It does not assume that a plus construction has
already been built.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The canonical homomorphism from `π₁(BGL(R))` to the Whitehead quotient. -/
noncomputable def BGLPlusQuotient.toWhiteheadHom
    (R : Type u) [Ring R] :
    FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) →*
      WhiteheadQuotient R :=
  (QuotientGroup.mk' (stableElementarySubgroup R)).comp
    (ordinaryBGLFundamentalMulEquiv R).toMonoidHom

/-- The canonical homomorphism to the Whitehead quotient is surjective. -/
theorem BGLPlusQuotient.toWhiteheadHom_surjective
    (R : Type u) [Ring R] :
    Function.Surjective (BGLPlusQuotient.toWhiteheadHom R) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (stableElementarySubgroup R) q
  refine ⟨(ordinaryBGLFundamentalMulEquiv R).symm g, ?_⟩
  change QuotientGroup.mk' (stableElementarySubgroup R)
      (ordinaryBGLFundamentalMulEquiv R
        ((ordinaryBGLFundamentalMulEquiv R).symm g)) =
    QuotientGroup.mk' (stableElementarySubgroup R) g
  rw [(ordinaryBGLFundamentalMulEquiv R).apply_symm_apply]

/-- The quotient of `π₁(BGL(R))` by the plus subgroup is the Whitehead
quotient `StableGL(R)/StableE(R)`. -/
noncomputable def BGLPlusQuotient.mulEquivWhitehead
    (R : Type u) [Ring R] :
    FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) ⧸
        BGLPlusSubgroup R ≃*
      WhiteheadQuotient R :=
  let φ := BGLPlusQuotient.toWhiteheadHom R
  have hker : BGLPlusSubgroup R = MonoidHom.ker φ := by
    change (stableElementarySubgroup R).comap
        (ordinaryBGLFundamentalMulEquiv R).toMonoidHom =
      MonoidHom.ker
        ((QuotientGroup.mk' (stableElementarySubgroup R)).comp
          (ordinaryBGLFundamentalMulEquiv R).toMonoidHom)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ
      (BGLPlusQuotient.toWhiteheadHom_surjective R))

@[simp]
theorem BGLPlusQuotient.mulEquivWhitehead_mk
    (R : Type u) [Ring R]
    (q : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R)) :
    BGLPlusQuotient.mulEquivWhitehead R
        (QuotientGroup.mk q) =
      QuotientGroup.mk
        (ordinaryBGLFundamentalMulEquiv R q) :=
  by
    unfold BGLPlusQuotient.mulEquivWhitehead
    dsimp only [MulEquiv.trans_apply]
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    change QuotientGroup.kerLift
        (BGLPlusQuotient.toWhiteheadHom R)
        (QuotientGroup.mk q) = _
    rw [QuotientGroup.kerLift_mk]
    rfl

/-- Additive equivalence from the quotient of `π₁(BGL(R))` by the plus
subgroup to classical `K₁(R)`. -/
noncomputable def BGLPlusQuotient.addEquivK1
    (R : Type u) [Ring R] :
    Additive
        (FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) ⧸
          BGLPlusSubgroup R) ≃+
      K1 R :=
  (BGLPlusQuotient.mulEquivWhitehead R).toAdditive.trans
    (WhiteheadQuotient.addEquivK1 R)

/-- The normalized `BGL` loop of `g` maps to its classical `K₁` class. -/
@[simp]
theorem BGLPlusQuotient.addEquivK1_loop
    (R : Type u) [Ring R] (g : StableGL R) :
    BGLPlusQuotient.addEquivK1 R
        (Additive.ofMul
          (QuotientGroup.mk
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))))) =
      K1.proj g := by
  change WhiteheadQuotient.addEquivK1 R
      (Additive.ofMul
        (BGLPlusQuotient.mulEquivWhitehead R
          (QuotientGroup.mk
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)))))) = _
  rw [BGLPlusQuotient.mulEquivWhitehead_mk,
    ordinaryBGLFundamentalMulEquiv_loop]
  rfl

/-- Canonical homomorphism from the fundamental group of native CGWH
`BGL(R)` to the Whitehead quotient. -/
noncomputable def BGLPlusQuotientCGWH.toWhiteheadHom
    (R : Type u) [Ring R] :
    FundamentalGroup (CGWH.cgwhToTop.obj (BGL.{w} R))
        (BGLBasepoint.{w} R) →* WhiteheadQuotient R :=
  (QuotientGroup.mk' (stableElementarySubgroup R)).comp
    (BGLFundamentalMulEquiv.{w} R).toMonoidHom

theorem BGLPlusQuotientCGWH.toWhiteheadHom_surjective
    (R : Type u) [Ring R] :
    Function.Surjective (BGLPlusQuotientCGWH.toWhiteheadHom.{w} R) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (stableElementarySubgroup R) q
  refine ⟨(BGLFundamentalMulEquiv.{w} R).symm g, ?_⟩
  change QuotientGroup.mk' (stableElementarySubgroup R)
      (BGLFundamentalMulEquiv.{w} R
        ((BGLFundamentalMulEquiv.{w} R).symm g)) =
    QuotientGroup.mk' (stableElementarySubgroup R) g
  rw [(BGLFundamentalMulEquiv.{w} R).apply_symm_apply]

/-- The native-CGWH fundamental-group quotient is the Whitehead quotient. -/
noncomputable def BGLPlusQuotientCGWH.mulEquivWhitehead
    (R : Type u) [Ring R] :
    FundamentalGroup (CGWH.cgwhToTop.obj (BGL.{w} R))
          (BGLBasepoint.{w} R) ⧸ BGLPlusSubgroupCGWH.{w} R ≃*
      WhiteheadQuotient R :=
  let phi := BGLPlusQuotientCGWH.toWhiteheadHom.{w} R
  have hker : BGLPlusSubgroupCGWH.{w} R = MonoidHom.ker phi := by
    change (stableElementarySubgroup R).comap
        (BGLFundamentalMulEquiv.{w} R).toMonoidHom =
      MonoidHom.ker
        ((QuotientGroup.mk' (stableElementarySubgroup R)).comp
          (BGLFundamentalMulEquiv.{w} R).toMonoidHom)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective phi
      (BGLPlusQuotientCGWH.toWhiteheadHom_surjective R))

/-- Additive equivalence from the native-CGWH `BGL` plus quotient to
classical `K₁(R)`. -/
noncomputable def BGLPlusQuotientCGWH.addEquivK1
    (R : Type u) [Ring R] :
    Additive
        (FundamentalGroup (CGWH.cgwhToTop.obj (BGL.{w} R))
          (BGLBasepoint.{w} R) ⧸ BGLPlusSubgroupCGWH.{w} R) ≃+
      K1 R :=
  (BGLPlusQuotientCGWH.mulEquivWhitehead.{w} R).toAdditive.trans
    (WhiteheadQuotient.addEquivK1 R)

end StableGL
end AlgebraicKTheory

end
