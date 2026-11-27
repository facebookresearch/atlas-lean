/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemiperfectDieudonneOperators
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Literal B_cris⁺ Frobenius and rational covariant F/V

The coefficient Frobenius is the native localization lift of the actual
A_cris Frobenius. Tensor composition supplies the rational twist
comparison. Rational F/V are scalar extensions of the original geometric
group-induced maps, transported by this exact tensor comparison.
No inverse Frobenius on either ring is used.

Source: Scholze--Weinstein1211.6357v2, Section4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RationalDieudonneOperators

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (Q : CartierFrobeniusVerschiebung p R G D)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)

/-- The original p-localization coefficient map. -/
abbrev rationalCoefficients : Acris p R A →+* BcrisPlus p R A := algebraMap _ _

/-- Native scalar extension is additive by its actual extension/restriction adjunction. -/
instance rationalExtension_additive :
    (ModuleCat.extendScalars.{0, 0, 1} (rationalCoefficients p R A)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{1, 0, 0}
    (rationalCoefficients p R A)).left_adjoint_additive

/-- B_cris⁺ Frobenius is the native localization of the completed coefficient Frobenius. -/
def coefficientFrobenius : BcrisPlus p R A →+* BcrisPlus p R A :=
  IsLocalization.Away.lift (p : Acris p R A)
    (g := (rationalCoefficients p R A).comp φ.hom) (by
      simpa only [RingHom.comp_apply, map_natCast] using
        (IsLocalization.Away.algebraMap_isUnit (p : Acris p R A)
          (S := BcrisPlus p R A)))

/-- Rational Frobenius preserves every original A_cris coefficient. -/
theorem coefficientFrobenius_coefficients :
    (coefficientFrobenius p R A F₀ φ).comp (rationalCoefficients p R A) =
      (rationalCoefficients p R A).comp φ.hom :=
  IsLocalization.Away.lift_comp _ _

/-- The rational twist is actual tensor extension along B_cris⁺ Frobenius. -/
def frobeniusPullback : ModuleCat.{1} (BcrisPlus p R A) :=
  (ModuleCat.extendScalars (coefficientFrobenius p R A F₀ φ)).obj
    (rationalModule p R A E P G D)

/-- Native scalar-extension composition fixes the rational and integral tensor twists. -/
def twistComparison : frobeniusPullback p R A E P G D F₀ φ ≅
    (ModuleCat.extendScalars (rationalCoefficients p R A)).obj
      (SemiperfectDieudonneOperators.frobeniusPullback p R A E P G D F₀ φ) :=
  (ModuleCat.extendScalarsComp (rationalCoefficients p R A)
    (coefficientFrobenius p R A F₀ φ)).symm.app (integralModule p R A E P G D) ≪≫
  eqToIso (congrArg (fun f : Acris p R A →+* BcrisPlus p R A =>
    (ModuleCat.extendScalars f).obj (integralModule p R A E P G D))
      (coefficientFrobenius_coefficients p R A F₀ φ)) ≪≫
  (ModuleCat.extendScalarsComp φ.hom (rationalCoefficients p R A)).app
    (integralModule p R A E P G D)

variable (c : SemiperfectDieudonneOperators.frobeniusPullback p R A E P G D F₀ φ ≅
  integralModule p R A E P Q.source.twist.group Q.dualTwist)

/-- Rational F is literal scalar extension of the original group-V-induced integral map. -/
def frobenius : frobeniusPullback p R A E P G D F₀ φ ⟶ rationalModule p R A E P G D :=
  (twistComparison p R A E P G D F₀ φ).hom ≫
    (ModuleCat.extendScalars (rationalCoefficients p R A)).map
      (SemiperfectDieudonneOperators.frobenius p R A E P G D Q F₀ φ c)

/-- Rational V is literal scalar extension of the original group-F-induced integral map. -/
def verschiebung : rationalModule p R A E P G D ⟶ frobeniusPullback p R A E P G D F₀ φ :=
  (ModuleCat.extendScalars (rationalCoefficients p R A)).map
    (SemiperfectDieudonneOperators.verschiebung p R A E P G D Q F₀ φ c) ≫
      (twistComparison p R A E P G D F₀ φ).inv

variable (O : SemiperfectDieudonneOperators.OperatorsRealization p R A E P G D Q F₀ φ)

/-- The actual rational maps inherit the first p-product by native scalar extension. -/
theorem verschiebung_frobenius :
    verschiebung p R A E P G D Q F₀ φ O.baseChange ≫
      frobenius p R A E P G D Q F₀ φ O.baseChange =
        p • 𝟙 (rationalModule p R A E P G D) := by
  simp only [verschiebung, frobenius, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, O.vf, Functor.map_nsmul]
  exact congrArg (fun f => p • f)
    ((ModuleCat.extendScalars.{0, 0, 1} (rationalCoefficients p R A)).map_id
      (integralModule p R A E P G D))

/-- The actual rational maps inherit the second p-product on the literal Frobenius twist. -/
theorem frobenius_verschiebung :
    frobenius p R A E P G D Q F₀ φ O.baseChange ≫
      verschiebung p R A E P G D Q F₀ φ O.baseChange =
        p • 𝟙 (frobeniusPullback p R A E P G D F₀ φ) := by
  simp only [verschiebung, frobenius, Category.assoc,
    ← Functor.map_comp_assoc, O.fv, Functor.map_nsmul,
    Preadditive.nsmul_comp, Preadditive.comp_nsmul]
  rw [(ModuleCat.extendScalars.{0, 0, 1} (rationalCoefficients p R A)).map_id
    (SemiperfectDieudonneOperators.frobeniusPullback p R A E P G D F₀ φ)]
  simp only [Category.id_comp, Iso.hom_inv_id]

end MathlibExt.AlgebraicGeometry.RationalDieudonneOperators
