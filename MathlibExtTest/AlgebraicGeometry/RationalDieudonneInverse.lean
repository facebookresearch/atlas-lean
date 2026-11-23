/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RationalDieudonneOperators
import MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels

/-!
Consumer tests for the final crystalline F/V pipeline. From the two product equations of the actual
rational maps, linearised Frobenius on the rational Dieudonné module over `B_cris⁺ = A_cris[1/p]`
is an isomorphism whose inverse is `p⁻¹ V`. On the full crystal, either p-product makes Frobenius
commute with multiplication by `p` through Verschiebung.
-/

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.AlgebraicGeometry
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.RationalDieudonneInverse

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (Q : CartierFrobeniusVerschiebung p R G D)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)

/-- The inverse of `p` in `B_cris⁺ = A_cris[1/p]`. -/
abbrev pInv : BcrisPlus p R A := IsLocalization.Away.invSelf (p : Acris p R A)

theorem natCast_mul_pInv : (p : BcrisPlus p R A) * pInv p R A = 1 := by
  simpa [map_natCast] using
    IsLocalization.Away.mul_invSelf (S := BcrisPlus p R A) (p : Acris p R A)

variable (O : SemiperfectDieudonneOperators.OperatorsRealization p R A E P G D Q F₀ φ)

/-- `p⁻¹ V` is a right inverse of rational linearised Frobenius. -/
theorem frobenius_comp_pInv_verschiebung :
    RationalDieudonneOperators.frobenius p R A E P G D Q F₀ φ O.baseChange ≫
        (pInv p R A • RationalDieudonneOperators.verschiebung p R A E P G D Q F₀ φ O.baseChange) =
      𝟙 _ := by
  rw [Linear.comp_smul, RationalDieudonneOperators.frobenius_verschiebung p R A E P G D Q F₀ φ O,
    ← Nat.cast_smul_eq_nsmul (BcrisPlus p R A), smul_smul, mul_comm, natCast_mul_pInv, one_smul]

/-- `p⁻¹ V` is a left inverse of rational linearised Frobenius. -/
theorem pInv_verschiebung_comp_frobenius :
    (pInv p R A • RationalDieudonneOperators.verschiebung p R A E P G D Q F₀ φ O.baseChange) ≫
        RationalDieudonneOperators.frobenius p R A E P G D Q F₀ φ O.baseChange =
      𝟙 _ := by
  rw [Linear.smul_comp, RationalDieudonneOperators.verschiebung_frobenius p R A E P G D Q F₀ φ O,
    ← Nat.cast_smul_eq_nsmul (BcrisPlus p R A), smul_smul, mul_comm, natCast_mul_pInv, one_smul]

/-- Rational linearised Frobenius is an isomorphism. -/
theorem frobenius_isIso :
    IsIso (RationalDieudonneOperators.frobenius p R A E P G D Q F₀ φ O.baseChange) :=
  ⟨_, frobenius_comp_pInv_verschiebung p R A E P G D Q F₀ φ O,
    pInv_verschiebung_comp_frobenius p R A E P G D Q F₀ φ O⟩

/-- Its inverse is `p⁻¹ V`. -/
example :
    haveI := frobenius_isIso p R A E P G D Q F₀ φ O
    inv (RationalDieudonneOperators.frobenius p R A E P G D Q F₀ φ O.baseChange) =
      pInv p R A • RationalDieudonneOperators.verschiebung p R A E P G D Q F₀ φ O.baseChange :=
  haveI := frobenius_isIso p R A E P G D Q F₀ φ O
  IsIso.inv_eq_of_hom_inv_id (frobenius_comp_pInv_verschiebung p R A E P G D Q F₀ φ O)

open DieudonneFrobeniusProjectionModels CrystallineFrobeniusSourceComparison
  PDCrystallineFrobeniusMaps in
/-- On the full crystal, the first p-product makes `F V F = p F`. -/
example (C : Compatibility p R A E P F₀ φ) (N : SourceComparison p R A E P F₀ φ C G D Q)
    (h : FullCrystalProducts p R A E P F₀ φ C G D Q N) :
    crystallineFrobenius p R A E P F₀ φ C G D Q N ≫
        crystallineVerschiebung p R A E P F₀ φ C G D Q N ≫
          crystallineFrobenius p R A E P F₀ φ C G D Q N =
      p • crystallineFrobenius p R A E P F₀ φ C G D Q N := by
  rw [h.vf, Preadditive.comp_nsmul, Category.comp_id]

end MathlibExtTest.AlgebraicGeometry.RationalDieudonneInverse

#print axioms MathlibExtTest.AlgebraicGeometry.RationalDieudonneInverse.frobenius_isIso
#print axioms MathlibExt.AlgebraicGeometry.RationalDieudonneOperators.frobenius_verschiebung
#print axioms
  MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels.liftedLimitMap_projection
