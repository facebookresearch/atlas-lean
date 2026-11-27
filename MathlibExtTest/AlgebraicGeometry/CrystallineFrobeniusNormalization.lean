/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CrystallineFrobeniusNormalization

/-!
# Crystalline Frobenius product tests

Derive the triple-composition identity from the full crystalline products.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.CrystallineFrobeniusNormalization

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.AlgebraicGeometry
open SemiperfectCrystallinePDStages PDivisibleGroupSchemes PDivisibleCartierTowerModels
open PDivisibleCartierGroupMaps PDCrystallineFrobeniusMaps CrystallineFrobeniusSourceComparison
open DieudonneFrobeniusProjectionModels
open WantedExt.AlgebraicGeometry.CrystallineFrobeniusNormalization

/-- The full crystalline products imply `F V F = p F`. -/
public theorem frobenius_verschiebung_frobenius
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D)
    (N : SourceComparison p R A E P F₀ φ C G D Q) :
    crystallineFrobenius p R A E P F₀ φ C G D Q N ≫
        crystallineVerschiebung p R A E P F₀ φ C G D Q N ≫
          crystallineFrobenius p R A E P F₀ φ C G D Q N =
      p • crystallineFrobenius p R A E P F₀ φ C G D Q N := by
  have h := fullCrystallineFrobeniusProducts p R hR A E P F₀ φ C G D Q N
  rw [h.vf, Preadditive.comp_nsmul, Category.comp_id]

end MathlibExtTest.AlgebraicGeometry.CrystallineFrobeniusNormalization
