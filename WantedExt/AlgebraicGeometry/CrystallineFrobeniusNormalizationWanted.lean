/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels

/-!
# Source-normalized native crystalline Frobenius comparison

Construct original compatible PD stages and the native slice/Cartier/Ext
comparison on every coefficient and finite point, and prove the full crystal
p-products. The isomorphism and F/V properties of the already-defined native
limit/tensor map are requested once, as
`WantedExt.AlgebraicGeometry.SemiperfectDieudonneOperators.dieudonneFrobeniusVerschiebung`.
No independent module isomorphism or invertible ring Frobenius is supplied.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CrystallineFrobeniusNormalization

open _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps
open MathlibExt.AlgebraicGeometry.PDCrystallineFrobeniusMaps
open MathlibExt.AlgebraicGeometry.CrystallineFrobeniusSourceComparison
open MathlibExt.AlgebraicGeometry.NormalizedDieudonneFrobenius
open MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels

/-- Construct the original full PD stages compatible with this exact completed Frobenius. -/
public def_wanted crystallineFrobeniusPDStages
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀) :
    {P : PDStages p R A E // Compatibility p R A E P F₀ φ}

/-- Construct the exact native slice/finite-point/ring-unit Ext comparison on the full PD basis. -/
public def_wanted crystallineFrobeniusSourceComparison
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D) :
    SourceComparison p R A E P F₀ φ C G D Q

/-- Prove the full crystal p-products for those same native group-induced sheaf maps. -/
public theorem_wanted fullCrystallineFrobeniusProducts
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D)
    (N : SourceComparison p R A E P F₀ φ C G D Q) :
    FullCrystalProducts p R A E P F₀ φ C G D Q N

end WantedExt.AlgebraicGeometry.CrystallineFrobeniusNormalization
