/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NormalizedDieudonneFrobenius

/-!
# Source Frobenius base change and original covariant F/V identities

The original Cartier-normalized geometric group maps and the literal
completed coefficient Frobenius determine all maps. Construct the
isomorphism property of the native PD/Ext/limit/tensor base-change map
and prove both p-products. Every finite projection is fixed by the
original PD arrow. No independent base-change isomorphism is requested.

Source: BBM82; Scholze--Weinstein1211.6357v2, Section4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemiperfectDieudonneOperators

open _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps
open MathlibExt.AlgebraicGeometry.SemiperfectDieudonneOperators
open MathlibExt.AlgebraicGeometry.PDCrystallineFrobeniusMaps
open MathlibExt.AlgebraicGeometry.CrystallineFrobeniusSourceComparison
open MathlibExt.AlgebraicGeometry.NormalizedDieudonneFrobenius

/-- Construct actual Frobenius base change and the covariant group-induced F/V p-products. -/
public def_wanted dieudonneFrobeniusVerschiebung
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D)
    (N : SourceComparison p R A E P F₀ φ C G D Q) :
    OperatorsNormalization p R A E P F₀ φ C G D Q N

end WantedExt.AlgebraicGeometry.SemiperfectDieudonneOperators
