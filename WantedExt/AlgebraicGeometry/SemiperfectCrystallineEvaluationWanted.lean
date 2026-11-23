/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SemiperfectCrystallineEvaluationMaps

/-!
# Universal crystalline evaluation on every full PD test over the universal hull

All rings, scalar maps, Ext modules, inverse limits and evaluation maps
are completed definitions. PD factorization, finite projectivity and
the actual normalized tensor/Ext comparisons are construction outputs.
The tests are hull algebras, so the factorization request concerns an already hull-linear test;
it does not ask for the hull map of a bare PD thickening of `R`.

Source: BBM82; Scholze--Weinstein1211.6357v2, Section3.2 and Proposition4.1.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemiperfectCrystallineEvaluation

open _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
open MathlibExt.AlgebraicGeometry.SemiperfectCrystallineEvaluationMaps
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels

/-- Construct the original full-PD arrow for the fixed universal coefficient factor. -/
public def_wanted universalCrystallinePDTargetFactorization
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E)
    (B : MathlibExt.AlgebraicGeometry.FullPDCrystallineTests.Obj p
      (hullPDBase p R A) (baseScheme p R A E))
    (n : ℕ) (hn : (p : B.ring) ^ (n + 1) = 0) : TargetFactorization p R A E P B n hn

/-- Establish the full native Ext crystal and every original A_cris/PD-test tensor comparison. -/
public def_wanted universalAcrisDieudonneEvaluation
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) : AcrisRealization p R A E P G D

end WantedExt.AlgebraicGeometry.SemiperfectCrystallineEvaluation
