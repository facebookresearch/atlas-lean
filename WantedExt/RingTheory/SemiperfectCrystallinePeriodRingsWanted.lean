/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings

/-!
# Universal semiperfect PD-envelope construction

Scholze--Weinstein, arXiv:1211.6357v2, Proposition 4.1.3, p. 30.
These requests construct the universal PD hull and its original residue
dictionary. The actual p-adic completion and localization are completed
definitions. No new generic Witt, perfection or completion theory is requested.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.RingTheory.SemiperfectCrystallinePeriodRings

open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings

/-- Construct the universal PD hull of the full original Witt kernel. -/
public def_wanted universalWittPDEnvelope
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) : UniversalEnvelope p R

/-- Identify its residue with the original semiperfect R on every Witt coefficient. -/
public def_wanted universalWittPDResidue
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) : ResidueIdentification A

/-- Extend the original Witt Frobenius through the universal PD hull. -/
public def_wanted universalWittPDFrobenius
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) : HullFrobenius (A := A)

end WantedExt.RingTheory.SemiperfectCrystallinePeriodRings
