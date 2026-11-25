/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages

/-!
# Divided powers on the literal finite completed universal hull

All finite rings, residue ideals, coefficient maps and quotient
transitions are already fixed. This request constructs only their
compatible original divided powers. Uniform ideal nilpotence and
p-torsionfreeness are not hypotheses.

Source: Scholze--Weinstein1211.6357v2, Proposition4.1.3 and Lemma4.1.8.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemiperfectCrystallinePDStages

open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages

/-- Construct compatible divided powers on the full original A_cris/p^(n+1) kernels. -/
public def_wanted completedWittPDStages
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A) :
    PDStages p R A E

end WantedExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
