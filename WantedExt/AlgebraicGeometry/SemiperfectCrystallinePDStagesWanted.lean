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

/-- **Divided powers on the finite stages of the crystalline period ring.** Let $p$ be a prime,
$R$ a semiperfect ring of characteristic $p$ (its Frobenius is surjective), $A$ the universal PD
hull of $W(R^\flat) \to R$, where $R^\flat$ is the inverse perfection of $R$ (`UniversalEnvelope`:
initial among the PD algebras under $W(R^\flat)$ whose PD ideal contains the kernel of
$W(R^\flat) \to R$ and whose divided powers are compatible with those of $p\mathbb{Z}_p$), and $E$
an identification of its residue ring with $R$ compatible with the Witt coefficients
(`ResidueIdentification`). Then there are divided powers on the kernel of the residue map
$A_{cris}/p^{n+1} → R$ for every $n$, where $A_{cris}$ is the $p$-adic completion of $A$, such that
the maps from $A$ and the transition maps $A_{cris}/p^{m+1} → A_{cris}/p^{n+1}$ for $n ≤ m$ are PD
morphisms (`PDStages`). -/
public def_wanted completedWittPDStages
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A) :
    PDStages p R A E

end WantedExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
