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

/-- Divided powers on the finite stages of $A_{\mathrm{cris}}$ compatible with Frobenius: let $p$ be
a prime, $R$ a semiperfect ring of characteristic $p$, $A$ the universal PD hull of
$W(R^\flat) \to R$ with its identification of residue ring with $R$, $F_0$ a PD endomorphism of $A$
lifting the Witt vector Frobenius, and φ its completion on $A_{\mathrm{cris}}$. Then there are
divided powers on the kernel of each $A_{\mathrm{cris}}/p^{n+1} \to R$, compatible with those of $A$
and with the transition maps (`PDStages`), for which φ induces PD endomorphisms of all these stages
compatible with the Frobenius of $R$ (`Compatibility`). -/
public def_wanted crystallineFrobeniusPDStages
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀) :
    {P : PDStages p R A E // Compatibility p R A E P F₀ φ}

/-- Comparison of the crystalline Dieudonné module of a $p$-divisible group with that of its
Frobenius twist: let $p$ be a prime, $R$ a semiperfect ring of characteristic $p$, $A$ the universal
PD hull of $W(R^\flat) \to R$ with its identification of residue ring with $R$, $F_0$ a PD
endomorphism of $A$ lifting the Witt vector Frobenius, and φ its completion on $A_{\mathrm{cris}}$,
with divided powers on the finite stages of $A_{\mathrm{cris}}$ compatible with φ (`PDStages`,
`Compatibility`), and let $G$ be a $p$-divisible group over $R$ with a Cartier dual tower and
Frobenius and Verschiebung maps on it (`CartierFrobeniusVerschiebung`). Then on every object of the
full PD crystalline site, restriction along Frobenius reindexing is continuous and exact, and
identifies the restricted structure sheaf with the structure sheaf and the restricted group sheaf of
the dual tower of $G$ with that of the dual tower of its Frobenius twist, compatibly with sections
and finite group points; and the Frobenius-reindexed crystalline $\mathcal{E}xt^1$ module of $G$ is
isomorphic to that of its Frobenius twist, compatibly with these identifications on every local
$\mathcal{E}xt$ class (`SourceComparison`). -/
public def_wanted crystallineFrobeniusSourceComparison
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D) :
    SourceComparison p R A E P F₀ φ C G D Q

/-- The crystalline Frobenius and Verschiebung of a $p$-divisible group over a semiperfect ring
compose to $p$: let $p$ be a prime, $R$ a semiperfect ring of characteristic $p$, $A$ the universal
PD hull of $W(R^\flat) \to R$ with its identification of residue ring with $R$, $F_0$ a PD
endomorphism of $A$ lifting the Witt vector Frobenius, and φ its completion on $A_{\mathrm{cris}}$,
with divided powers on the finite stages of $A_{\mathrm{cris}}$ compatible with φ (`PDStages`,
`Compatibility`); let $G$ be a $p$-divisible group over $R$ with a Cartier dual tower and Frobenius
and Verschiebung maps on it (`CartierFrobeniusVerschiebung`), and $N$ a comparison of the
Frobenius-reindexed crystalline Dieudonné module of $G$ with that of its Frobenius twist
(`SourceComparison`). Let $F$, from the Frobenius-reindexed module to the module of $G$, be $N$
followed by the map induced by the Verschiebung of $G$, and $V$, in the other direction, the map
induced by the Frobenius of $G$ followed by $N^{-1}$. Then $F \circ V = p$ and $V \circ F = p$
(`FullCrystalProducts`). -/
public theorem_wanted fullCrystallineFrobeniusProducts
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D)
    (N : SourceComparison p R A E P F₀ φ C G D Q) :
    FullCrystalProducts p R A E P F₀ φ C G D Q N

end WantedExt.AlgebraicGeometry.CrystallineFrobeniusNormalization
