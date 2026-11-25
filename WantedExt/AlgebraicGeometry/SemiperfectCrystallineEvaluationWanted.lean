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

/-- PD tests over the universal hull factor through the finite stages of $A_{\mathrm{cris}}$: let
$p$ be a prime, $R$ a semiperfect ring of characteristic $p$, $A$ the universal PD hull of
$W(R^\flat) \to R$ with its identification of residue ring with $R$, with divided powers on the
finite stages of $A_{\mathrm{cris}}$ (`PDStages`), and $B$ a full PD test over $A$ with
$p^{n+1} = 0$ in $B$. Then there is a morphism of PD tests from $B$ to the stage
$A_{\mathrm{cris}}/p^{n+1}$ whose ring map $A_{\mathrm{cris}}/p^{n+1} \to B$ is the one induced by
the structure map $A \to B$ (`TargetFactorization`). -/
public def_wanted universalCrystallinePDTargetFactorization
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E)
    (B : MathlibExt.AlgebraicGeometry.FullPDCrystallineTests.Obj p
      (hullPDBase p R A) (baseScheme p R A E))
    (n : ℕ) (hn : (p : B.ring) ^ (n + 1) = 0) : TargetFactorization p R A E P B n hn

/-- The crystalline Dieudonné module of a $p$-divisible group over a semiperfect ring, evaluated on
$A_{\mathrm{cris}}$: let $p$ be a prime, $R$ a semiperfect ring of characteristic $p$, $A$ the
universal PD hull of $W(R^\flat) \to R$ with its identification of residue ring with $R$, with
divided powers on the finite stages of $A_{\mathrm{cris}}$ (`PDStages`), and $G$ a $p$-divisible
group over $R$ with a Cartier dual tower $D$. Then the crystalline $\mathcal{E}xt^1$ module of $D$
on the full PD site is a crystal of finite projective modules identified with the internal
$\mathcal{E}xt^1$ (`CrystalRealization`); its value $M$ on $A_{\mathrm{cris}}$, the limit of its
values on the finite stages, is a finite projective $A_{\mathrm{cris}}$-module and $M[1/p]$ a finite
projective $B_{\mathrm{cris}}^+$-module; and for every PD test $C$ with $p^{k+1} = 0$ and every
factorization of $C$ through $A_{\mathrm{cris}}/p^{k+1}$ (`TargetFactorization`), the induced map
$M \otimes_{A_{\mathrm{cris}}} C \to M(C)$ is an isomorphism (`AcrisRealization`). -/
public def_wanted universalAcrisDieudonneEvaluation
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) : AcrisRealization p R A E P G D

end WantedExt.AlgebraicGeometry.SemiperfectCrystallineEvaluation
