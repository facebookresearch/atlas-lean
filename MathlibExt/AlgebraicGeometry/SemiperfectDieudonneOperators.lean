/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemiperfectCrystallineModuleLimits

/-!
# Covariant Dieudonne F/V from the original geometric group maps

The Frobenius twist is literal tensor extension along the original
completed Witt/PD-hull Frobenius. Covariant F is induced by the group's
Verschiebung, and V by its relative Frobenius. A source crystal/base-change
comparison is an explicit construction output; the operators are defined
by composing that comparison with the native original group module maps.
Both p-composite identities remain proof outputs. Frobenius invertibility
is never assumed.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemiperfectDieudonneOperators

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (Q : CartierFrobeniusVerschiebung p R G D)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)

/-- The source twist is tensor extension along the actual completed coefficient Frobenius. -/
def frobeniusPullback : ModuleCat.{1} (Acris p R A) :=
  (ModuleCat.extendScalars φ.hom).obj (integralModule p R A E P G D)

/-- The module map of the original relative group Frobenius. -/
def groupFrobeniusMap : integralModule p R A E P G D ⟶
    integralModule p R A E P Q.source.twist.group Q.dualTwist :=
  Maps.integralMap p R A E P D Q.dualTwist
    (frobeniusHom p R G Q.source) Q.dualFrobenius

/-- The module map of the original Cartier-normalized group Verschiebung. -/
def groupVerschiebungMap : integralModule p R A E P Q.source.twist.group Q.dualTwist ⟶
    integralModule p R A E P G D :=
  Maps.integralMap p R A E P Q.dualTwist D
    (verschiebungHom p R G Q.source) Q.dualVerschiebung

variable (c : frobeniusPullback p R A E P G D F₀ φ ≅
  integralModule p R A E P Q.source.twist.group Q.dualTwist)

/-- Covariant F comes from original group V, after the source Frobenius base-change map. -/
def frobenius : frobeniusPullback p R A E P G D F₀ φ ⟶ integralModule p R A E P G D :=
  c.hom ≫ groupVerschiebungMap p R A E P G D Q

/-- Covariant V comes from original group F, with the same source base-change map. -/
def verschiebung : integralModule p R A E P G D ⟶ frobeniusPullback p R A E P G D F₀ φ :=
  groupFrobeniusMap p R A E P G D Q ≫ c.inv

/-- Frobenius and Verschiebung on the integral Dieudonné module $M(G)$ over $A_{\mathrm{cris}}$
(`integralModule`) of a $p$-divisible group $G$ over a ring $R$ of characteristic $p$, for a prime
$p$ and the given crystalline and Cartier data: an isomorphism $c$ from the Frobenius pullback
$\varphi^* M(G)$ (scalar extension along the completed Frobenius $\varphi$) to the module
$M(G^{(p)})$ of the Frobenius twist of $G$, such that $F = M(V_G) \circ c$ from $\varphi^* M(G)$ to
$M(G)$ and $V = c^{-1} \circ M(F_G)$ from $M(G)$ to $\varphi^* M(G)$, induced by the Verschiebung
$V_G$ and the relative Frobenius $F_G$ of $G$, satisfy $F \circ V = p$ on $M(G)$ and
$V \circ F = p$ on $\varphi^* M(G)$. -/
structure OperatorsRealization where
  baseChange : frobeniusPullback p R A E P G D F₀ φ ≅
    integralModule p R A E P Q.source.twist.group Q.dualTwist
  vf : verschiebung p R A E P G D Q F₀ φ baseChange ≫
    frobenius p R A E P G D Q F₀ φ baseChange =
      p • 𝟙 (integralModule p R A E P G D)
  fv : frobenius p R A E P G D Q F₀ φ baseChange ≫
    verschiebung p R A E P G D Q F₀ φ baseChange =
      p • 𝟙 (frobeniusPullback p R A E P G D F₀ φ)

end MathlibExt.AlgebraicGeometry.SemiperfectDieudonneOperators
