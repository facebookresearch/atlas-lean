/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StableEnvelopeBorelModels

/-!
# The cohomological stable-envelope map, normalized relative to an orientation

The map has the actual native Borel cohomology of the full fixed
scheme as its source. Component insertion in that cohomology is the
inverse of the computed native component-restriction map. Support
uses the actual closure-generated full attracting locus. The signed
Euler and partial-degree operators are the previously computed ones.
The Euler classes are relative to the orientation datum of the
geometry's coefficient system: when it is the complex orientation, this
is Maulik--Okounkov's normalization; for another datum each component's
signed Euler class is a locally constant unit multiple of the usual one,
and the map is Maulik--Okounkov's precomposed with multiplication by
those units on the source components.

The strict A-degree clause tests only quotient-torus classes gamma.
Linearity over all actual H_T(pt) coefficients supplies the extension.
Reference: Maulik--Okounkov 1211.1287v3, Theorem3.3.4 and Section3.3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.StableEnvelopeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusDifferentialGeometryModels
open TorusPolynomialDegreeModels IntegralChowChernModels SymplecticTorusSourceModels
open TorusFixedSchemeModels TorusAttractingSchemeModels TorusAttractingOrderModels
open ComplexAnalytification TorusBorelCoefficientModels ResidualTorusDegreeModels
open StableEnvelopeNormalModels StableEnvelopeBorelModels

variable [ThetaQuotientSources.ContractingAction ℂ]
  {A T : Over base} [GrpObj A] [GrpObj T]
  (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T) (P : TorusSplitting S)
  (X : SchemeData) [ModObj A X.scheme] [ModObj T X.scheme]
  (Source : StableEnvelopeSource MA MT S X)
  (F : FixedSchemeModel A X.scheme) (Z : FixedComponents A X.scheme F)
  (N : NormalFamily MA X.scheme F Z) (C : Chamber N.roots) (L : ChamberCocharacter C)
  (Ch : ∀ j : Fin Z.count, ComponentChamber C L (N.componentRoots j))

/-- Geometry and operators retain the chosen chamber, polarization and original source
hypotheses. -/
structure StableEnvelopeGeometry where
  tangent : TorusTangentActionData MT X.scheme
  source_forms : tangent.forms = Source.forms
  attracting : AttractingScheme A X.scheme L.map F
  coefficients : CoefficientCoordinates MT
  component : ∀ j : Fin Z.count,
    ComponentBorelData MA MT S P X.scheme tangent Source.analytic (Z.component j).data
      ((Z.component j).toAmbient A X.scheme) (StableEnvelopeNormalModels.componentFixed (Z.component
        j))
      (N.normal j) (N.componentRoots j) (Ch j).chamber (Ch j).cocharacter coefficients
  [fixedAction : ModObj T F.scheme]
  fixedAnalytic : AnalyticTorusAction MT F.scheme
  fixedEquivariant : γ[T,F.scheme] ≫ F.inclusion = (T ◁ F.inclusion) ≫ γ[T,X.scheme]
  componentEquivariant : ∀ j : Fin Z.count,
    letI := (component j).action
    γ[T,(Z.component j).data.scheme] ≫ (Z.component j).inclusion =
      (T ◁ (Z.component j).inclusion) ≫ γ[T,F.scheme]
  componentTopology : ∀ j : Fin Z.count,
    letI := fixedAnalytic.action
    letI := fixedAnalytic.continuous
    letI := (component j).action
    letI := (component j).analytic.action
    letI := (component j).analytic.continuous
    ∀ (g : Fin MT.rank → ℂˣ) (z : space (Z.component j).data.scheme),
      spaceMap (Z.component j).inclusion (g • z) = g • spaceMap (Z.component j).inclusion z
  supportInvariant : ∀ j : Fin Z.count,
    letI := Source.analytic.action
    letI := Source.analytic.continuous
    ∀ (g : Fin MT.rank → ℂˣ) (x : space X.scheme),
      (g • x).schemePoint ∈ fullAttracting A X.scheme L.map attracting Z j ↔
        x.schemePoint ∈ fullAttracting A X.scheme L.map attracting Z j

variable (G : StableEnvelopeGeometry MA MT S P X Source F Z N C L Ch)

abbrev AmbientH := H MT X.scheme Source.analytic

abbrev FixedH :=
  letI := G.fixedAction
  H MT F.scheme G.fixedAnalytic

abbrev ComponentH (j : Fin Z.count) :=
  letI := (G.component j).action
  H MT (Z.component j).data.scheme (G.component j).analytic

/-- All component restrictions are the actual Borel maps of the original closed embeddings. -/
def componentRestrictions : FixedH MA MT S P X Source F Z N C L Ch G →ₗ[ℂ]
    ((j : Fin Z.count) → ComponentH MA MT S P X Source F Z N C L Ch G j) := by
  letI := G.fixedAction
  letI := G.fixedAnalytic.action
  letI := G.fixedAnalytic.continuous
  apply LinearMap.pi
  intro j
  letI := (G.component j).action
  letI := (G.component j).analytic.action
  letI := (G.component j).analytic.continuous
  exact BorelCohomologyModels.gradedRestriction (spaceMap (Z.component j).inclusion)
    (G.componentTopology j)

/-- Bijectivity is a theorem about this computed restriction map. -/
structure StableEnvelopeData where
  geometry : StableEnvelopeGeometry MA MT S P X Source F Z N C L Ch
  components : Function.Bijective
    (componentRestrictions MA MT S P X Source F Z N C L Ch geometry)

variable (D : StableEnvelopeData MA MT S P X Source F Z N C L Ch)

/-- Insert a component class by the inverse of the native fixed-scheme restriction. -/
def componentInsertion (j : Fin Z.count)
    (gamma : ComponentH MA MT S P X Source F Z N C L Ch D.geometry j) :
    FixedH MA MT S P X Source F Z N C L Ch D.geometry :=
  (LinearEquiv.ofBijective (componentRestrictions MA MT S P X Source F Z N C L Ch D.geometry)
    D.components).symm (Pi.single j gamma)

def restrictToComponent (j : Fin Z.count) : AmbientH MA MT S X Source →ₗ[ℂ]
    ComponentH MA MT S P X Source F Z N C L Ch D.geometry j :=
  ambientRestriction MA MT S P X.scheme D.geometry.tangent Source.analytic (Z.component j).data
    ((Z.component j).toAmbient A X.scheme) (StableEnvelopeNormalModels.componentFixed (Z.component
      j))
    (N.normal j) (N.componentRoots j) (Ch j).chamber (Ch j).cocharacter D.geometry.coefficients
    (D.geometry.component j)

/-- Cup with the signed Euler class of the negative normal bundle, relative to the coefficient
system's orientation datum. -/
def normalizedEuler (j : Fin Z.count) : Module.End ℂ
    (ComponentH MA MT S P X Source F Z N C L Ch D.geometry j) :=
  signedEulerCup MA MT S P X.scheme D.geometry.tangent Source.analytic (Z.component j).data
    ((Z.component j).toAmbient A X.scheme) (StableEnvelopeNormalModels.componentFixed (Z.component
      j))
    (N.normal j) (N.componentRoots j) (Ch j).chamber (Ch j).cocharacter D.geometry.coefficients
    (D.geometry.component j) (Ch j).polarization

/-- This support is the analytic inverse image of the actual full attracting subset. -/
def fullSupport (j : Fin Z.count) :
    letI := Source.analytic.action
    letI := Source.analytic.continuous
    BorelCohomologyModels.InvariantSubset (Fin MT.rank → ℂˣ) (space X.scheme) := by
  letI := Source.analytic.action
  letI := Source.analytic.continuous
  exact {
    carrier := {x | x.schemePoint ∈
      fullAttracting A X.scheme L.map D.geometry.attracting Z j}
    invariant := D.geometry.supportInvariant j }

/-- The native cohomology-map conditions have the exact quotient-class degree quantifier. -/
def IsStableEnvelope (stab : FixedH MA MT S P X Source F Z N C L Ch D.geometry →ₗ[ℂ]
    AmbientH MA MT S X Source) : Prop :=
  (letI := Source.analytic.action
   letI := Source.analytic.continuous
   letI := D.geometry.fixedAction
   letI := D.geometry.fixedAnalytic.action
   letI := D.geometry.fixedAnalytic.continuous
   BorelCohomologyModels.CoefficientLinear stab) ∧
  ∀ j : Fin Z.count,
    letI := (D.geometry.component j).action
    ∀ gamma : QuotientH (D.geometry.component j).residual,
    let ordinary := quotientClasses (D.geometry.component j).residual gamma
    let envelope := stab (componentInsertion MA MT S P X Source F Z N C L Ch D j ordinary)
    (letI := Source.analytic.action
     letI := Source.analytic.continuous
     BorelCohomologyModels.Supported (fullSupport MA MT S P X Source F Z N C L Ch D j) envelope) ∧
    restrictToComponent MA MT S P X Source F Z N C L Ch D j envelope =
      normalizedEuler MA MT S P X Source F Z N C L Ch D j ordinary ∧
    ∀ lower : Fin Z.count,
      letI := (D.geometry.component lower).action
      precedes A X.scheme L.map D.geometry.attracting Z lower j → lower ≠ j →
      ResidualTorusDegreeModels.strictHalfDegree (D.geometry.component lower).residual
        D.geometry.coefficients (D.geometry.component lower).polynomial
        (normalRank (N.componentRoots lower))
        (restrictToComponent MA MT S P X Source F Z N C L Ch D lower envelope)

end MathlibExt.AlgebraicGeometry.StableEnvelopeModels
