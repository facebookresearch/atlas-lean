/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StableEnvelopeModels
public import MathlibExt.AlgebraicGeometry.TorusSupportedCorrespondenceModels

/-!
# The cohomological stable-envelope theorem, relative to an orientation datum

All requests retain the source smooth symplectic quasiprojective
geometry, proper map to an affine variety and native equivariant
formality edge. Chambers and square-root polarizations remain chosen
parameters. The geometry provider chooses the coefficient system and its
one orientation datum, which orients every Euler class; existence is not
requested for an arbitrary table of orientations. The theorem requests
existence and uniqueness of the actual cohomology map with native
support, signed negative Euler class relative to that datum, and the
strict quotient-class A-degree condition. When the datum is the complex
orientation this is Maulik--Okounkov's stable envelope. For another datum
the Euler classes are locally constant unit multiples of the usual ones
and the degree filtration is unchanged, so the requested map is
Maulik--Okounkov's precomposed with multiplication by those units on the
source components.
Reference: Maulik--Okounkov 1211.1287v3, Sections3.1--3.3 and Theorem3.3.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.StableEnvelopeSources

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonObj
open MathlibExt.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusDifferentialGeometryModels
open TorusPolynomialDegreeModels IntegralChowChernModels SymplecticTorusSourceModels
open TorusFixedSchemeModels TorusAttractingOrderModels TorusBorelCoefficientModels
open StableEnvelopeNormalModels StableEnvelopeModels

variable [ThetaQuotientSources.ContractingAction ℂ]
  (A T : Over base) [GrpObj A] [GrpObj T]
  (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T) (P : TorusSplitting S)
  (X : SchemeData) [ModObj A X.scheme] [ModObj T X.scheme]
  (Source : StableEnvelopeSource MA MT S X)

def_wanted actual_torus_fixed_scheme (_source : StableEnvelopeSource MA MT S X) :
    FixedSchemeModel A X.scheme

def_wanted actual_torus_fixed_components (F : FixedSchemeModel A X.scheme) :
    FixedComponents A X.scheme F

def_wanted actual_normal_character_family (F : FixedSchemeModel A X.scheme)
    (Z : FixedComponents A X.scheme F) (_source : StableEnvelopeSource MA MT S X) :
    NormalFamily MA X.scheme F Z

def_wanted actual_chamber_cocharacter {Roots : RootCoordinates MA} (C : Chamber Roots) :
    ChamberCocharacter C

variable (F : FixedSchemeModel A X.scheme) (Z : FixedComponents A X.scheme F)
  (N : NormalFamily MA X.scheme F Z) (C : Chamber N.roots) (L : ChamberCocharacter C)

def_wanted actual_component_chamber (_source : StableEnvelopeSource MA MT S X)
    (j : Fin Z.count) (epsilon : CharacterPolynomials MA.rank)
    (_square : epsilon^2 = (-1)^(normalRank (N.componentRoots j)/2) *
      normalEuler (N.componentRoots j)) :
    {Ch : ComponentChamber C L (N.componentRoots j) // Ch.polarization.epsilon = epsilon}

variable (Ch : ∀ j : Fin Z.count, ComponentChamber C L (N.componentRoots j))

def_wanted actual_stable_envelope_geometry :
    StableEnvelopeGeometry MA MT S P X Source F Z N C L Ch

theorem_wanted actual_fixed_borel_decomposition
    (G : StableEnvelopeGeometry MA MT S P X Source F Z N C L Ch) :
    Function.Bijective (componentRestrictions MA MT S P X Source F Z N C L Ch G)

theorem_wanted actual_attraction_order_antisymmetric
    (G : StableEnvelopeGeometry MA MT S P X Source F Z N C L Ch) (j k : Fin Z.count)
    (_forward : precedes A X.scheme L.map G.attracting Z j k)
    (_backward : precedes A X.scheme L.map G.attracting Z k j) : j=k

theorem_wanted actual_full_attracting_closed
    (G : StableEnvelopeGeometry MA MT S P X Source F Z N C L Ch) (j : Fin Z.count) :
    IsClosed (fullAttracting A X.scheme L.map G.attracting Z j)

/-- The strict degree condition is only on gamma in actual quotient-torus cohomology. -/
theorem_wanted stable_envelope_exists_unique
    (D : StableEnvelopeData MA MT S P X Source F Z N C L Ch) :
    ∃! stab : FixedH MA MT S P X Source F Z N C L Ch D.geometry →ₗ[ℂ]
      AmbientH MA MT S X Source,
      IsStableEnvelope MA MT S P X Source F Z N C L Ch D stab

end WantedExt.AlgebraicGeometry.StableEnvelopeSources
