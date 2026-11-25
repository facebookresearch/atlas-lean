/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteRamificationStalkModels
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Actual strict local curve traits

The ring is the native global-section ring of the pointed étale limit,
and its generic field is that ring's actual fraction field. The affine
comparison is Mathlib's `Scheme.isoSpec`; the generic map is its composite
with the spectrum of the fraction-field algebra map. No valuation ring,
generic field or geometric generic point is assigned independently.

For a smooth curve at a closed point over a perfect field, the affine,
henselian DVR and algebraically closed residue-field properties are source
construction requests. They contain no ramification or Milnor conclusion.

Reference: Saito, arXiv:1510.03018v4, Sections 1.1 and 1.3, especially
the strict local smooth curve `Y_(y) = Spec O_Ky` on printed page 16.
Native affine and fraction-ring operations are Mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleCurveTraitModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open CotangentBundleTestModels EtaleStrictLocalizationModels

variable {Y : Scheme.{0}} (Ω : GeometricField) (y : Spec (.of Ω.carrier) ⟶ Y)

/-- The section ring of the actual pointed étale limit. -/
abbrev localRing (L : StrictLocalization Ω y) := Γ(L.scheme, ⊤)

/-- A strict trait presentation supplies only properties of that fixed ring. -/
class Trait (L : StrictLocalization Ω y) : Prop where
  [affine : IsAffine L.scheme]
  [domain : IsDomain (localRing Ω y L)]
  [dvr : IsDiscreteValuationRing (localRing Ω y L)]
  [henselian : HenselianLocalRing (localRing Ω y L)]
  [closedResidue : IsAlgClosed (IsLocalRing.ResidueField (localRing Ω y L))]

attribute [instance] Trait.affine Trait.domain Trait.dvr Trait.henselian Trait.closedResidue

variable (L : StrictLocalization Ω y) [Trait Ω y L]

abbrev genericField := FractionRing (localRing Ω y L)

/-- The actual generic point of the native strict local scheme. -/
def genericMap : Spec (.of (genericField Ω y L)) ⟶ L.scheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (localRing Ω y L) (genericField Ω y L))) ≫ L.scheme.isoSpec.inv

/-- Its actual algebraic-closure geometric generization. -/
def geometricGenericMap :
    Spec (.of (AlgebraicClosure (genericField Ω y L))) ⟶ L.scheme :=
  EtaleGaloisStalkActions.closurePoint (genericField Ω y L) ≫ genericMap Ω y L

def genericGenerization {X : Scheme.{0}} (x : Spec (.of Ω.carrier) ⟶ X)
    (f : X ⟶ Y) (LY : StrictLocalization Ω (x ≫ f)) [Trait Ω (x ≫ f) LY] :
    Generization Ω x f LY where
  field := EtaleGaloisStalkActions.closureField (genericField Ω (x ≫ f) LY)
  point := geometricGenericMap Ω (x ≫ f) LY

end MathlibExt.AlgebraicGeometry.EtaleCurveTraitModels
