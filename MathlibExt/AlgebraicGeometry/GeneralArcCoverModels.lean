/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# General qcqs arc covers and normalized valuation excision rings

Schemes are arbitrary qcqs schemes. The cover test uses every actual
rank-at-most-one valuation ring and faithfully flat valuation extension.
No field, finite-type or Noetherian target restriction is imposed.

The excision coefficient rings are the actual V/p, V_p and Frac(V/p).
The two residue descriptions and every ring map are normalized on the
canonical quotient/localization maps.

Reference: Bhatt--Mathew, arXiv:1807.04725v4, Definitions 1.1--1.2,
Theorem 1.7 and its valuation excision square.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralArcCoverModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open TopologicalSpace

structure QcqsScheme where
  scheme : Scheme.{0}
  [compact : CompactSpace scheme]
  [quasiSeparated : QuasiSeparatedSpace scheme]

attribute [instance] QcqsScheme.compact QcqsScheme.quasiSeparated

instance : Category.{0} QcqsScheme where
  Hom X Y := X.scheme ⟶ Y.scheme
  id X := 𝟙 X.scheme
  comp f g := f ≫ g

def forgetScheme : QcqsScheme ⥤ Scheme.{0} where
  obj X := X.scheme
  map f := f

def affine (R : CommRingCat.{0}) : QcqsScheme where
  scheme := Spec R
  compact := inferInstance
  quasiSeparated := inferInstance

/-- Rank at most one includes the field case; it uses the actual prime-ideal condition. -/
def RankAtMostOne (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] : Prop :=
  ∀ p : Ideal R, p.IsPrime → p = ⊥ ∨ p.IsMaximal

structure ValuationRingData where
  ring : Type
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [valuation : ValuationRing ring]

attribute [instance] ValuationRingData.commRing ValuationRingData.domain ValuationRingData.valuation

structure RankOneValuationRing extends ValuationRingData where
  rank : RankAtMostOne ring

/-- Extension means the paper's actual faithfully flat ring map. -/
structure ValuationExtension (V : RankOneValuationRing) where
  target : RankOneValuationRing
  map : V.ring →+* target.ring
  faithfullyFlat : map.FaithfullyFlat

structure ArcLift {X Y : QcqsScheme} (f : Y ⟶ X) (V : RankOneValuationRing)
    (x : Spec (.of V.ring) ⟶ X.scheme) where
  extension : ValuationExtension V
  lift : Spec (.of extension.target.ring) ⟶ Y.scheme
  comm : lift ≫ f = Spec.map (CommRingCat.ofHom extension.map) ≫ x

/-- The literal valuation lifting test on general qcqs schemes. -/
def IsArcCover {X Y : QcqsScheme} (f : Y ⟶ X) : Prop :=
  ∀ (V : RankOneValuationRing) (x : Spec (.of V.ring) ⟶ X.scheme), Nonempty (ArcLift f V x)

structure ValuationExcision (V : ValuationRingData) (p : PrimeSpectrum V.ring) where
  localToKappa : Localization.AtPrime p.asIdeal →+* FractionRing (V.ring ⧸ p.asIdeal)
  comm : localToKappa.comp (algebraMap V.ring (Localization.AtPrime p.asIdeal)) =
    (algebraMap (V.ring ⧸ p.asIdeal) (FractionRing (V.ring ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal)
  residueIso : IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal) ≃+*
    FractionRing (V.ring ⧸ p.asIdeal)
  residue_eq : localToKappa = residueIso.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime p.asIdeal))

end MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
