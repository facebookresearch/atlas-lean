/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleLogNativeCategory
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Actual coefficients of small Kato charts

The chart monoid is small, with only a universe lift in the etale sheaf.
Its original generators pass through the actual constant-sheaf unit,
chart map and log alpha. Regular-function descent inverts the specified
native sheafification unit. The resulting Z[P] ring map and scheme map
are computed by native monoid algebra and Gamma--Spec adjunction maps.

Source: Kato Section1; Talpo--Vistoli arXiv:1410.1164v2, the chart
diagram preceding Definition6.10.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open EtaleLogSchemes LogStructures SmallEtaleGeometry

abbrev identityEtale (X : Scheme.{0}) : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- The actual native regular-function sheafification unit. -/
def regularUnit (X : Scheme.{0}) (U : X.Etale) :
    (rawRing X).obj (op U) ⟶ (structureRing X).obj.obj (op U) :=
  ((sheafificationAdjunction X.smallEtaleTopology CommRingCat.{1}).unit.app
    (rawRing X)).app (op U)

/-- Ordinary etale regular-function descent, on the fixed unit map. -/
structure RegularSectionComparisons : Prop where
  isIso : ∀ (X : Scheme.{0}) (U : X.Etale), IsIso (regularUnit X U)

variable (D : RegularSectionComparisons)

def regularIso (X : Scheme.{0}) (U : X.Etale) :
    (rawRing X).obj (op U) ≅ (structureRing X).obj.obj (op U) := by
  letI := D.isIso X U
  exact asIso (regularUnit X U)

abbrev liftedMonoid (P : CommMonCat.{0}) : CommMonCat.{1} := .of (ULift.{1} P)

/-- A small original monoid chart on the actual identity-etale object. -/
structure SmallChart (X : LogScheme.{0}) where
  monoid : CommMonCat.{0}
  fine : IsFineMonoid (liftedMonoid monoid)
  chart : LogStructures.Chart X.scheme.smallEtaleTopology X.log
    (identityEtale X.scheme) (liftedMonoid monoid)

variable {X : LogScheme.{0}} (C : SmallChart X)

/-- Constant-sheaf generators mapped into the original log sheaf. -/
def logGenerator : liftedMonoid C.monoid ⟶
    (monoid X.scheme.smallEtaleTopology X.log).obj.obj (op (identityEtale X.scheme)) :=
  let U := identityEtale X.scheme
  ((sheafificationAdjunction (X.scheme.smallEtaleTopology.over U) CommMonCat.{1}).unit.app
    ((Functor.const (Over U)ᵒᵖ).obj (liftedMonoid C.monoid))).app (op (Over.mk (𝟙 U))) ≫
      C.chart.map.hom.app (op (Over.mk (𝟙 U)))

/-- Alpha of those exact log generators, followed by the native unit inverse. -/
def coefficient (p : C.monoid) : Γ(X.scheme, ⊤) :=
  ((ULift.ringEquiv : ULift.{1} Γ(X.scheme, ⊤) ≃+* Γ(X.scheme, ⊤)))
    ((regularIso D X.scheme (identityEtale X.scheme)).inv.hom
      ((alpha X.scheme.smallEtaleTopology X.log).hom.app (op (identityEtale X.scheme))
        (logGenerator C (ULift.up p))))

def coefficientMap : C.monoid →* Γ(X.scheme, ⊤) where
  toFun := coefficient D C
  map_one' := by
    change ULift.ringEquiv
      ((regularIso D X.scheme (identityEtale X.scheme)).inv.hom
        (((alpha X.scheme.smallEtaleTopology X.log).hom.app
          (op (identityEtale X.scheme))).hom ((logGenerator C).hom 1))) = 1
    rw [map_one, map_one, map_one, map_one]
  map_mul' p q := by
    change ULift.ringEquiv
      ((regularIso D X.scheme (identityEtale X.scheme)).inv.hom
        (((alpha X.scheme.smallEtaleTopology X.log).hom.app
          (op (identityEtale X.scheme))).hom
          ((logGenerator C).hom (ULift.up p * ULift.up q)))) = _
    rw [map_mul, map_mul, map_mul, map_mul]
    rfl

/-- The Z[P] map is the native universal monoid-algebra extension. -/
def ringMap : MonoidAlgebra ℤ C.monoid →+* Γ(X.scheme, ⊤) :=
  (MonoidAlgebra.lift ℤ Γ(X.scheme, ⊤) C.monoid (coefficientMap D C)).toRingHom

def monoidScheme (P : CommMonCat.{0}) : Scheme.{0} := Spec (.of (MonoidAlgebra ℤ P))

/-- The chart map on schemes is computed by the native global-functions unit. -/
def schemeMap : X.scheme ⟶ monoidScheme C.monoid :=
  X.scheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ringMap D C))

/-- Each original monoid-algebra generator has the computed alpha coefficient. -/
theorem ringMap_generator (p : C.monoid) :
    ringMap D C (MonoidAlgebra.of ℤ C.monoid p) = coefficient D C p :=
  MonoidAlgebra.lift_of (coefficientMap D C) p

end MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels
