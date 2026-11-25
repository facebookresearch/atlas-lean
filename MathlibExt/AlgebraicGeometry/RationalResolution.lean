/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import MathlibExt.AlgebraicGeometry.BirationalResolution
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

/-!
# Rational resolutions and canonical direct images

The structure-sheaf map is the actual module pullback/pushforward unit,
followed by the canonical pullback of the structure module. Higher direct
images are Mathlib's right-derived module-sheaf pushforward.

Rationality is expressed by this particular map being an isomorphism and
the actual higher direct images being zero. Normality and Cohen–Macaulayness
are tested on actual scheme stalk rings.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RationalResolution

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BirationalResolution
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

universe u

/-- Canonical structure-sheaf unit for an actual scheme morphism. -/
def structureUnit {Y X : Scheme.{u}} (f : Y ⟶ X) :
    structureModule X ⟶ (Scheme.Modules.pushforward f).obj (structureModule Y) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureModule X) ≫
    (Scheme.Modules.pushforward f).map (pullbackStructureIso f).hom

/-- The actual higher module-sheaf direct image. -/
abbrev higherDirectImage {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : Y.Modules) (i : ℕ) : X.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived i).obj M

def IsNormalIntegral (X : Scheme.{u}) [IsIntegral X] : Prop :=
  ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/-- Stalkwise Cohen–Macaulayness of a locally Noetherian scheme via actual local
Ext-depth: every stalk, a Noetherian local ring, has depth equal to its dimension. -/
def IsCohenMacaulayStalkwise (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ x : X,
    (IsLocalRing.depth
      (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk x)

/-- Rationality of the specified normalized resolution. -/
def IsRationalResolution {k : Type u} [Field k]
    {X : Over (Spec (.of k))} (R : ResolutionModel X) : Prop :=
  IsIso (structureUnit R.morphism.left) ∧
    ∀ i : ℕ, 0 < i →
      IsZero (higherDirectImage R.morphism.left (structureModule R.source.left) i)

end MathlibExt.AlgebraicGeometry.RationalResolution
