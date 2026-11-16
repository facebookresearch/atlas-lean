/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Batteries.Util.ProofWanted

/-!
# Bounded presentations of actual relative determinant factors

These native construction requests use the specified derived direct
image and affine pullback. Proper flat finite-presentation morphisms
and actual line bundles give the classical perfect direct images;
the requested data integrate their bounded projective presentations
with these native operators.

The second request is only the affine independence consequence of
the determinant construction. Global transport, coherent base change,
adelic completion and metrized Deligne comparisons are distinct
constructions; no arbitrary affine isomorphism supplies them.

References: Knudsen--Mumford, *The projectivity of the moduli space of
stable curves I*, Sections 1--2; Stacks Project, Tags 0FJW and 0FJX.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries AffineDerivedCoefficientModules

attribute [local instance] HasDerivedCategory.standard

def_wanted relativeAffinePresentations
    [FourierMukai.HasDerivedPullbacks.{0}]
    [FourierMukai.HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (m : ℕ) (L : Fin m → X.Modules) (hL : ∀ i, IsLineBundle (L i)) :
    ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a

theorem_wanted localPairingPresentationIndependence
    [FourierMukai.HasDerivedPullbacks.{0}]
    [FourierMukai.HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (m : ℕ) (L : Fin m → X.Modules)
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y)
    (P Q : Presentations f L R a) : Nonempty (localPairing P ≅ localPairing Q)

end MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings
