/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels

/-!
# Source-normalized bounded determinant and global Deligne construction requests

The scalar target is the actual native degreewise extension; exterior
maps, dual evaluation, ordered tensor maps and zero-factor units are fixed.
Global line comparisons retain the actual derived pullback transitions.
The Deligne line retains every subset of the source tensor expression.

Source: Knudsen--Mumford, Sections 1--2; Yuan--Zhang,
arXiv:2105.13587v9, Section 4.2.1 and Theorem 4.1.3.
These are construction/integration requests, not asserted completed providers.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GlobalBoundedDeterminants

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants
open MathlibExt.AlgebraicGeometry.BoundedScalarDeterminants
open MathlibExt.AlgebraicGeometry.BoundedDeterminantTransportModels
open MathlibExt.AlgebraicGeometry.DeterminantScalarTensorModels
open MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels
open MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings

/-- The actual bounded source target includes the full scalar complex
and exact zero-support trim. -/
public def_wanted scalarPresentation {R S : CommRingCat.{0}} (g : R ⟶ S)
    (C : MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants.Complex R) :
    ScalarPresentation g C

/-- Normalize the completed projective exterior and dual scalar sources in every degree. -/
public def_wanted scalarTermSources {R S : CommRingCat.{0}} (g : R ⟶ S)
    (C : MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants.Complex R)
    (D : ScalarPresentation g C) : TermSources g C D

/-- The full scalar determinant comparison has the exact native adjunction-unit equation. -/
public def_wanted scalarComparison {R S : CommRingCat.{0}} (g : R ⟶ S)
    (C : MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants.Complex R)
    (D : ScalarPresentation g C) (T : TermSources g C D) : ScalarComparison g C D T

/-- Normalize native scalar tensor, unit and finite-projective dual comparisons. -/
public def_wanted scalarTensorSources {R S : CommRingCat.{0}} (g : R ⟶ S) :
    ScalarTensorSources g

/-- Transport determinant modules on actual arbitrary-amplitude derived isomorphisms. -/
public def_wanted boundedTransport (R : Type) [CommRing R] : TransportSystem R

/-- Existence of the left derived functor of actual termwise scalar extension: unbounded
complexes of modules have K-projective resolutions. This provides the
`HasDerivedScalarExtensions` hypothesis of the global requests below. -/
public instance_wanted derivedScalarExtensions_exists :
    MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}

/-- The exterior-annihilator determinant of a finite projective module is invertible: on each
rank stratum it is the top exterior power. This provides the `ProjectiveSources` hypothesis of
the global requests below. -/
public instance_wanted projectiveSources_exists (R : CommRingCat.{0}) : ProjectiveSources R

variable [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPullbacks.{0}]
  [MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, CategoryTheory.Limits.PreservesFiniteLimits
    (_root_.AlgebraicGeometry.tilde.functor R)]

/-- Derived pullbacks are pseudofunctorial: their identity and composition comparisons,
normalized by the native cochain counits, satisfy the associativity and unit laws. This
provides the `Coherence` input of the determinant transitions. -/
public def_wanted derivedPullbackCoherence :
    MathlibExt.AlgebraicGeometry.DeterminantPullbackCoherence.Coherence.{0}

/-- Derived pullback along `Spec g` of the affine coefficient functor is derived scalar
extension, normalized by the native cochain comparison. This provides the
`DerivedComparison` input of the determinant transitions. -/
public def_wanted derivedTildeComparison {R S : CommRingCat.{0}} (g : R ⟶ S) :
    MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules.DerivedComparison g

/-- Construct the source-normalized determinant data and its global
line on this exact derived object. -/
public def_wanted globalDeterminant {X : Scheme.{0}}
    (K : MathlibExt.AlgebraicGeometry.FourierMukai.D X) (P : AffineFamily K) :
    Σ I : DeterminantSources, DeterminantLine I K P

variable [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, ProjectiveSources R]

/-- Construct the actual global algebraic Deligne line of the complete subset expression. -/
public def_wanted globalDeligne {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (L : Fin (n+1) → X.Modules)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a) :
    Σ I : DeterminantSources, DeligneLine I f n L P

end WantedExt.AlgebraicGeometry.GlobalBoundedDeterminants
