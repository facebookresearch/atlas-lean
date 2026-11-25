/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
public import MathlibExt.AlgebraicGeometry.CompactSupportComparison

/-!
# Geometric Verdier duality on the actual complex-point topology

The requests use the rational-linear derived compact-support section functor
and its represented derived-Hom dual. The smooth fundamental class and trace,
once a purity isomorphism is given, are already constructed in MathlibExt.

The residual requests concern existence on this precise analytification model
and smooth purity. The classical compact-support comparison is completed in
`MathlibExt/AlgebraicGeometry/CompactSupportComparison.lean`.
These requests do not claim that generic Poincaré duality, abstract
dualizing objects, or TauCeti's compact-support cap maps are missing. Proper
pushforward is defined from a compact-support pullback normalized by the actual
cochain units; existence of that input for algebraic proper maps is requested
here. Künneth normalization requires additional concrete operators.

Sources: Kashiwara--Schapira, *Sheaves on Manifolds*, §§3.1--3.3; Dimca,
*Sheaves in Topology*, Chapter 3. Existing compact-support cap maps:
https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality.lean
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeometricVerdierDualityWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality

attribute [local instance] HasDerivedCategory.standard

/-- Represent the actual derived compact-support dual on a complex variety. -/
public def_wanted dualizingComplex (X : ComplexScheme) [IsComplexVariety X] :
    DualizingComplex (space X)

/-- A proper algebraic map supplies the support-preserving inverse-image
section map and its enhancement fixed by the actual right-derived units. -/
public def_wanted properPullback (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] (f : X ⟶ Y) [IsProper f.left] :
    ProperPullback (spaceMap f)

/-- Smooth pure-dimensional complex varieties have the indicated dualizing
complex; the real degree is twice the algebraic relative dimension. -/
public theorem_wanted smooth_purity (X : ComplexScheme) [IsComplexVariety X]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (D : DualizingComplex (space X)) :
    Nonempty (D.obj ≅ (rationalUnit (space X))⟦(2 * d : ℤ)⟧)

end WantedExt.AlgebraicGeometry.GeometricVerdierDualityWanted
