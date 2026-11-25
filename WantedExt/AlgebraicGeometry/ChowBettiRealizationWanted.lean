/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BettiMotiveRealization

/-!
# Concrete Chow-to-Betti correspondence and tensor comparison

The correspondence groups are the actual geometric-family rational quotient.
Their Betti operator is the constructed pull/cup/Gysin formula. The requested
composition agrees with literal middle fibre products of actual transverse
proper presentations, and realizes identities and composition on that same
operator. Conditional rational functors and actual projector ranges are
already constructed in MathlibExt; generic Karoubi work is not re-requested.

The tensor comparison is bijectivity of the displayed actual Künneth map.
This packet is for effective pure complex Betti motives; it does not furnish
an unspecified Frobenius, Galois or mixed-motive model.

Existing generic realization and motive calculus:
https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/RealizationFunctor.lean
Reference: Fulton, *Intersection Theory*, §16.1 and §19.1; Stacks Tag 0FHL.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ChowBettiRealizationWanted

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open BettiMotiveRealization

/-- The fibre product of two smooth projective complex varieties is a smooth projective
complex variety whose relative dimension is the sum of theirs. -/
public instance_wanted productGeometry (X Y : SmoothObject) : ProductGeometry X Y

/-- Construct the composition and compatibility bridge for this actual Chow
presentation and the fixed Betti action, including geometric normalization. -/
public def_wanted correspondenceCalculus
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
    (S : BettiCycleRealization.CycleRealization D P) :
    CorrespondenceCalculus D P S

/-- The actual finite tensor/cup/pullback map realizes the Künneth isomorphism
on pure-dimensional smooth projective complex schemes. -/
public theorem_wanted kunneth_bijective (X Y : SmoothObject) (n : ℤ) :
    Function.Bijective (kunnethMap X Y n)

end WantedExt.AlgebraicGeometry.ChowBettiRealizationWanted
