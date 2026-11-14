/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses

/-!
# Betti characteristic classes and projective-bundle calculus

The request constructs a compatible smooth purity family for the exact
Betti operators in MathlibExt. Projective bundles are pinned by the actual
invertible-quotient universal property; the tautological line's total space
represents its actual sections. Hyperplane, projective-bundle maps, Chern
coefficients and Segre recurrences are completed conditional constructors.

The remaining theory proves bijectivity and the exact normalized pushforward,
pullback, Whitney and projection identities. Generic algebraic Chern/Segre
and projective-bundle formulas already exist in the following source and
are not requested as absent general foundations:
https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Chow/ProjectiveBundleFormula/Formula.lean
Reference: Fulton, *Intersection Theory*, Chapters 3 and 6, §19.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BettiCharacteristicClassesWanted

open CategoryTheory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open BettiCharacteristicClasses

/-- Construct the compatible positive-rank Betti characteristic theory on
the fixed sheaf, quotient-bundle and cohomological maps, including its laws. -/
public def_wanted characteristicTheory
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f)) :
    CharacteristicClassTheory D P

end WantedExt.AlgebraicGeometry.BettiCharacteristicClassesWanted
