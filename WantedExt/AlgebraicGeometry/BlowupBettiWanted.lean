/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BlowupBettiModels

/-!
# Betti splitting for a smooth-center blowup

The displayed map is pullback from the original variety plus the actual
exceptional Gysin contributions. The exceptional class is minus the
exceptional self-intersection class, computed from the same purity data; for
complex orientations it is the hyperplane class of the exceptional divisor,
and other purity choices rescale the summands by units, which does not affect
bijectivity. The result is an additive Betti splitting; no independently
normalized ring or cycle realization is assumed.

The global blowup construction, full universal property and exceptional
normal-cone description in Axiom's Stacks project are completed support.
The verified algebraic excess/Gysin formulas are also covered inputs.
This request concerns these fixed rational Betti carriers.

Reference: Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
Section 7.3, cohomology of a blowup; Fulton, *Intersection Theory*,
Section 6.7 and Section 19.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BlowupBettiWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves CompactSupportBetti
open ProperBettiFunctoriality BettiGysin BlowupBettiModels

theorem_wanted blowupComparison_bijective
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
    {X Z : ComplexScheme} (i : Z ⟶ X) [IsClosedImmersion i.left]
    [IsIntegral X.left] [IsProper X.hom] [IsProper Z.hom]
    (B : BlowupModel i) (d c : ℕ) (hc : 2 ≤ c)
    [IsComplexVariety X] [IsComplexVariety Z] [IsComplexVariety B.source]
    [IsComplexVariety B.exceptional]
    [SmoothOfRelativeDimension (d + c) X.hom]
    [SmoothOfRelativeDimension d Z.hom]
    [SmoothOfRelativeDimension (d + c) B.source.hom]
    [SmoothOfRelativeDimension (d + c - 1) B.exceptional.hom]
    (F : PureFamily D) (n : ℤ) :
    Function.Bijective (blowupComparison D P i B d c hc F n)

end WantedExt.AlgebraicGeometry.BlowupBettiWanted
