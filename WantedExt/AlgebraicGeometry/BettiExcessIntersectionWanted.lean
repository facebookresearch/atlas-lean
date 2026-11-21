/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffineExcessBetti

/-!
# Betti realization of the excess formula for an actual affine clean square

All four schemes, both quotient maps and their Cartesian relation are fixed
by the ring map and ideal. The excess conormal is the kernel of the actual
cotangent base-change map, and its dual normal space and zero section are
constructed. Euler and Gysin operators use the actual compact-support
duality and the same selected purity family.

The request constructs a compatible family realizing the excess formula;
it does not assume the desired equation as a theorem hypothesis. This is an
affine Betti bridge, and does not claim a full general lci bivariant theory.
The generic algebraic formula already exists in AxiomMath/Stacks:
https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Chow/GysinLocalCompleteIntersection/BaseChangeExcessFormula.lean
Mathematical reference: Fulton, *Intersection Theory*, Theorem 6.3, §19.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BettiExcessIntersectionWanted

open CategoryTheory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open AffineExcessBetti

/-- Construct compatible smooth purities and the displayed Betti excess
formula, with rank and dimensions supplied by the actual smooth normal space. -/
public def_wanted compatible_excess (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B] (I : Ideal A)
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
    (dx dx' c' e : ℕ) [SmoothExcessSquare A B I dx dx' c' e] :
    ExcessPurities A B I D P dx dx' c' e

end WantedExt.AlgebraicGeometry.BettiExcessIntersectionWanted
