/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BettiCycleRealization

/-!
# The actual geometric Betti cycle realization

Construct rational cycle classes on projective complex varieties from the
actual quotient by flat-family relations into actual dualizing-derived
Borel–Moore groups. The requested
provider chooses a compatible purity family, normalizes every smooth
projective proper presentation by the fixed compact-support duality map,
and realizes transverse smooth closed intersections as the actual cup.

The dualizing complexes and normalized compact-support pullback are explicit
ordinary sheaf-theory toolbox inputs. This request neither reconstructs a
generic Chow ring nor assumes an abstract Weil-cohomology cycle map. No
canonical complex-orientation choice is asserted without constructing it.

Reference: W. Fulton, *Intersection Theory*, §19.1;
https://doi.org/10.1007/978-1-4612-1700-8
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BettiCycleRealizationWanted

open _root_.AlgebraicGeometry CategoryTheory
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.AlgebraicGeometry.BettiCycleRealization

/-- Construct the normalized ordinary Betti cycle realization on the actual
Chow and compact-support dualizing carriers. -/
public def_wanted bettiCycleRealization
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X],
      DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f)) :
    CycleRealization D P

end WantedExt.AlgebraicGeometry.BettiCycleRealizationWanted
