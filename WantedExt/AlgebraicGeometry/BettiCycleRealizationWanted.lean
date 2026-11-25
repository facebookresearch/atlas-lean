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

/-- **Betti cycle realization of Chow groups of complex varieties.** A cycle realization
(`CycleRealization D P`) for the given dualizing complexes $D$ on the analytic spaces of complex
varieties and the given compact-support pullbacks $P$ along the analytifications of proper
morphisms: purity isomorphisms $D_X \cong \mathbb{Q}[2d]$ for smooth proper projective $X$ of
dimension $d$, and $\mathbb{Q}$-linear cycle class maps from $\mathrm{CH}_r(X)$ to the Borel–Moore
group of degree $2r$ defined by $D_X$, for proper projective $X$, normalized on fundamental cycles
and on pushforwards along proper maps of fundamental cycles of smooth varieties, and compatible with
cup products for smooth closed subschemes of a smooth proper projective variety whose intersection
is smooth of the expected dimension. -/
public def_wanted bettiCycleRealization
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X],
      DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f)) :
    CycleRealization D P

end WantedExt.AlgebraicGeometry.BettiCycleRealizationWanted
