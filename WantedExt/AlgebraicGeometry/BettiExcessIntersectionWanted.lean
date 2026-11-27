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

The request constructs one purity family, chosen once for all smooth
varieties, realizing the excess formula on every such square; it does not
assume the desired equation as a theorem hypothesis. This is an
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

/-- **A purity family satisfying the excess intersection formula.** Given a dualizing complex `D X`
on the analytic space of every complex variety $X$ and a compactly supported pullback `P f` along
the analytification of every proper morphism $f$ of complex varieties, there is a single purity
family (`PureFamily D`: isomorphisms $D_X ≅ \mathbb Q[2d]$ for the smooth complex varieties $X$ of
pure dimension $d$) for which the excess intersection formula $g^* i_! a = j_!(e(E) ∪ g'^* a)$ holds
on every smooth affine excess square (`SmoothExcessSquare`), the Gysin maps and the Euler class of
the excess normal bundle $E$ being those of this family (Fulton, Theorem 6.3). -/
public def_wanted compatible_excess
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f)) :
    ExcessPurities D P

end WantedExt.AlgebraicGeometry.BettiExcessIntersectionWanted
