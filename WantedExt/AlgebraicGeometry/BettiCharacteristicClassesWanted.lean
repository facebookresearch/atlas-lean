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

/-- **Betti characteristic class theory.** For a chosen dualizing complex $D_X$ on the space of
complex points of every complex variety $X$, and chosen proper-pullback data $P_f$ for every
proper morphism $f$ of complex varieties: a Betti characteristic class theory
(`CharacteristicClassTheory D P`), namely a purity family for which the projective bundle formula
holds and whose classes satisfy, for every projective bundle $\pi : \mathbb{P}(E) \to X$ of
relative dimension $r$ over a smooth complex variety, with hyperplane class $h$, and every
cohomology class $a$ of $X$: $\pi_*(h^r \cup \pi^* a) = a$, $\pi_*(h^i \cup \pi^* a) = 0$ for
$i < r$ and $\pi_*(h^{r+n}) = s_n$, where $s_n$ (`projectiveSegre`) is the degree-$n$ coefficient
of $1/c(-t)$ for the Chern polynomial $c(t) = \sum_i c_i(E) t^i$ of $E$ in the theory; together
with naturality of Chern classes under pullback, the Whitney sum formula and the projection
formula. -/
public def_wanted characteristicTheory
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f)) :
    CharacteristicClassTheory D P

end WantedExt.AlgebraicGeometry.BettiCharacteristicClassesWanted
