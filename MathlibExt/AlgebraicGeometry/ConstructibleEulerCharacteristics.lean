/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompactSupportBetti
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Compact-support Betti Euler characteristics and constructible weights

Euler characteristics below are finite alternating sums of the ranks
of the actual rational compact-support cohomology. Finiteness and a
vanishing bound are retained; finrank of an infinite-dimensional space
is not used to certify finiteness. The ordinary Betti version is kept
separate for the Milnor fibre in Behrend's critical-chart formula.

A constructible presentation uses genuine finite smooth locally closed
algebraic strata and their actual images on complex points. Weighted
Euler integration is the sum of the constant weights times these
compact-support Euler characteristics. Independence of presentations
is a separate theorem, not a freely supplied Euler function.

References: Behrend, arXiv:math/0507523v2, §1.2, equations (3)–(4);
Bridgeland, arXiv:1002.4374v3, Theorem 5.1, equation (25).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

/-- Finite compact-support Betti ranks, with an actual upper vanishing bound. -/
structure FiniteCompactBetti (Z : TopCat.{0}) where
  bound : ℕ
  finite : ∀ n : ℕ, FiniteDimensional ℚ (CompactSupportBetti.Cohomology Z n)
  vanishing : ∀ n : ℕ, bound < n → IsZero (CompactSupportBetti.Cohomology Z n)

/-- The Euler characteristic of actual compact-support rational cohomology. -/
def compactEuler {Z : TopCat.{0}} (B : FiniteCompactBetti Z) : ℤ :=
  ∑ n ∈ Finset.range (B.bound+1), (-1 : ℤ)^n *
    (Module.finrank ℚ (CompactSupportBetti.Cohomology Z n) : ℤ)

/-- Finite ordinary Betti ranks for a genuine topological Milnor fibre. -/
structure FiniteOrdinaryBetti (Z : TopCat.{0}) where
  bound : ℕ
  finite : ∀ n : ℕ, FiniteDimensional ℚ (BettiRealization.Cohomology Z (n : ℤ))
  vanishing : ∀ n : ℕ, bound < n →
    Subsingleton (BettiRealization.Cohomology Z (n : ℤ))

/-- Ordinary Euler characteristic, used in the critical-chart normalization. -/
def ordinaryEuler {Z : TopCat.{0}} (B : FiniteOrdinaryBetti Z) : ℤ :=
  ∑ n ∈ Finset.range (B.bound+1), (-1 : ℤ)^n *
    (Module.finrank ℚ (BettiRealization.Cohomology Z (n : ℤ)) : ℤ)

/-- A point belongs to a stratum precisely by its actual complex-point map. -/
def inStratum {X : ComplexScheme} (S : AlgebraicStratification X) (i : Fin S.count)
    (p : space X) : Prop := p ∈ Set.range (spaceMap (S.inclusion i))

/-- The integer weight is computed from the actual disjoint stratum images. -/
def stratumWeight {X : ComplexScheme} (S : AlgebraicStratification X)
    (w : Fin S.count → ℤ) (p : space X) : ℤ := by
  classical
  exact ∑ i, if inStratum S i p then w i else 0

/-- A constructible function has a genuine finite algebraic presentation. -/
structure ConstructiblePresentation (X : ComplexScheme) (f : space X → ℤ) where
  strata : AlgebraicStratification X
  weights : Fin strata.count → ℤ
  complexCover : ∀ p : space X, ∃ i : Fin strata.count, inStratum strata i p
  normalized : ∀ p : space X, f p = stratumWeight strata weights p

/-- Every stratum's actual compact-support cohomology has finite Euler sum. -/
structure EulerPresentation (X : ComplexScheme) (f : space X → ℤ)
    extends ConstructiblePresentation X f where
  betti : ∀ i : Fin strata.count, FiniteCompactBetti (space (strata.stratum i))

/-- The actual constructible weighted compact-support integral. -/
def weightedEuler {X : ComplexScheme} {f : space X → ℤ} (P : EulerPresentation X f) : ℤ :=
  ∑ i, P.weights i * compactEuler (P.betti i)

/-- Pull a specified weight back along the actual complex-point scheme map. -/
def pulledWeight {X Y : ComplexScheme} (g : X ⟶ Y) (f : space Y → ℤ) : space X → ℤ :=
  f ∘ spaceMap g

end MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics
