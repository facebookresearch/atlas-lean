/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nowhere dense Julia sets of positive area (Lyubich, Stony Brook problems)

Stony Brook Open Problems in Dynamical Systems (1992), problem P1 (M. Lyubich): can a nowhere dense
Julia set of a rational map have positive Lebesgue measure?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Dynamics.NowhereDenseJuliaSetPositiveAreaAMR52Problem0041Wanted

/-!
Source: M. Lyubich, Stony Brook - Open Problems in Dynamical Systems (1992), problem P1,
https://www.math.stonybrook.edu/open-problems-dynamical-systems. UnsolvedMath record UM-05300041
(`AMR-052-0041`), dataset ulamai/UnsolvedMath v1.8.0.

The existential is witnessed inside the quadratic family `z ↦ z² + c`, whose Julia set is the
boundary of the filled Julia set (points with bounded orbit); a quadratic polynomial is a rational
map, so this implies the affirmative answer. Measure is Lebesgue measure on `ℂ`.
-/

/-- The filled Julia set of `z ↦ z ^ 2 + c`: the points whose forward orbit is bounded. -/
def filledJuliaSet (c : ℂ) : Set ℂ :=
  {z | ∃ R : ℝ, ∀ k : ℕ, ‖(fun w => w ^ 2 + c)^[k] z‖ ≤ R}

/-- The Julia set of `z ↦ z ^ 2 + c`: the boundary of its filled Julia set. -/
def juliaSet (c : ℂ) : Set ℂ :=
  frontier (filledJuliaSet c)

/-- Lyubich's question (Stony Brook problem list, 1992), with a quadratic witness: some quadratic
polynomial `z ↦ z ^ 2 + c` has a nowhere dense Julia set of positive Lebesgue measure. -/
def nowhereDenseJuliaSetOfPositiveArea : Prop :=
  ∃ c : ℂ, IsNowhereDense (juliaSet c) ∧ 0 < MeasureTheory.volume (juliaSet c)

/--
Resolved true: Buff and Chéritat proved that some quadratic polynomials have a Julia set of positive
Lebesgue measure; a polynomial Julia set is the boundary of the compact filled Julia set, so it is
nowhere dense. Each such polynomial is affinely conjugate to some `z ↦ z² + c`, which preserves
positive area. Source: M. Lyubich, Stony Brook - Open Problems in Dynamical Systems (1992), problem
P1, https://www.math.stonybrook.edu/open-problems-dynamical-systems; resolution: X. Buff and A.
Chéritat, Quadratic Julia sets with positive area, Ann. of Math. 176 (2012), 673-746,
arXiv:math/0605514, main theorem: quadratic polynomials with a Cremer point, a Siegel disk, or
infinitely many satellite renormalizations whose Julia set has positive area,
https://arxiv.org/abs/math/0605514.
-/
public theorem_wanted nowhereDenseJuliaSetOfPositiveArea_holds : nowhereDenseJuliaSetOfPositiveArea

end MathlibExt.Dynamics.NowhereDenseJuliaSetPositiveAreaAMR52Problem0041Wanted
