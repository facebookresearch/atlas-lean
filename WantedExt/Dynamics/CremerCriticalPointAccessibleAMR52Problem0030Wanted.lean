/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Accessibility of the critical point of a Cremer quadratic polynomial (Milnor)

Milnor, Problems in holomorphic dynamics (Stony Brook, 1992), problems on local connectivity,
Problem 5: can the critical point of a Cremer polynomial `P(z) = z² + e^{2πiα} z` be accessible from
the complement of its Julia set?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.Dynamics.CremerCriticalPointAccessibleAMR52Problem0030Wanted

/-!
Source: J. Milnor (ed.), Problems in holomorphic dynamics (Stony Brook, 1992), arXiv:math/9205209,
Problems on local connectivity, Problem 5,
https://www.math.stonybrook.edu/open-problems-dynamical-systems. UnsolvedMath record UM-05300030
(`AMR-052-0030`), dataset ulamai/UnsolvedMath v1.8.0.

The Julia set of `P_α` is the boundary of its filled Julia set (bounded orbits). `0` is a Cremer
point when `α` is irrational and `P_α` is not linearizable at `0` (no holomorphic `φ` on a disc with
`φ 0 = 0`, `φ' 0 = 1`, `P_α ∘ φ = φ ∘ (z ↦ e^{2πiα} z)`); for Siegel parameters such a `φ` exists,
so they are excluded. The critical point is `-e^{2πiα}/2`; it is accessible if it is the endpoint of
a path `γ : [0, 1] → ℂ` with `γ t ∉ J` for `t < 1`.
-/

open Complex

/-- The multiplier `λ = e^{2πiα}` of the fixed point `0`. -/
noncomputable def multiplier (α : ℝ) : ℂ :=
  exp (2 * Real.pi * I * α)

/-- The quadratic polynomial `P_α(z) = z ^ 2 + e^{2πiα} z`, with a fixed point at `0` of
multiplier `e^{2πiα}`. -/
noncomputable def quadMap (α : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 + multiplier α * z

/-- The filled Julia set of `P_α`: the points whose forward orbit is bounded. -/
def filledJuliaSet (α : ℝ) : Set ℂ :=
  {z | ∃ R : ℝ, ∀ k : ℕ, ‖(quadMap α)^[k] z‖ ≤ R}

/-- The Julia set of `P_α`: the boundary of its filled Julia set. -/
def juliaSet (α : ℝ) : Set ℂ :=
  frontier (filledJuliaSet α)

/-- `0` is a Cremer point of `P_α`: `α` is irrational and `P_α` is not linearizable at `0`, that is,
there is no holomorphic `φ` on a disc around `0` with `φ 0 = 0`, `φ' 0 = 1` and
`P_α (φ z) = φ (λ z)`. -/
def IsCremer (α : ℝ) : Prop :=
  Irrational α ∧ ¬ ∃ (φ : ℂ → ℂ) (r : ℝ), 0 < r ∧ DifferentiableOn ℂ φ (Metric.ball 0 r) ∧
    φ 0 = 0 ∧ deriv φ 0 = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) r, quadMap α (φ z) = φ (multiplier α * z)

/-- The point `z` is accessible from the complement of the Julia set of `P_α`: it is the endpoint
of a path whose other points avoid the Julia set. -/
def IsAccessible (α : ℝ) (z : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ (∀ t ∈ Set.Ico (0 : ℝ) 1, γ t ∉ juliaSet α) ∧
    γ 1 = z

/-- Milnor's question, with a positive answer: for some Cremer parameter `α`, the critical point
`-λ/2` of `P_α` is accessible from the complement of the Julia set. -/
def cremerCriticalPointAccessible : Prop :=
  ∃ α : ℝ, IsCremer α ∧ IsAccessible α (-(multiplier α) / 2)

/--
Resolved false: Kiwi (Corollary 1.2) proves that the critical point of a quadratic polynomial with a
Cremer periodic point is not accessible from the complement of its Julia set; in particular for
every Cremer parameter `α` the critical point of `P_α` is not accessible. Source: J. Milnor (ed.),
Problems in holomorphic dynamics (Stony Brook, 1992), arXiv:math/9205209, Problems on local
connectivity, Problem 5, https://www.math.stonybrook.edu/open-problems-dynamical-systems;
resolution: J. Kiwi, Non-accessible critical points of Cremer polynomials, Ergodic Theory Dynam.
Systems 20 (2000); arXiv:math/9502235, Corollary 1.2: the critical point of a quadratic polynomial P
with a Cremer periodic point is not accessible from the complement of the Julia set (from the main
theorem and Yoccoz's result that quadratic Cremer points are approximated by small cycles),
https://doi.org/10.1017/S0143385700000754.
-/
public theorem_wanted cremerCriticalPointAccessible_refuted : ¬ cremerCriticalPointAccessible

end MathlibExt.Dynamics.CremerCriticalPointAccessibleAMR52Problem0030Wanted
