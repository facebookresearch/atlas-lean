/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Asymptotic Borsuk-number bounds
-/
module

public import Batteries.Util.ProofWanted

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Geometry.Euclidean.BorsukNumber

@[expose] public section

namespace WantedExt.Geometry.BorsukAsymptoticBoundsWanted

open Metric

/-- Kahn and Kalai's eventual exponential lower bound. This is an unproved claim.
Source: Optimization Problems, constant 28a, [KK1993-asymptotic]. -/
private theorem_wanted kahnKalaiAsymptoticLowerBound :
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    ENNReal.ofReal (Real.exp (c * Real.sqrt n)) ≤
      (dimensionBorsukNumber n : ENNReal)

/-- The explicit eventual lower bound in the cited abstract. This is an unproved claim.
Source: Kahn and Kalai (1993), abstract; constant 28a, [KK1993-asymptotic]. -/
private theorem_wanted kahnKalaiExplicitAsymptoticLowerBound :
  ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    ENNReal.ofReal ((6 / 5 : ℝ) ^ Real.sqrt n) ≤
      (dimensionBorsukNumber n : ENNReal)

/-- Lassak's bound, restricted to positive dimensions. This is an unproved claim.
Source: Optimization Problems, constant 28a, [KK1993-lassak-schramm]. -/
private theorem_wanted lassakUpperBound :
  ∀ n : ℕ, 0 < n → dimensionBorsukNumber n ≤ (2 ^ (n - 1) + 1 : ℕ∞)

/-- Schramm's upper bound for every positive error. This is an unproved claim.
Source: Optimization Problems, constant 28a, [KK1993-lassak-schramm]. -/
private theorem_wanted schrammAsymptoticUpperBound :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    (dimensionBorsukNumber n : ENNReal) ≤
      ENNReal.ofReal ((Real.sqrt (3 / 2) + ε) ^ n)

end WantedExt.Geometry.BorsukAsymptoticBoundsWanted
