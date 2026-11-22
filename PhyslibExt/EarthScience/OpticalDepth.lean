/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Optical depth adds across absorption-only layers

For an absorption-only (no-scattering) atmosphere, the optical depth
of a layer from `a` to `b` is `tau(a, b) = integral_x in a..b, kappa x`,
where `kappa >= 0` is the absorption coefficient. Optical depth adds
across adjacent layers, `tau(a, c) = tau(a, b) + tau(b, c)`, because
the interval integral splits at `b`. Beer-Lambert transmission through
a layer is `exp(-tau)`; it multiplies across layers, and across
finitely many layers `exp(-sum_i tau_i) = prod_i exp(-tau_i)`.

## i. Overview

Additivity is `intervalIntegral.integral_add_adjacent_intervals`.
Transmission multiplication follows from `Real.exp_add` and
`Real.exp_sum`. The boundary cases are `integral_same` (zero
thickness) and `intervalIntegral.integral_nonneg` (nonnegative
absorption).

## ii. Key results

- `EarthScience.opticalDepth`: optical depth as an interval integral.
- `EarthScience.optical_depth_add`: additivity across adjacent layers.
- `EarthScience.transmission_mul_layers`: Beer-Lambert transmission
  multiplies across finitely many layers.
- `EarthScience.transmission_mul_two_layers`: Beer-Lambert transmission
  multiplies across two adjacent layers.
- `EarthScience.optical_depth_nonneg`: zero thickness gives zero depth;
  nonnegative absorption gives nonnegative depth.

## iii. Table of contents

- A. Optical depth and Beer-Lambert transmission

## iv. References

- J. Marshall and R. A. Plumb, *Atmosphere, Ocean, and Climate
  Dynamics: An Introductory Text*, Elsevier Academic Press (2008),
  Chapter 2: optical depth and Beer-Lambert attenuation.
- `intervalIntegral.integral_add_adjacent_intervals`,
  `intervalIntegral.integral_nonneg`, `Real.exp_sum` in Mathlib.

## A. Optical depth and Beer-Lambert transmission
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

open MeasureTheory intervalIntegral

/-- Optical depth of an absorption-only layer: `τ(a, b) = ∫ x in a..b, κ x`,
with `κ` the absorption coefficient. -/
noncomputable def opticalDepth (κ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, κ x

set_option linter.unusedVariables false in
/-- Optical depth adds across adjacent layers: `τ(a, c) = τ(a, b) + τ(b, c)`. -/
theorem optical_depth_add (κ : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hint1 : IntervalIntegrable κ volume a b)
    (hint2 : IntervalIntegrable κ volume b c) :
    opticalDepth κ a c = opticalDepth κ a b + opticalDepth κ b c := by
  unfold opticalDepth
  exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm

/-- Beer-Lambert transmission multiplies across layers: with total
optical depth `τ = ∑ τᵢ`, transmission `exp(-τ)` is the product of the
per-layer transmissions `exp(-τᵢ)`. -/
theorem transmission_mul_layers (τ : ℕ → ℝ) (n : ℕ) :
    Real.exp (-∑ i ∈ Finset.range n, τ i) =
      ∏ i ∈ Finset.range n, Real.exp (-τ i) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

/-- Beer-Lambert transmission multiplies across two adjacent layers. -/
theorem transmission_mul_two_layers (κ : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hint1 : IntervalIntegrable κ volume a b)
    (hint2 : IntervalIntegrable κ volume b c) :
    Real.exp (-opticalDepth κ a c) =
      Real.exp (-opticalDepth κ a b) * Real.exp (-opticalDepth κ b c) := by
  have h := optical_depth_add κ a b c hab hbc hint1 hint2
  rw [h, neg_add, Real.exp_add]

set_option linter.unusedVariables false in
/-- Boundary cases: zero thickness gives zero optical depth, and
nonnegative absorption gives nonnegative optical depth. -/
theorem optical_depth_nonneg (κ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hκ : ∀ x ∈ Set.Icc a b, 0 ≤ κ x)
    (hint : IntervalIntegrable κ volume a b) :
    0 ≤ opticalDepth κ a b ∧ opticalDepth κ a a = 0 := by
  constructor
  · unfold opticalDepth
    exact intervalIntegral.integral_nonneg hab hκ
  · unfold opticalDepth
    exact intervalIntegral.integral_same

end EarthScience
