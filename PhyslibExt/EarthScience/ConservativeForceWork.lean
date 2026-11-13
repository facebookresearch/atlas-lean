/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp

import Mathlib.Tactic.Linarith

/-!
# Work of a conservative force equals the potential decrease

## i. Overview

For a conservative force `F = -g`, where `g` is the gradient field of a
potential `U`, the work along an admissible path `γ` is the integral of
`⟪F (γ t), γ' t⟫` over the parameter interval, and it equals the
potential decrease `-(U (γ b) - U (γ a))`. The proof is the chain rule
for `U ∘ γ` followed by the fundamental theorem of calculus. The path is
admissible when it is differentiable on the interval with derivative
`γ'` and the work integrand is interval-integrable.

The main statement uses Mathlib's `HasGradientAt U (g x) x`, which is
defined through the Riesz isomorphism `InnerProductSpace.toDual` and so
needs `[CompleteSpace E]`. The proof does not use completeness: the
general form states the gradient hypothesis as
`HasFDerivAt U (innerSL ℝ (g x)) x` and holds in every real inner
product space.

## ii. Key results

- `EarthScience.conservative_force_work_eq_potential_decrease`: work is
  the potential decrease along the path, for a gradient field in the
  sense of `HasGradientAt`.
- `EarthScience.conservative_force_work_eq_potential_decrease_of_hasFDerivAt`:
  the same identity in an arbitrary (not necessarily complete) real inner
  product space.

## iii. Table of contents

- A. Work of a conservative force

## iv. References

- `HasFDerivAt.comp_hasDerivAt` in Mathlib (chain rule).
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in Mathlib (FTC).
- `HasGradientAt` and `hasGradientAt_iff_hasFDerivAt` in Mathlib.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-! ## A. Work of a conservative force -/

/-- Work of a conservative force along an admissible path equals the
potential decrease, in any real inner product space: if `F = -g` where
`g x` represents the derivative of `U` at `x` (`HasFDerivAt U (innerSL ℝ (g x)) x`),
`γ` is differentiable on `[a, b]` with derivative `γ'`, and the work
integrand is interval-integrable, then
`∫ t in a..b, ⟪F (γ t), γ' t⟫ = -(U (γ b) - U (γ a))`. -/
theorem conservative_force_work_eq_potential_decrease_of_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b : ℝ} {U : E → ℝ} {g F : E → E} {γ γ' : ℝ → E}
    (hF : ∀ x, F x = -g x)
    (hgrad : ∀ x, HasFDerivAt U (innerSL ℝ (g x)) x)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hInt : IntervalIntegrable (fun t => inner ℝ (F (γ t)) (γ' t)) volume a b) :
    ∫ t in a..b, inner ℝ (F (γ t)) (γ' t) = -(U (γ b) - U (γ a)) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (U ∘ γ) (-inner ℝ (F (γ t)) (γ' t)) t := by
    intro t ht
    have hcomp := (hgrad (γ t)).comp_hasDerivAt t (hγ t ht)
    rw [innerSL_apply_apply] at hcomp
    have hg : g (γ t) = -F (γ t) := by rw [hF]; simp
    rw [hg, inner_neg_left] at hcomp
    exact hcomp
  have hIntNeg : IntervalIntegrable (fun t => -inner ℝ (F (γ t)) (γ' t)) volume a b :=
    hInt.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntNeg
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Function.comp_apply] at hFTC
  linarith

/-- Work of a conservative force along an admissible path equals the
potential decrease: if `F = -g` where `g` is the gradient field of `U`
(`HasGradientAt U (g x) x`), `γ` is differentiable on `[a, b]` with
derivative `γ'`, and the work integrand is interval-integrable, then
`∫ t in a..b, ⟪F (γ t), γ' t⟫ = -(U (γ b) - U (γ a))`. The space is
complete because Mathlib's `HasGradientAt` requires it; see
`conservative_force_work_eq_potential_decrease_of_hasFDerivAt` for the
general form. -/
theorem conservative_force_work_eq_potential_decrease
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {U : E → ℝ} {g F : E → E} {γ γ' : ℝ → E}
    (hF : ∀ x, F x = -g x)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hInt : IntervalIntegrable (fun t => inner ℝ (F (γ t)) (γ' t)) volume a b) :
    ∫ t in a..b, inner ℝ (F (γ t)) (γ' t) = -(U (γ b) - U (γ a)) :=
  conservative_force_work_eq_potential_decrease_of_hasFDerivAt hF
    (fun x => (hgrad x).hasFDerivAt) hγ hInt

end EarthScience
