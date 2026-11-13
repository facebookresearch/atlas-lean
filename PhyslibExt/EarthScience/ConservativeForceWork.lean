/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Comp

import Mathlib.Tactic.Linarith

/-!
# Work of a conservative force equals the potential decrease

## i. Overview

For a conservative force `F = -g`, where `g` is the gradient field of a
potential `U`, the work along an admissible path `γ` is the integral of
`⟪F (γ t), γ' t⟫` over the parameter interval, and it equals the
potential decrease `-(U (γ b) - U (γ a))`. The proof is the chain rule
for `U ∘ γ` followed by the fundamental theorem of calculus. The
gradient is phrased with `InnerProductSpace.toDual`: `g x` is the vector
with `toDual (g x) = fderiv ℝ U x`. The path is admissible when it is
differentiable on the interval with derivative `γ'` and the work
integrand is interval-integrable.

## ii. Key results

- `EarthScience.conservative_force_work_eq_potential_decrease`: work is
  the potential decrease along the path.

## iii. Table of contents

- A. Work of a conservative force

## iv. References

- `HasFDerivAt.comp_hasDerivAt` in Mathlib (chain rule).
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in Mathlib (FTC).
- `InnerProductSpace.toDual_apply_apply` in Mathlib.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-! ## A. Work of a conservative force -/

/-- Work of a conservative force along an admissible path equals the
potential decrease: if `F = -g` where `g` is the gradient field of `U`
(`HasFDerivAt U (toDual (g x)) x`), `γ` is differentiable on `[a, b]`
with derivative `γ'`, and the work integrand is interval-integrable,
then `∫ t in a..b, ⟪F (γ t), γ' t⟫ = -(U (γ b) - U (γ a))`. -/
theorem conservative_force_work_eq_potential_decrease
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {U : E → ℝ} {g F : E → E} {γ γ' : ℝ → E}
    (hF : ∀ x, F x = -g x)
    (hgrad : ∀ x, HasFDerivAt U (InnerProductSpace.toDual ℝ E (g x)) x)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hInt : IntervalIntegrable (fun t => inner ℝ (F (γ t)) (γ' t)) volume a b) :
    ∫ t in a..b, inner ℝ (F (γ t)) (γ' t) = -(U (γ b) - U (γ a)) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (U ∘ γ) (-inner ℝ (F (γ t)) (γ' t)) t := by
    intro t ht
    have hcomp := (hgrad (γ t)).comp_hasDerivAt t (hγ t ht)
    rw [InnerProductSpace.toDual_apply_apply] at hcomp
    have hg : g (γ t) = -F (γ t) := by rw [hF]; simp
    rw [hg, inner_neg_left] at hcomp
    exact hcomp
  have hIntNeg : IntervalIntegrable (fun t => -inner ℝ (F (γ t)) (γ' t)) volume a b :=
    hInt.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntNeg
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Function.comp_apply] at hFTC
  linarith

end EarthScience
