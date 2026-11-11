/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Borrowing constraints and the consumption Euler condition

A two-period household with incomes `y₀, y₁` consumes `c₀` in period 0, saves
`y₀ - c₀` (borrows when negative) at the real rate `r`, and consumes
`c₁ = (1 + r) (y₀ - c₀) + y₁` in period 1, with lifetime utility
`u c₀ + β u c₁`. Feasible consumption is nonnegative in both periods and the
household borrows at most `b`: the single inequality `c₀ ≤ y₀ + b`.

At a feasible maximizer with positive consumption in both periods, the Euler
equality is replaced by the Karush–Kuhn–Tucker system for the borrowing limit:
a multiplier `μ ≥ 0` with `μ (c₀ - (y₀ + b)) = 0` and
`u'(c₀) = β (1 + r) u'(c₁) + μ`. Hence `β (1 + r) u'(c₁) ≤ u'(c₀)`, with
equality when the limit is slack. The constraint has derivative `1`, so the
regularity condition holds automatically and the proof is the one-sided Fermat
argument on the scalar choice variable. These are necessary conditions only;
neither `0 < β` nor `0 < 1 + r` is needed.

## Main results

* `MathlibExt.Economics.BorrowingConstraint.euler_complementary_slackness`
* `MathlibExt.Economics.BorrowingConstraint.euler_inequality`
* `MathlibExt.Economics.BorrowingConstraint.euler_equation_of_slack`

## References

Standard deterministic two-period consumption-saving model with a borrowing
constraint, as in intermediate macroeconomics courses (e.g. MIT 14.05,
consumption unit). Atlas roadmap target MA04.T04.
-/

namespace MathlibExt.Economics.BorrowingConstraint

/-- Period-1 consumption of a two-period household that consumes `c₀` in
period 0, saves `y₀ - c₀` (borrows when negative) at real rate `r`, and spends
all period-1 resources: `c₁ = (1 + r) (y₀ - c₀) + y₁`. -/
def nextConsumption (r y₀ y₁ c₀ : ℝ) : ℝ :=
  (1 + r) * (y₀ - c₀) + y₁

/-- Lifetime utility `u c₀ + β u c₁` along the binding budget line, as a function
of period-0 consumption. -/
def utilityAlongBudget (u : ℝ → ℝ) (β r y₀ y₁ c₀ : ℝ) : ℝ :=
  u c₀ + β * u (nextConsumption r y₀ y₁ c₀)

/-- Feasible period-0 consumptions under the borrowing limit `b`: consumption is
nonnegative in both periods and savings satisfy `y₀ - c₀ ≥ -b`, i.e. the
household borrows at most `b`, written as the single inequality `c₀ ≤ y₀ + b`. -/
def borrowingFeasible (r y₀ y₁ b : ℝ) : Set ℝ :=
  {c₀ | 0 ≤ c₀ ∧ 0 ≤ nextConsumption r y₀ y₁ c₀ ∧ c₀ ≤ y₀ + b}

/-- Inner budget map has derivative `-(1 + r)`. -/
theorem hasDerivAt_nextConsumption (r y₀ y₁ c₀ : ℝ) :
    HasDerivAt (nextConsumption r y₀ y₁) (-(1 + r)) c₀ := by
  have hid : HasDerivAt id (1 : ℝ) c₀ := hasDerivAt_id c₀
  have hsub : HasDerivAt (fun c : ℝ => y₀ - id c) (-1) c₀ := hid.const_sub y₀
  have hmul : HasDerivAt (fun c : ℝ => (1 + r) * (y₀ - id c)) ((1 + r) * (-1)) c₀ :=
    hsub.const_mul (1 + r)
  have hadd : HasDerivAt (fun c : ℝ => (1 + r) * (y₀ - id c) + y₁) ((1 + r) * (-1)) c₀ :=
    hmul.add_const y₁
  have hfun : (fun c : ℝ => (1 + r) * (y₀ - id c) + y₁) = nextConsumption r y₀ y₁ := by
    ext c
    simp [nextConsumption]
  have hder : (1 + r) * (-1 : ℝ) = -(1 + r) := by ring
  rw [hfun, hder] at hadd
  exact hadd

/-- Utility along the budget has derivative `u'(c₀) - β (1 + r) u'(c₁)`. -/
theorem hasDerivAt_utilityAlongBudget (u : ℝ → ℝ) (β r y₀ y₁ c₀ : ℝ)
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (nextConsumption r y₀ y₁ c₀)) :
    HasDerivAt (utilityAlongBudget u β r y₀ y₁)
      (deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀)) c₀ := by
  have hg : HasDerivAt (nextConsumption r y₀ y₁) (-(1 + r)) c₀ :=
    hasDerivAt_nextConsumption r y₀ y₁ c₀
  have hu₀' : HasDerivAt u (deriv u c₀) c₀ := hu₀.hasDerivAt
  have hu₁' : HasDerivAt u (deriv u (nextConsumption r y₀ y₁ c₀))
      (nextConsumption r y₀ y₁ c₀) := hu₁.hasDerivAt
  have hcomp : HasDerivAt (u ∘ nextConsumption r y₀ y₁)
      (deriv u (nextConsumption r y₀ y₁ c₀) * (-(1 + r))) c₀ :=
    hu₁'.comp c₀ hg
  have hcmul : HasDerivAt (fun c : ℝ => β * (u ∘ nextConsumption r y₀ y₁) c)
      (β * (deriv u (nextConsumption r y₀ y₁ c₀) * (-(1 + r)))) c₀ :=
    hcomp.const_mul β
  have hadd : HasDerivAt (u + fun c : ℝ => β * (u ∘ nextConsumption r y₀ y₁) c)
      (deriv u c₀ + β * (deriv u (nextConsumption r y₀ y₁ c₀) * (-(1 + r)))) c₀ :=
    hu₀'.add hcmul
  have hfun : (u + fun c : ℝ => β * (u ∘ nextConsumption r y₀ y₁) c)
      = utilityAlongBudget u β r y₀ y₁ := by
    ext c
    simp [utilityAlongBudget]
  have hder : deriv u c₀ + β * (deriv u (nextConsumption r y₀ y₁ c₀) * (-(1 + r)))
      = deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀) := by
    ring
  rw [hfun, hder] at hadd
  exact hadd

/-- The budget map `c₀ ↦ (1 + r) (y₀ - c₀) + y₁` is continuous at `c₀`. -/
theorem continuousAt_nextConsumption (r y₀ y₁ c₀ : ℝ) :
    ContinuousAt (nextConsumption r y₀ y₁) c₀ := by
  unfold nextConsumption
  fun_prop

/-- Euler condition with a borrowing constraint (KKT form): at a feasible
maximizer with positive consumption in both periods, there is a multiplier
`μ ≥ 0` on the borrowing limit, complementary slack with it, such that
`u'(c₀) = β (1 + r) u'(c₁) + μ`. -/
theorem euler_complementary_slackness {u : ℝ → ℝ} {β r y₀ y₁ b c₀ : ℝ}
    (hmax : IsMaxOn (utilityAlongBudget u β r y₀ y₁) (borrowingFeasible r y₀ y₁ b) c₀)
    (hmem : c₀ ∈ borrowingFeasible r y₀ y₁ b)
    (hc₀ : 0 < c₀) (hc₁ : 0 < nextConsumption r y₀ y₁ c₀)
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (nextConsumption r y₀ y₁ c₀)) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ * (c₀ - (y₀ + b)) = 0 ∧
      deriv u c₀ = β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀) + μ := by
  have hU : HasDerivAt (utilityAlongBudget u β r y₀ y₁)
      (deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀)) c₀ :=
    hasDerivAt_utilityAlongBudget u β r y₀ y₁ c₀ hu₀ hu₁
  obtain ⟨_, _, hle⟩ := hmem
  have hg_cont : ContinuousAt (nextConsumption r y₀ y₁) c₀ :=
    continuousAt_nextConsumption r y₀ y₁ c₀
  have hpos0 : ∀ᶠ x in nhds c₀, 0 < x := eventually_gt_nhds hc₀
  have hpos1 : ∀ᶠ x in nhds c₀, 0 < nextConsumption r y₀ y₁ x :=
    hg_cont.tendsto.eventually (eventually_gt_nhds hc₁)
  have hpos : ∀ᶠ x in nhds c₀, 0 < x ∧ 0 < nextConsumption r y₀ y₁ x :=
    hpos0.and hpos1
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hpos
  have hIoc_sub : Set.Ioc (c₀ - δ) c₀ ⊆ borrowingFeasible r y₀ y₁ b := by
    intro x hx
    obtain ⟨hx_left, hx_right⟩ := hx
    have hx_ball : x ∈ Metric.ball c₀ δ := by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have hmem' := hδ x hx_ball
    exact ⟨le_of_lt hmem'.1, le_of_lt hmem'.2, le_trans hx_right hle⟩
  rcases lt_or_eq_of_le hle with hslack | heq
  · have hev_lt : ∀ᶠ x in nhds c₀, x < y₀ + b := eventually_lt_nhds hslack
    have hev_mem : ∀ᶠ x in nhds c₀, x ∈ borrowingFeasible r y₀ y₁ b := by
      filter_upwards [hpos, hev_lt] with x hx hlt
      exact ⟨le_of_lt hx.1, le_of_lt hx.2, le_of_lt hlt⟩
    have hnhds : borrowingFeasible r y₀ y₁ b ∈ nhds c₀ :=
      Filter.eventually_mem_set.mp hev_mem
    have hloc : IsLocalMax (utilityAlongBudget u β r y₀ y₁) c₀ :=
      hmax.isLocalMax hnhds
    have hD0 : deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀) = 0 :=
      hloc.hasDerivAt_eq_zero hU
    refine ⟨0, le_refl 0, zero_mul _, ?_⟩
    linarith
  · have hTendsto : Filter.Tendsto (slope (utilityAlongBudget u β r y₀ y₁) c₀)
        (nhdsWithin c₀ (Set.Iio c₀))
        (nhds (deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀))) :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp hU).1
    have hIoc_mem : Set.Ioc (c₀ - δ) c₀ ∈ nhdsWithin c₀ (Set.Iio c₀) :=
      Ioc_mem_nhdsLT (by linarith)
    have hEv : ∀ᶠ x in nhdsWithin c₀ (Set.Iio c₀),
        0 ≤ slope (utilityAlongBudget u β r y₀ y₁) c₀ x := by
      filter_upwards [hIoc_mem] with x hx
      have hx_feas : x ∈ borrowingFeasible r y₀ y₁ b := hIoc_sub hx
      obtain ⟨_, hx_right⟩ := hx
      have hle_U : utilityAlongBudget u β r y₀ y₁ x
          ≤ utilityAlongBudget u β r y₀ y₁ c₀ :=
        (isMaxOn_iff.mp hmax) x hx_feas
      rw [slope_def_field]
      apply div_nonneg_of_nonpos
      · linarith
      · linarith
    have hD_nonneg : 0 ≤ deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀) :=
      ge_of_tendsto hTendsto hEv
    refine ⟨deriv u c₀ - β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀),
      hD_nonneg, ?_, ?_⟩
    · have hsub : c₀ - (y₀ + b) = 0 := by linarith
      rw [hsub, mul_zero]
    · ring

/-- The Euler equality is replaced by the inequality `β (1 + r) u'(c₁) ≤ u'(c₀)`
under a borrowing limit. -/
theorem euler_inequality {u : ℝ → ℝ} {β r y₀ y₁ b c₀ : ℝ}
    (hmax : IsMaxOn (utilityAlongBudget u β r y₀ y₁) (borrowingFeasible r y₀ y₁ b) c₀)
    (hmem : c₀ ∈ borrowingFeasible r y₀ y₁ b)
    (hc₀ : 0 < c₀) (hc₁ : 0 < nextConsumption r y₀ y₁ c₀)
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (nextConsumption r y₀ y₁ c₀)) :
    β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀) ≤ deriv u c₀ := by
  obtain ⟨μ, hμ_nonneg, _, heq⟩ :=
    euler_complementary_slackness hmax hmem hc₀ hc₁ hu₀ hu₁
  linarith

/-- If the borrowing limit is slack at the maximizer, the unconstrained Euler
equation `u'(c₀) = β (1 + r) u'(c₁)` holds. -/
theorem euler_equation_of_slack {u : ℝ → ℝ} {β r y₀ y₁ b c₀ : ℝ}
    (hmax : IsMaxOn (utilityAlongBudget u β r y₀ y₁) (borrowingFeasible r y₀ y₁ b) c₀)
    (hc₀ : 0 < c₀) (hc₁ : 0 < nextConsumption r y₀ y₁ c₀)
    (hslack : c₀ < y₀ + b)
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (nextConsumption r y₀ y₁ c₀)) :
    deriv u c₀ = β * (1 + r) * deriv u (nextConsumption r y₀ y₁ c₀) := by
  have hmem : c₀ ∈ borrowingFeasible r y₀ y₁ b :=
    ⟨le_of_lt hc₀, le_of_lt hc₁, le_of_lt hslack⟩
  obtain ⟨μ, _, hcomp, heq⟩ :=
    euler_complementary_slackness hmax hmem hc₀ hc₁ hu₀ hu₁
  have hne : c₀ - (y₀ + b) ≠ 0 := ne_of_lt (sub_neg.mpr hslack)
  have hμ0 : μ = 0 := (mul_eq_zero.mp hcomp).resolve_right hne
  rw [hμ0, add_zero] at heq
  exact heq

end MathlibExt.Economics.BorrowingConstraint
