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

@[expose] public section

/-!
# The two-period consumption Euler equation

A household with incomes `y₀, y₁` consumes `c₀` in period 0, saves or borrows
`y₀ - c₀` at the real interest rate `r`, and consumes
`c₁ = (1 + r) (y₀ - c₀) + y₁` in period 1. Lifetime utility is
`u c₀ + β u c₁`, and feasible consumption is nonnegative in both periods. When
the gross return `1 + r` is positive, `0 ≤ c₁` is the natural borrowing limit
`c₀ ≤ y₀ + y₁ / (1 + r)`, so borrowing is bounded; the definitions impose no
sign condition on `1 + r`.

At an interior maximizer (`0 < c₀`, `0 < c₁`) at which `u` is differentiable,
the consumption Euler equation `u'(c₀) = β (1 + r) u'(c₁)` holds. This is a
necessary first-order condition: it needs neither `0 < β` nor `0 < 1 + r`, and
it asserts no existence, uniqueness, or sufficiency. Infinite-horizon versions
need terminal conditions and are not treated here. A binding borrowing limit
replaces the equation by complementary slackness (Atlas roadmap MA04.T04, a
separate file).

## Main results

* `MathlibExt.Economics.IntertemporalChoice.hasDerivAt_lifetimeUtility`: the
  derivative of lifetime utility along the budget line is
  `u'(c₀) - β (1 + r) u'(c₁)`.
* `MathlibExt.Economics.IntertemporalChoice.euler_equation`: the Euler
  equation at an interior maximizer over the feasible set.

## References

Standard deterministic two-period consumption-saving model, as in
intermediate macroeconomics courses (e.g. MIT 14.05, consumption unit).
Atlas roadmap target MA04.T02.
-/

namespace MathlibExt.Economics.IntertemporalChoice

/-- Second-period consumption of a two-period household that consumes `c₀` in
period 0, saves (or borrows) `y₀ - c₀` at the real interest rate `r`, and
spends all period-1 resources: `c₁ = (1 + r) (y₀ - c₀) + y₁`. -/
def secondPeriodConsumption (r y₀ y₁ c₀ : ℝ) : ℝ :=
  (1 + r) * (y₀ - c₀) + y₁

/-- Lifetime utility `u c₀ + β u c₁` along the binding intertemporal budget
line, as a function of first-period consumption `c₀`. -/
def lifetimeUtility (u : ℝ → ℝ) (β r y₀ y₁ c₀ : ℝ) : ℝ :=
  u c₀ + β * u (secondPeriodConsumption r y₀ y₁ c₀)

/-- Feasible first-period consumptions: both periods' consumption are
nonnegative. When `0 < 1 + r`, the constraint `0 ≤ c₁` is the natural borrowing
limit `c₀ ≤ y₀ + y₁ / (1 + r)`, so borrowing is bounded. No sign condition on
`1 + r` is imposed here: if `1 + r ≤ 0`, the constraint `0 ≤ c₁` does not bound
borrowing. -/
def feasibleConsumption (r y₀ y₁ : ℝ) : Set ℝ :=
  {c₀ | 0 ≤ c₀ ∧ 0 ≤ secondPeriodConsumption r y₀ y₁ c₀}

/-- Derivative of lifetime utility along the budget line (chain rule). -/
theorem hasDerivAt_lifetimeUtility {u : ℝ → ℝ} {β r y₀ y₁ c₀ : ℝ}
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (secondPeriodConsumption r y₀ y₁ c₀)) :
    HasDerivAt (lifetimeUtility u β r y₀ y₁)
      (deriv u c₀ - β * (1 + r) * deriv u (secondPeriodConsumption r y₀ y₁ c₀)) c₀ := by
  have hconst : HasDerivAt (fun _ : ℝ => y₀) 0 c₀ := hasDerivAt_const c₀ y₀
  have hid : HasDerivAt (fun c : ℝ => c) 1 c₀ := hasDerivAt_id c₀
  have hsub : HasDerivAt (fun c : ℝ => y₀ - c) (-1) c₀ := by
    have h := hconst.sub hid
    rw [zero_sub] at h
    exact h
  have hmul : HasDerivAt (fun c : ℝ => (1 + r) * (y₀ - c)) ((1 + r) * -1) c₀ :=
    hsub.const_mul (1 + r)
  have hg : HasDerivAt (fun c : ℝ => (1 + r) * (y₀ - c) + y₁) ((1 + r) * -1) c₀ :=
    hmul.add_const y₁
  have hcomp := hu₁.hasDerivAt.comp c₀ hg
  have hscaled := hcomp.const_mul β
  have hadd := hu₀.hasDerivAt.add hscaled
  simp only [Function.comp_apply] at hadd
  refine hadd.congr_deriv ?_
  ring

/-- Consumption Euler equation: an interior maximizer of lifetime utility over
the feasible set, with `u` differentiable at both consumption levels, satisfies
`u'(c₀) = β (1 + r) u'(c₁)`. -/
theorem euler_equation {u : ℝ → ℝ} {β r y₀ y₁ c₀ : ℝ}
    (hmax : IsMaxOn (lifetimeUtility u β r y₀ y₁) (feasibleConsumption r y₀ y₁) c₀)
    (hc₀ : 0 < c₀) (hc₁ : 0 < secondPeriodConsumption r y₀ y₁ c₀)
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (secondPeriodConsumption r y₀ y₁ c₀)) :
    deriv u c₀ = β * (1 + r) * deriv u (secondPeriodConsumption r y₀ y₁ c₀) := by
  have hcont : Continuous fun c : ℝ => secondPeriodConsumption r y₀ y₁ c := by
    unfold secondPeriodConsumption
    exact (continuous_const.mul (continuous_const.sub continuous_id)).add continuous_const
  have h1 : IsOpen {c : ℝ | (0:ℝ) < c} := isOpen_lt continuous_const continuous_id
  have h2 : IsOpen {c : ℝ | (0:ℝ) < secondPeriodConsumption r y₀ y₁ c} :=
    isOpen_lt continuous_const hcont
  have hs : IsOpen {c : ℝ | 0 < c ∧ 0 < secondPeriodConsumption r y₀ y₁ c} :=
    h1.inter h2
  have hmem : c₀ ∈ {c : ℝ | 0 < c ∧ 0 < secondPeriodConsumption r y₀ y₁ c} := ⟨hc₀, hc₁⟩
  have hnh := hs.mem_nhds hmem
  have hsub : {c : ℝ | 0 < c ∧ 0 < secondPeriodConsumption r y₀ y₁ c}
      ⊆ feasibleConsumption r y₀ y₁ := by
    intro c hc
    exact ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  have hfeas : feasibleConsumption r y₀ y₁ ∈ nhds c₀ := Filter.mem_of_superset hnh hsub
  have hloc : IsLocalMax (lifetimeUtility u β r y₀ y₁) c₀ := hmax.isLocalMax hfeas
  have hderiv := hasDerivAt_lifetimeUtility (β := β) hu₀ hu₁
  have hz := hloc.hasDerivAt_eq_zero hderiv
  exact sub_eq_zero.mp hz

end MathlibExt.Economics.IntertemporalChoice
