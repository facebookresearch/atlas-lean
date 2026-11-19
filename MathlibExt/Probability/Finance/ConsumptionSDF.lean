/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Field

/-!
# The marginal-utility stochastic discount factor

An investor with period utility `u`, time-discount factor `β`, date-0 endowment `e0` and
state-contingent date-1 endowment `e1` buys `ξ` units of an asset with price `p` and payoff `X`
on a finite state space with state weights `π`. In applications `π` is the physical probability
vector; the results hold for any real weights, so nonnegativity and normalization are not
assumed. The objective is `u (e0 - ξ p) + β ∑ ω, π ω * u (e1 ω + ξ X ω)`, which is expected
utility when `π` is a probability vector. If `ξ` is an interior optimum (a local maximum of the
objective over unrestricted holdings) at which `u` is differentiable, and date-0 marginal
utility is nonzero, the price satisfies the consumption pricing equation
`p = ∑ ω, π ω * (m ω * X ω)` with the stochastic discount factor `m = β u'(c1) / u'(c0)`; when
`π` is a probability vector this is `p = E[m X]`. With full support and positive marginal
utility the implied state prices `π m` are strictly positive.

The state space is finite, so the weighted sum is finite and differentiating under it needs no
interchange hypothesis. A measure-theoretic version needs a dominated-derivative hypothesis and
is not treated here. The deterministic two-period consumption Euler equation is the special
case of a riskless asset.

## Main results

* `price_eq_sum_marginalUtilitySDF_mul`: the pricing equation `p = ∑ ω, π ω * (m ω * X ω)`.
* `mul_marginalUtilitySDF_pos`: strictly positive state prices.

## References

* J. H. Cochrane, *Asset Pricing*, revised edition, Princeton University Press (2005),
  Section 1.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ConsumptionSDF

/-- Objective of an investor who buys `ξ` units of an asset with date-0 price `p` and
date-1 payoff `X ω` in state `ω`: date-0 consumption is `e0 - ξ * p`, date-1 consumption in
state `ω` is `e1 ω + ξ * X ω`, state `ω` has weight `π ω`, `u` is the period utility and `β`
the time-discount factor. When `π` is a probability vector this is expected utility; the results
below do not assume it. -/
def expectedUtility {Ω : Type*} [Fintype Ω] (u : ℝ → ℝ) (β : ℝ) (π : Ω → ℝ) (e0 p : ℝ)
    (e1 X : Ω → ℝ) (ξ : ℝ) : ℝ :=
  u (e0 - ξ * p) + β * ∑ ω, π ω * u (e1 ω + ξ * X ω)

/-- The marginal-utility stochastic discount factor `m ω = β u'(c1 ω) / u'(c0)` for date-0
consumption `c0` and date-1 consumption `c1`. -/
noncomputable def marginalUtilitySDF {Ω : Type*} (u : ℝ → ℝ) (β c0 : ℝ) (c1 : Ω → ℝ)
    (ω : Ω) : ℝ :=
  β * deriv u (c1 ω) / deriv u c0

/-- **Consumption pricing equation.** If holding `ξ` units is a local maximum of
`expectedUtility` over unrestricted holdings, `u` is differentiable at the resulting date-0
and date-1 consumption levels, and date-0 marginal utility is nonzero, then the price is the
`π`-weighted sum of SDF-weighted payoffs, `p = ∑ ω, π ω * (m ω * X ω)` with
`m = β u'(c1) / u'(c0)`; when `π` is a probability vector this is `p = E[m X]`. -/
theorem price_eq_sum_marginalUtilitySDF_mul {Ω : Type*} [Fintype Ω] {u : ℝ → ℝ} {β : ℝ}
    {π : Ω → ℝ} {e0 p : ℝ} {e1 X : Ω → ℝ} {ξ : ℝ}
    (hu0 : DifferentiableAt ℝ u (e0 - ξ * p))
    (hu1 : ∀ ω, DifferentiableAt ℝ u (e1 ω + ξ * X ω))
    (hmu : deriv u (e0 - ξ * p) ≠ 0)
    (hmax : IsLocalMax (expectedUtility u β π e0 p e1 X) ξ) :
    p = ∑ ω, π ω *
      (marginalUtilitySDF u β (e0 - ξ * p) (fun ω => e1 ω + ξ * X ω) ω * X ω) := by
  have hg0 : HasDerivAt (fun ξ => e0 - ξ * p) (-p) ξ := by
    have h : HasDerivAt ((fun _ : ℝ => e0) - (fun ξ : ℝ => ξ * p)) (0 - 1 * p) ξ :=
      (hasDerivAt_const ξ e0).sub ((hasDerivAt_id' ξ).mul_const p)
    have hr : (0 : ℝ) - 1 * p = -p := by ring
    rw [hr] at h
    exact h
  have hg1 : ∀ ω, HasDerivAt (fun ξ => e1 ω + ξ * X ω) (X ω) ξ := fun ω => by
    have h := ((hasDerivAt_id' ξ).mul_const (X ω)).const_add (e1 ω)
    simpa using h
  have hh0 : HasDerivAt (fun ξ => u (e0 - ξ * p)) (deriv u (e0 - ξ * p) * -p) ξ :=
    hu0.hasDerivAt.comp ξ hg0
  have hh1 : ∀ ω, HasDerivAt (fun ξ => u (e1 ω + ξ * X ω))
      (deriv u (e1 ω + ξ * X ω) * X ω) ξ :=
    fun ω => (hu1 ω).hasDerivAt.comp ξ (hg1 ω)
  have hk1 : ∀ ω, HasDerivAt (fun ξ => π ω * u (e1 ω + ξ * X ω))
      (π ω * (deriv u (e1 ω + ξ * X ω) * X ω)) ξ :=
    fun ω => (hh1 ω).const_mul (π ω)
  have hsum : HasDerivAt (fun ξ => ∑ ω, π ω * u (e1 ω + ξ * X ω))
      (∑ ω, π ω * (deriv u (e1 ω + ξ * X ω) * X ω)) ξ :=
    HasDerivAt.fun_sum (fun ω _ => hk1 ω)
  have hβ : HasDerivAt (fun ξ => β * ∑ ω, π ω * u (e1 ω + ξ * X ω))
      (β * ∑ ω, π ω * (deriv u (e1 ω + ξ * X ω) * X ω)) ξ :=
    hsum.const_mul β
  have hF : HasDerivAt (fun ξ => u (e0 - ξ * p) + β * ∑ ω, π ω * u (e1 ω + ξ * X ω))
      (deriv u (e0 - ξ * p) * -p
        + β * ∑ ω, π ω * (deriv u (e1 ω + ξ * X ω) * X ω)) ξ :=
    hh0.add hβ
  have hF' : HasDerivAt (expectedUtility u β π e0 p e1 X)
      (deriv u (e0 - ξ * p) * -p
        + β * ∑ ω, π ω * (deriv u (e1 ω + ξ * X ω) * X ω)) ξ := hF
  have h0 := hmax.hasDerivAt_eq_zero hF'
  have hS : p * deriv u (e0 - ξ * p)
      = β * ∑ ω, π ω * (deriv u (e1 ω + ξ * X ω) * X ω) := by
    linear_combination -h0
  have hRHS : (∑ ω, π ω * (marginalUtilitySDF u β (e0 - ξ * p)
      (fun ω => e1 ω + ξ * X ω) ω * X ω))
      = β * (∑ ω, π ω * (deriv u (e1 ω + ξ * X ω) * X ω)) / deriv u (e0 - ξ * p) := by
    simp only [marginalUtilitySDF]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => by ring)
  rw [hRHS, eq_div_iff hmu]
  exact hS

/-- With full support, a positive time-discount factor and positive marginal utility at both
dates, the implied state prices `π ω * m ω` are strictly positive. -/
theorem mul_marginalUtilitySDF_pos {Ω : Type*} {u : ℝ → ℝ} {β c0 : ℝ} {π : Ω → ℝ}
    {c1 : Ω → ℝ} (hβ : 0 < β) (hπ : ∀ ω, 0 < π ω) (hu0 : 0 < deriv u c0)
    (hu1 : ∀ ω, 0 < deriv u (c1 ω)) (ω : Ω) :
    0 < π ω * marginalUtilitySDF u β c0 c1 ω := by
  unfold marginalUtilitySDF
  exact mul_pos (hπ ω) (div_pos (mul_pos hβ (hu1 ω)) hu0)

end MathlibExt.Probability.Finance.ConsumptionSDF
