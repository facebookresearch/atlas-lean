/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Golden-rule condition for the discrete Solow model

Capital accumulates as `K' = s * Y + (1 - δ) * K`, while labor and labor-augmenting technology
grow by the factors `1 + n` and `1 + g` per period. For capital per effective worker `k` and
output per effective worker `f k`, the law of motion is therefore
`(1 + n) * (1 + g) * k' = s * f k + (1 - δ) * k`. A steady state at saving rate `s` is a `k`
with `k' = k` (`IsSteadyState`); it is feasible when `0 ≤ k`, `0 ≤ f k`, and `0 ≤ s ≤ 1`, so
that consumption and investment are nonnegative (`IsFeasibleSteadyState`).

At a steady state, consumption per effective worker `(1 - s) * f k` equals the objective
`goldenConsumption f δ n g k = f k - (δ + n + g + n * g) * k`
(`consumption_eq_goldenConsumption`), since `(1 + n) * (1 + g) - 1 = n + g + n * g`. The golden
rule maximizes steady-state consumption over feasible steady states; at an interior optimum the
marginal product equals the exact discrete break-even rate `δ + n + g + n * g`, not the
first-order approximation `δ + n + g`. The proof applies Fermat's theorem
(`IsLocalMax.deriv_eq_zero`, cited, not reproved) to the objective.

## Main results

* `consumption_eq_goldenConsumption`: steady-state consumption equals the objective.
* `goldenRule_condition`: at a feasible steady state whose consumption is maximal among nearby
  feasible steady states, with every nearby capital stock a feasible steady state and `f`
  differentiable, `deriv f k = δ + n + g + n * g`.
* `deriv_eq_breakEven_of_isLocalMax`: the unconstrained first-order condition for a local
  maximum of the objective over all real `k`, with no steady-state or feasibility hypothesis.
* `goldenConsumption_breakEven`: the break-even rate in expanded discrete-factor form.
* `goldenRule_example`: the quadratic example at `k = 49/10`, an unconstrained local maximum of
  the objective.

## References

* R. M. Solow, A contribution to the theory of economic growth, *Quarterly Journal of
  Economics* 70(1) (1956), 65–94.
* E. S. Phelps, The golden rule of accumulation: a fable for growthmen, *American Economic
  Review* 51(4) (1961), 638–643.
* P. B. Sørensen and H. J. Whitta-Jacobsen, *Introducing Advanced Macroeconomics: Growth and
  Business Cycles*, 3rd ed., Oxford University Press (2022), Chapter 3 (the basic Solow model
  in discrete time and the golden-rule saving rate) and Chapter 5 (the Solow model with
  technological progress).

Atlas roadmap target MA03.T03.
-/

@[expose] public section

open scoped Topology

namespace MathlibExt.Economics.Macro.SolowGoldenRule

/-- The steady-state consumption objective `f k - (δ + n + g + n * g) * k` on capital per
effective worker `k`. It is defined for every `k`; at a steady state with saving rate `s` it
equals consumption per effective worker `(1 - s) * f k`
(`consumption_eq_goldenConsumption`). -/
noncomputable def goldenConsumption (f : ℝ → ℝ) (δ n g : ℝ) (k : ℝ) : ℝ :=
  f k - (δ + n + g + n * g) * k

/-- The discrete Solow steady-state equation: with saving rate `s`, depreciation rate `δ`, and
labor and technology growing by the factors `1 + n` and `1 + g` per period, the law of motion
`(1 + n) * (1 + g) * k' = s * f k + (1 - δ) * k` keeps capital per effective worker at
`k' = k`. -/
def IsSteadyState (f : ℝ → ℝ) (s δ n g k : ℝ) : Prop :=
  (1 + n) * (1 + g) * k = s * f k + (1 - δ) * k

/-- A feasible steady state: capital per effective worker and output are nonnegative, the
saving rate `s` lies in `[0, 1]` (so consumption `(1 - s) * f k` and investment `s * f k` are
nonnegative), and `s` keeps `k` fixed. -/
structure IsFeasibleSteadyState (f : ℝ → ℝ) (s δ n g k : ℝ) : Prop where
  /-- Capital per effective worker is nonnegative. -/
  capital_nonneg : 0 ≤ k
  /-- Output per effective worker is nonnegative. -/
  output_nonneg : 0 ≤ f k
  /-- The saving rate lies in `[0, 1]`. -/
  rate_mem : s ∈ Set.Icc (0 : ℝ) 1
  /-- The saving rate keeps `k` fixed. -/
  steady : IsSteadyState f s δ n g k

/-- The break-even rate in the consumption function equals the expanded
discrete factor minus one plus depreciation. -/
theorem goldenConsumption_breakEven (f : ℝ → ℝ) (δ n g k : ℝ) :
    goldenConsumption f δ n g k =
      f k - ((1 + n) * (1 + g) - 1 + δ) * k := by
  unfold goldenConsumption
  ring

/-- At a steady state with saving rate `s`, consumption per effective worker `(1 - s) * f k`
equals the objective `goldenConsumption f δ n g k`. -/
theorem consumption_eq_goldenConsumption {f : ℝ → ℝ} {s δ n g k : ℝ}
    (h : IsSteadyState f s δ n g k) :
    (1 - s) * f k = goldenConsumption f δ n g k := by
  unfold IsSteadyState at h
  unfold goldenConsumption
  linear_combination h

/-- **Unconstrained first-order condition (Fermat).** At a local maximum of the objective
`goldenConsumption f δ n g` over all real `k`, with `f` differentiable there, the marginal
product equals the exact discrete break-even rate. No steady-state or feasibility hypothesis is
made; `goldenRule_condition` is the golden rule over feasible steady states. This cites
`IsLocalMax.deriv_eq_zero`; it does not reprove Fermat. -/
theorem deriv_eq_breakEven_of_isLocalMax {f : ℝ → ℝ} {δ n g k : ℝ}
    (hdiff : DifferentiableAt ℝ f k)
    (hmax : IsLocalMax (goldenConsumption f δ n g) k) :
    deriv f k = δ + n + g + n * g := by
  have hlin : DifferentiableAt ℝ (fun k => (δ + n + g + n * g) * k) k :=
    differentiableAt_id.const_mul _
  have hsub : deriv (f - fun k => (δ + n + g + n * g) * k) k
      = deriv f k - (δ + n + g + n * g) := by
    have h := deriv_sub hdiff hlin
    rwa [deriv_const_mul_id] at h
  have hfg : goldenConsumption f δ n g = f - fun k => (δ + n + g + n * g) * k := rfl
  have hzero := hmax.deriv_eq_zero
  rw [hfg, hsub] at hzero
  linarith

/-- **Golden rule.** Let `k` be a feasible steady state with saving rate `s₀` whose consumption
`(1 - s₀) * f k` is at least the consumption `(1 - s) * f x` of every feasible steady state
`(s, x)` with `x` near `k`. If every capital stock near `k` is a feasible steady state for some
saving rate (an interior optimum) and `f` is differentiable at `k`, then the marginal product
equals the exact discrete break-even rate `δ + n + g + n * g`. -/
theorem goldenRule_condition {f : ℝ → ℝ} {s₀ δ n g k : ℝ}
    (hdiff : DifferentiableAt ℝ f k)
    (hk : IsFeasibleSteadyState f s₀ δ n g k)
    (hint : ∀ᶠ x in 𝓝 k, ∃ s, IsFeasibleSteadyState f s δ n g x)
    (hmax : ∀ᶠ x in 𝓝 k, ∀ s, IsFeasibleSteadyState f s δ n g x →
      (1 - s) * f x ≤ (1 - s₀) * f k) :
    deriv f k = δ + n + g + n * g := by
  refine deriv_eq_breakEven_of_isLocalMax hdiff ?_
  filter_upwards [hint, hmax] with x ⟨s, hs⟩ hx
  rw [← consumption_eq_goldenConsumption hs.steady, ← consumption_eq_goldenConsumption hk.steady]
  exact hx s hs

/-- **Concrete first-order point.** For `f(k) = -k ^ 2 + 10 * k`, `δ = n = 1 / 10`, `g = 0`,
the point `k = 49 / 10` is a local maximum of the objective `goldenConsumption` over all real
`k`, and `deriv f (49 / 10) = 1 / 5 = δ + n + g + n * g`. -/
theorem goldenRule_example :
    IsLocalMax (goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0)
        (49 / 10) ∧
      deriv (fun k : ℝ => -k ^ 2 + 10 * k) (49 / 10) = 1 / 5 := by
  constructor
  · have hmax : IsMaxOn
        (goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0)
        Set.univ (49 / 10) := by
      intro k _
      change goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0 k ≤
        goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0 (49 / 10)
      have hdiff : goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0
            (49 / 10)
          - goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0 k
          = (k - 49 / 10) ^ 2 := by
        simp only [goldenConsumption]
        ring
      have hsq : 0 ≤ (k - 49 / 10) ^ 2 := sq_nonneg _
      linarith [hdiff, hsq]
    exact hmax.isLocalMax (isOpen_univ.mem_nhds (Set.mem_univ _))
  · have hpow : HasDerivAt (fun k : ℝ => k ^ 2) (2 * (49 / 10)) (49 / 10) := by
      simpa using hasDerivAt_pow 2 (49 / 10 : ℝ)
    have hlin : HasDerivAt (fun k : ℝ => 10 * k) 10 (49 / 10) := by
      simpa using (hasDerivAt_id (49 / 10 : ℝ)).const_mul 10
    have hderiv : deriv (fun k : ℝ => -k ^ 2 + 10 * k) (49 / 10)
        = -(2 * (49 / 10)) + 10 := (hpow.neg.add hlin).deriv
    rw [hderiv]
    norm_num

end MathlibExt.Economics.Macro.SolowGoldenRule
