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
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Golden-rule condition

At a steady state the saving rate needed to sustain capital `k` is
`s(k) = (D - 1 + delta) * k / f(k)` with `D = (1 + n) * (1 + g)`, so
steady-state consumption per effective worker is
`c(k) = f(k) - (D - 1 + delta) * k`. Since `D - 1 = n + g + n * g`, the
exact discrete break-even rate is `delta + n + g + n * g`, not the
first-order approximation `delta + n + g`. The condition is Fermat applied
to steady-state consumption: it cites `IsLocalMax.deriv_eq_zero` and does
not reprove it.

## Main results

* `MathlibExt.Economics.Macro.SolowGoldenRule.goldenRule_condition`: at an
  interior local maximum of steady-state consumption, the marginal product
  equals the exact discrete break-even rate.
* `MathlibExt.Economics.Macro.SolowGoldenRule.goldenConsumption_breakEven`:
  the break-even rate in expanded discrete-factor form.
* `MathlibExt.Economics.Macro.SolowGoldenRule.goldenRule_example`: the
  concrete quadratic example at `k = 49/10`.

## References

Atlas roadmap target MA03.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SolowGoldenRule

/-- Steady-state consumption per effective worker as a function of the
capital stock, at the saving rate that sustains that stock. -/
noncomputable def goldenConsumption (f : ℝ → ℝ) (δ n g : ℝ) (k : ℝ) : ℝ :=
  f k - (δ + n + g + n * g) * k

/-- The break-even rate in the consumption function equals the expanded
discrete factor minus one plus depreciation. -/
theorem goldenConsumption_breakEven (f : ℝ → ℝ) (δ n g k : ℝ) :
    goldenConsumption f δ n g k =
      f k - ((1 + n) * (1 + g) - 1 + δ) * k := by
  unfold goldenConsumption
  ring

/-- **Golden rule (Fermat).** At an interior local maximum of steady-state
consumption, with `f` differentiable there, the marginal product equals the
exact discrete break-even rate. This cites `IsLocalMax.deriv_eq_zero`; it
does not reprove Fermat. -/
theorem goldenRule_condition {f : ℝ → ℝ} {δ n g k : ℝ}
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

/-- **Concrete golden-rule point.** For `f(k) = -k ^ 2 + 10 * k`,
`δ = n = 1 / 10`, `g = 0`, the point `k = 49 / 10` is a local maximum of
steady-state consumption and `deriv f (49 / 10) = 1 / 5 = δ + n + g + n * g`. -/
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
