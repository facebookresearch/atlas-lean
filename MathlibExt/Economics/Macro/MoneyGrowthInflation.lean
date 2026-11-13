/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# Inflation equals money growth minus output growth at constant velocity

With the quantity equation `M * V = P * Y` holding at constant velocity `V`,
price growth is money growth minus real-output growth. Two labeled forms:
exactly, in growth factors, `(P₁/P₀) = (M₁/M₀) / (Y₁/Y₀)`; log-differenced,
`Ṗ/P = Ṁ/M − Ẏ/Y`, where the growth rate `deriv f t / f t` is the derivative
of `Real.log ∘ f`. Neither form assumes output growth is zero. Velocity
constancy is a premise here (a single constant `V`), unlike MA05.T01, where
velocity is only defined.

## Main results

* `inflation_exact`: the exact growth-factor relation.
* `inflation_logDiff`: the log-differenced relation.

## References

* I. Fisher, *The Purchasing Power of Money*, Macmillan (1911).

Atlas roadmap target MA05.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.MoneyGrowthInflation

/-- **Exact inflation–money-growth relation.** If the quantity equation holds
at two dates with the SAME constant velocity `V ≠ 0`, then the price growth
factor is the money growth factor divided by the real-output growth factor
(Atlas roadmap MA05.T02, exact form). In `1 + x` notation: with
`1 + π = P₁/P₀`, `1 + μ = M₁/M₀`, `1 + g = Y₁/Y₀`, this is
`1 + π = (1 + μ) / (1 + g)`. -/
theorem inflation_exact {M0 M1 P0 P1 Y0 Y1 V : ℝ}
    (h0 : M0 * V = P0 * Y0) (h1 : M1 * V = P1 * Y1)
    (hV : V ≠ 0) (hM0 : M0 ≠ 0) (hY0 : Y0 ≠ 0) (hP0 : P0 ≠ 0) (hY1 : Y1 ≠ 0) :
    P1 / P0 = (M1 / M0) / (Y1 / Y0) := by
  field_simp
  linear_combination M1 * h0 - M0 * h1

/-- **Log-differenced inflation–money-growth relation.** If `M * V = P * Y`
holds along differentiable paths with `V` a single constant, then at any `t`
with all values nonzero, inflation equals money growth minus real-output
growth: `Ṗ/P = Ṁ/M − Ẏ/Y` (Atlas roadmap MA05.T02, log-differenced form).
Velocity constancy is built in: `V` is a constant, not a function of `t`. -/
theorem inflation_logDiff {M P Y : ℝ → ℝ} {V t : ℝ}
    (hMV : ∀ s, M s * V = P s * Y s) (hV0 : V ≠ 0)
    {M' P' Y' : ℝ}
    (hM : HasDerivAt M M' t) (hP : HasDerivAt P P' t) (hY : HasDerivAt Y Y' t)
    (hM0 : M t ≠ 0) (hP0 : P t ≠ 0) (hY0 : Y t ≠ 0) :
    logDeriv P t = logDeriv M t - logDeriv Y t := by
  unfold logDeriv
  simp only [Pi.div_apply]
  have hMderiv : deriv M t = M' := hM.deriv
  have hPderiv : deriv P t = P' := hP.deriv
  have hYderiv : deriv Y t = Y' := hY.deriv
  rw [hMderiv, hPderiv, hYderiv]
  have hfun : (fun s => M s * V) = (fun s => P s * Y s) := funext hMV
  have hMVderiv : HasDerivAt (fun s => M s * V) (M' * V) t := hM.mul_const V
  have hPYderiv : HasDerivAt (fun s => P s * Y s) (P' * Y t + P t * Y') t := hP.mul hY
  rw [hfun] at hMVderiv
  have hEq : M' * V = P' * Y t + P t * Y' := hMVderiv.unique hPYderiv
  have hqt : M t * V = P t * Y t := hMV t
  field_simp
  linear_combination M' * hqt - M t * hEq

end MathlibExt.Economics.Macro.MoneyGrowthInflation
