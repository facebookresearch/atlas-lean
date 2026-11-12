/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# Growth accounting by log differentiation

For output `Y = A * F(K, L)` with TFP `A`, capital `K`, labour `L`, and a
differentiable two-input production function `F`, log differentiation gives
growth accounting: `Ẏ/Y = Ȧ/A + ε_K * K̇/K + ε_L * L̇/L`, where the
elasticities are `ε_K = K * F_K / F` and `ε_L = L * F_L / F`. Factor shares
equal the elasticities ONLY under additional premises, kept explicit here:
competitive pricing (factor prices `A * F' (1, 0)` and `A * F' (0, 1)`) and
constant returns, stated as the Euler equation. Neither premise is proved.

## Main results

* `growthAccounting`: the growth-accounting identity.
* `competitiveShare_capital_eq_elasticity`,
  `competitiveShare_labour_eq_elasticity`: shares equal elasticities under
  competitive pricing.
* `competitiveShares_sum_eq_one`: shares sum to 1 under competitive pricing plus the Euler equation.

## References

* R. M. Solow, "Technical change and the aggregate production function",
  *Review of Economics and Statistics* 39 (1957).

Atlas roadmap target MA03.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SolowGrowthAccounting

/-- Output elasticity of the production function `F` with respect to capital:
`K * F_K / F`, where `F_K = F' (1, 0)` is the partial derivative of `F` in its
first argument (source clause: "capital elasticity"). -/
noncomputable def capitalElasticity (F : ℝ × ℝ → ℝ) (F' : ℝ × ℝ →L[ℝ] ℝ)
    (K L : ℝ) : ℝ :=
  K * F' (1, 0) / F (K, L)

/-- Output elasticity of the production function `F` with respect to labour:
`L * F_L / F`, where `F_L = F' (0, 1)` is the partial derivative of `F` in its
second argument (source clause: "labour elasticity"). -/
noncomputable def labourElasticity (F : ℝ × ℝ → ℝ) (F' : ℝ × ℝ →L[ℝ] ℝ)
    (K L : ℝ) : ℝ :=
  L * F' (0, 1) / F (K, L)

/-- **Growth accounting.** For `Y = A * F(K, L)` with all paths differentiable at
`t` and `F` differentiable at `(K t, L t)`, the growth rate of output is TFP
growth plus the elasticity-weighted growth rates of capital and labour
(Atlas roadmap MA03.T04). Growth rates are `deriv f t / f t`, i.e. derivatives
of `Real.log ∘ f` by `HasDerivAt.log`. -/
theorem growthAccounting {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ}
    {A K L Y : ℝ → ℝ} {t : ℝ}
    (hY : ∀ s, Y s = A s * F (K s, L s))
    {A' K' L' : ℝ}
    (hA : HasDerivAt A A' t) (hK : HasDerivAt K K' t) (hL : HasDerivAt L L' t)
    (hF : HasFDerivAt F F' (K t, L t))
    (hA0 : A t ≠ 0) (hK0 : K t ≠ 0) (hL0 : L t ≠ 0)
    (hF0 : F (K t, L t) ≠ 0) :
    deriv Y t / Y t = deriv A t / A t +
      capitalElasticity F F' (K t) (L t) * (deriv K t / K t) +
      labourElasticity F F' (K t) (L t) * (deriv L t / L t) := by
  -- Growth rates `deriv f t / f t` are derivatives of `Real.log ∘ f`
  -- (required reuse of `HasDerivAt.log`).
  have _hlogA := hA.log hA0
  have _hlogK := hK.log hK0
  have _hlogL := hL.log hL0
  have hYfun : Y = fun s => A s * F (K s, L s) := funext hY
  have hKL : HasDerivAt (fun s => (K s, L s)) (K', L') t := hK.prodMk hL
  have hFcomp : HasDerivAt (fun s => F (K s, L s)) (F' (K', L')) t :=
    hF.comp_hasDerivAt t hKL
  have hYderiv : HasDerivAt Y (A' * F (K t, L t) + A t * F' (K', L')) t := by
    rw [hYfun]
    exact hA.mul hFcomp
  have hderivY : deriv Y t = A' * F (K t, L t) + A t * F' (K', L') :=
    hYderiv.differentiableAt.hasDerivAt.unique hYderiv
  have hderivA : deriv A t = A' := hA.differentiableAt.hasDerivAt.unique hA
  have hderivK : deriv K t = K' := hK.differentiableAt.hasDerivAt.unique hK
  have hderivL : deriv L t = L' := hL.differentiableAt.hasDerivAt.unique hL
  have hdecomp : (K', L') = K' • ((1 : ℝ), (0 : ℝ)) + L' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp [smul_eq_mul]
  have hlin : F' (K', L') = K' * F' (1, 0) + L' * F' (0, 1) := by
    rw [hdecomp]
    simp only [map_add, map_smul, smul_eq_mul]
  have hYt : Y t = A t * F (K t, L t) := hY t
  have hden : A t * F (K t, L t) ≠ 0 := mul_ne_zero hA0 hF0
  rw [hderivY, hderivA, hderivK, hderivL, hlin, hYt]
  unfold capitalElasticity labourElasticity
  field_simp
  try ring

/-- **Capital share = capital elasticity under competitive pricing.** If capital
is paid its marginal product, the capital price is `A * F' (1, 0)` (this is an
explicit expression in the statement, NOT a proved claim about markets), then
the capital income share `(price * K) / Y` equals the capital elasticity. -/
theorem competitiveShare_capital_eq_elasticity {F : ℝ × ℝ → ℝ}
    {F' : ℝ × ℝ →L[ℝ] ℝ} {A K L Y : ℝ}
    (hY : Y = A * F (K, L))
    (hA0 : A ≠ 0) (hF0 : F (K, L) ≠ 0) :
    (A * F' (1, 0)) * K / Y = capitalElasticity F F' K L := by
  have hden : A * F (K, L) ≠ 0 := mul_ne_zero hA0 hF0
  rw [hY]
  unfold capitalElasticity
  field_simp
  try ring

/-- **Labour share = labour elasticity under competitive pricing.** If labour is
paid its marginal product, the wage is `A * F' (0, 1)` (explicit expression,
NOT a proved claim), then the labour income share equals the labour
elasticity. -/
theorem competitiveShare_labour_eq_elasticity {F : ℝ × ℝ → ℝ}
    {F' : ℝ × ℝ →L[ℝ] ℝ} {A K L Y : ℝ}
    (hY : Y = A * F (K, L))
    (hA0 : A ≠ 0) (hF0 : F (K, L) ≠ 0) :
    (A * F' (0, 1)) * L / Y = labourElasticity F F' K L := by
  have hden : A * F (K, L) ≠ 0 := mul_ne_zero hA0 hF0
  rw [hY]
  unfold labourElasticity
  field_simp
  try ring

/-- **Competitive shares sum to one.** Under competitive pricing (factor prices
`A * F' (1, 0)` and `A * F' (0, 1)`) AND constant returns, stated as the Euler
equation `hEuler` (an explicit hypothesis, NOT proved here), the two factor
shares sum to 1. -/
theorem competitiveShares_sum_eq_one {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ}
    {A K L Y : ℝ}
    (hY : Y = A * F (K, L))
    (hEuler : F (K, L) = K * F' (1, 0) + L * F' (0, 1))
    (hA0 : A ≠ 0) (hF0 : F (K, L) ≠ 0) :
    (A * F' (1, 0)) * K / Y + (A * F' (0, 1)) * L / Y = 1 := by
  have hY0 : Y ≠ 0 := by rw [hY]; exact mul_ne_zero hA0 hF0
  rw [← add_div, div_eq_iff hY0, hY, hEuler]
  ring

end MathlibExt.Economics.Macro.SolowGrowthAccounting