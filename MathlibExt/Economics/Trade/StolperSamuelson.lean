/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open scoped Topology

/-!
# Local Stolper–Samuelson theorem in the smooth 2×2 model

Two goods are produced from labor and capital with minimum unit-cost functions
`c₁, c₂` of factor prices `x = (w, r)`. Goods prices `p = (p₁, p₂)` determine
factor prices `f p` through both zero-profit conditions `cᵢ (f p) = pᵢ`
(locally diversified production).

Shephard's lemma is proved by the envelope argument: if the unit bundle
`(aL, aK)` is cost-minimizing at `x₀`, its cost bounds the minimum unit cost
from above near `x₀`, with equality at `x₀`, so a differentiable unit cost has
derivative `(aL, aK)` there (`IsCostMinimizingAt.hasFDerivAt`).

Differentiating the zero-profit conditions then gives the local
Stolper–Samuelson comparative statics with Jones' magnification effect: if good
1 is labor-intensive at `p₀` (`aL₂ / aK₂ < aL₁ / aK₁`, no intensity reversal),
then a rise in `p₁` raises the wage more than proportionally and lowers the
rental rate, and a rise in `p₂` raises the rental rate more than
proportionally and lowers the wage.

The results are local and assume both goods are produced. Not covered: global
statements, existence of the factor-price map, complete specialization,
terms-of-trade effects, or Rybczynski output responses.

## Main results

* `MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt.hasFDerivAt`
* `MathlibExt.Economics.StolperSamuelson.wage_magnified_rental_falls`
* `MathlibExt.Economics.StolperSamuelson.rental_magnified_wage_falls`

## References

* W. F. Stolper and P. A. Samuelson, "Protection and Real Wages",
  Review of Economic Studies 9 (1941), 58–73.
* R. W. Jones, "The Structure of Simple General Equilibrium Models",
  Journal of Political Economy 73 (1965), 557–572.

Atlas roadmap target AP01.T03.
-/

namespace MathlibExt.Economics.StolperSamuelson

/-- Unit-cost minimization at factor prices `x₀ = (w₀, r₀)`: `c` is the minimum
cost of producing one unit at factor prices `x = (w, r)`, and the unit input
bundle `(aL, aK)` (labor, capital) is cost-minimizing at `x₀`. Since that bundle
stays feasible, its cost `w aL + r aK` bounds `c x` from above near `x₀`, with
equality at `x₀`. -/
structure IsCostMinimizingAt (c : ℝ × ℝ → ℝ) (aL aK : ℝ) (x₀ : ℝ × ℝ) : Prop where
  le_bundle_cost : ∀ᶠ x in 𝓝 x₀, c x ≤ x.1 * aL + x.2 * aK
  eq_bundle_cost : c x₀ = x₀.1 * aL + x₀.2 * aK

/-- Shephard's lemma (envelope argument): a differentiable minimum unit cost has
derivative equal to the cost-minimizing unit input bundle, `∂c/∂w = aL`,
`∂c/∂r = aK`. -/
theorem IsCostMinimizingAt.hasFDerivAt {c : ℝ × ℝ → ℝ} {aL aK : ℝ} {x₀ : ℝ × ℝ}
    (h : IsCostMinimizingAt c aL aK x₀) (hc : DifferentiableAt ℝ c x₀) :
    HasFDerivAt c (aL • ContinuousLinearMap.fst ℝ ℝ ℝ + aK • ContinuousLinearMap.snd ℝ ℝ ℝ)
      x₀ := by
  have hL : HasFDerivAt (fun x : ℝ × ℝ => x.1 * aL + x.2 * aK)
      (aL • ContinuousLinearMap.fst ℝ ℝ ℝ + aK • ContinuousLinearMap.snd ℝ ℝ ℝ) x₀ :=
    (hasFDerivAt_fst.mul_const aL).add (hasFDerivAt_snd.mul_const aK)
  have hg : HasFDerivAt (fun x : ℝ × ℝ => x.1 * aL + x.2 * aK - c x)
      ((aL • ContinuousLinearMap.fst ℝ ℝ ℝ + aK • ContinuousLinearMap.snd ℝ ℝ ℝ) -
        fderiv ℝ c x₀) x₀ :=
    hL.sub hc.hasFDerivAt
  have h0 : x₀.1 * aL + x₀.2 * aK - c x₀ = 0 := by
    rw [h.eq_bundle_cost, sub_self]
  have hmin : IsLocalMin (fun x : ℝ × ℝ => x.1 * aL + x.2 * aK - c x) x₀ := by
    change ∀ᶠ x in 𝓝 x₀, x₀.1 * aL + x₀.2 * aK - c x₀ ≤ x.1 * aL + x.2 * aK - c x
    filter_upwards [h.le_bundle_cost] with x hx
    rw [h0]
    linarith
  have hzero := hmin.hasFDerivAt_eq_zero hg
  have heq : fderiv ℝ c x₀ =
      aL • ContinuousLinearMap.fst ℝ ℝ ℝ + aK • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (sub_eq_zero.mp hzero).symm
  rw [← heq]
  exact hc.hasFDerivAt

/-- Stolper–Samuelson, response to the price of the labor-intensive good 1.
Goods prices `p = (p₁, p₂)` determine factor prices `f p = (w, r)` through both
zero-profit conditions `c₁ (f p) = p₁`, `c₂ (f p) = p₂` near `p₀` (locally
diversified production). If good 1 is labor-intensive at `p₀`
(`aL₂ / aK₂ < aL₁ / aK₁`, no intensity reversal), then the wage rises more than
proportionally (`(p₁ / w) ∂w/∂p₁ > 1`) and the rental rate falls
(`∂r/∂p₁ < 0`). -/
theorem wage_magnified_rental_falls {c₁ c₂ : ℝ × ℝ → ℝ} {aL₁ aK₁ aL₂ aK₂ : ℝ}
    {f : ℝ × ℝ → ℝ × ℝ} {p₀ : ℝ × ℝ}
    (h₁ : IsCostMinimizingAt c₁ aL₁ aK₁ (f p₀)) (h₂ : IsCostMinimizingAt c₂ aL₂ aK₂ (f p₀))
    (hc₁ : DifferentiableAt ℝ c₁ (f p₀)) (hc₂ : DifferentiableAt ℝ c₂ (f p₀))
    (hf : DifferentiableAt ℝ f p₀)
    (hzero : ∀ᶠ p in 𝓝 p₀, c₁ (f p) = p.1 ∧ c₂ (f p) = p.2)
    (hw : 0 < (f p₀).1) (hr : 0 < (f p₀).2)
    (haK₁ : 0 < aK₁) (haL₂ : 0 < aL₂) (haK₂ : 0 < aK₂)
    (hint : aL₂ * aK₁ < aL₁ * aK₂) :
    (f p₀).1 < p₀.1 * (fderiv ℝ f p₀ (1, 0)).1 ∧ (fderiv ℝ f p₀ (1, 0)).2 < 0 := by
  have hS1 : fderiv ℝ c₁ (f p₀) =
      aL₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + aK₁ • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (h₁.hasFDerivAt hc₁).fderiv
  have hS2 : fderiv ℝ c₂ (f p₀) =
      aL₂ • ContinuousLinearMap.fst ℝ ℝ ℝ + aK₂ • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (h₂.hasFDerivAt hc₂).fderiv
  have hcomp1 : HasFDerivAt (fun p : ℝ × ℝ => c₁ (f p))
      ((fderiv ℝ c₁ (f p₀)).comp (fderiv ℝ f p₀)) p₀ :=
    HasFDerivAt.comp p₀ hc₁.hasFDerivAt hf.hasFDerivAt
  have hcomp2 : HasFDerivAt (fun p : ℝ × ℝ => c₂ (f p))
      ((fderiv ℝ c₂ (f p₀)).comp (fderiv ℝ f p₀)) p₀ :=
    HasFDerivAt.comp p₀ hc₂.hasFDerivAt hf.hasFDerivAt
  have heq1 : (fun p : ℝ × ℝ => c₁ (f p)) =ᶠ[𝓝 p₀] Prod.fst :=
    hzero.mono fun p hp => hp.1
  have heq2 : (fun p : ℝ × ℝ => c₂ (f p)) =ᶠ[𝓝 p₀] Prod.snd :=
    hzero.mono fun p hp => hp.2
  have hderiv1 : HasFDerivAt (fun p : ℝ × ℝ => c₁ (f p))
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p₀ :=
    hasFDerivAt_fst.congr_of_eventuallyEq heq1
  have hderiv2 : HasFDerivAt (fun p : ℝ × ℝ => c₂ (f p))
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p₀ :=
    hasFDerivAt_snd.congr_of_eventuallyEq heq2
  have hCLM1 : (fderiv ℝ c₁ (f p₀)).comp (fderiv ℝ f p₀) =
      ContinuousLinearMap.fst ℝ ℝ ℝ :=
    hcomp1.fderiv.symm.trans hderiv1.fderiv
  have hCLM2 : (fderiv ℝ c₂ (f p₀)).comp (fderiv ℝ f p₀) =
      ContinuousLinearMap.snd ℝ ℝ ℝ :=
    hcomp2.fderiv.symm.trans hderiv2.fderiv
  rw [hS1] at hCLM1
  rw [hS2] at hCLM2
  have app1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hCLM1
  have app2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hCLM2
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, smul_eq_mul] at app1 app2
  have eq1 : aL₁ * (fderiv ℝ f p₀ (1, 0)).1 + aK₁ * (fderiv ℝ f p₀ (1, 0)).2 = 1 := app1
  have eq2 : aL₂ * (fderiv ℝ f p₀ (1, 0)).1 + aK₂ * (fderiv ℝ f p₀ (1, 0)).2 = 0 := app2
  have hD : 0 < aL₁ * aK₂ - aL₂ * aK₁ := sub_pos.mpr hint
  have hp0 := hzero.self_of_nhds
  have hp1 : p₀.1 = (f p₀).1 * aL₁ + (f p₀).2 * aK₁ := by
    rw [← hp0.1, h₁.eq_bundle_cost]
  have hp2 : p₀.2 = (f p₀).1 * aL₂ + (f p₀).2 * aK₂ := by
    rw [← hp0.2, h₂.eq_bundle_cost]
  have hDdw : (aL₁ * aK₂ - aL₂ * aK₁) * (fderiv ℝ f p₀ (1, 0)).1 = aK₂ := by
    linear_combination aK₂ * eq1 - aK₁ * eq2
  have hDdr : (aL₁ * aK₂ - aL₂ * aK₁) * (fderiv ℝ f p₀ (1, 0)).2 = -aL₂ := by
    linear_combination -aL₂ * eq1 + aL₁ * eq2
  have hDX : (aL₁ * aK₂ - aL₂ * aK₁) *
      (p₀.1 * (fderiv ℝ f p₀ (1, 0)).1 - (f p₀).1) = aK₁ * p₀.2 := by
    linear_combination p₀.1 * hDdw + aK₂ * hp1 - aK₁ * hp2
  have hp2pos : 0 < p₀.2 := by
    rw [hp2]
    exact add_pos (mul_pos hw haL₂) (mul_pos hr haK₂)
  have hP : 0 < aK₁ * p₀.2 := mul_pos haK₁ hp2pos
  have hmag : 0 < p₀.1 * (fderiv ℝ f p₀ (1, 0)).1 - (f p₀).1 := by
    by_contra hcon
    replace hcon := le_of_not_gt hcon
    have hle : (aL₁ * aK₂ - aL₂ * aK₁) *
        (p₀.1 * (fderiv ℝ f p₀ (1, 0)).1 - (f p₀).1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD) hcon
    rw [hDX] at hle
    linarith
  have hfall : (fderiv ℝ f p₀ (1, 0)).2 < 0 := by
    by_contra hcon
    replace hcon := le_of_not_gt hcon
    have hle : 0 ≤ (aL₁ * aK₂ - aL₂ * aK₁) * (fderiv ℝ f p₀ (1, 0)).2 :=
      mul_nonneg (le_of_lt hD) hcon
    rw [hDdr] at hle
    have : 0 < aL₂ := haL₂
    linarith
  exact ⟨by linarith, hfall⟩

/-- Stolper–Samuelson, response to the price of the capital-intensive good 2:
the rental rate rises more than proportionally (`(p₂ / r) ∂r/∂p₂ > 1`) and the
wage falls (`∂w/∂p₂ < 0`). Same hypotheses as `wage_magnified_rental_falls`. -/
theorem rental_magnified_wage_falls {c₁ c₂ : ℝ × ℝ → ℝ} {aL₁ aK₁ aL₂ aK₂ : ℝ}
    {f : ℝ × ℝ → ℝ × ℝ} {p₀ : ℝ × ℝ}
    (h₁ : IsCostMinimizingAt c₁ aL₁ aK₁ (f p₀)) (h₂ : IsCostMinimizingAt c₂ aL₂ aK₂ (f p₀))
    (hc₁ : DifferentiableAt ℝ c₁ (f p₀)) (hc₂ : DifferentiableAt ℝ c₂ (f p₀))
    (hf : DifferentiableAt ℝ f p₀)
    (hzero : ∀ᶠ p in 𝓝 p₀, c₁ (f p) = p.1 ∧ c₂ (f p) = p.2)
    (hw : 0 < (f p₀).1) (hr : 0 < (f p₀).2)
    (haK₁ : 0 < aK₁) (haL₂ : 0 < aL₂) (haK₂ : 0 < aK₂)
    (hint : aL₂ * aK₁ < aL₁ * aK₂) :
    (f p₀).2 < p₀.2 * (fderiv ℝ f p₀ (0, 1)).2 ∧ (fderiv ℝ f p₀ (0, 1)).1 < 0 := by
  have hS1 : fderiv ℝ c₁ (f p₀) =
      aL₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + aK₁ • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (h₁.hasFDerivAt hc₁).fderiv
  have hS2 : fderiv ℝ c₂ (f p₀) =
      aL₂ • ContinuousLinearMap.fst ℝ ℝ ℝ + aK₂ • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (h₂.hasFDerivAt hc₂).fderiv
  have hcomp1 : HasFDerivAt (fun p : ℝ × ℝ => c₁ (f p))
      ((fderiv ℝ c₁ (f p₀)).comp (fderiv ℝ f p₀)) p₀ :=
    HasFDerivAt.comp p₀ hc₁.hasFDerivAt hf.hasFDerivAt
  have hcomp2 : HasFDerivAt (fun p : ℝ × ℝ => c₂ (f p))
      ((fderiv ℝ c₂ (f p₀)).comp (fderiv ℝ f p₀)) p₀ :=
    HasFDerivAt.comp p₀ hc₂.hasFDerivAt hf.hasFDerivAt
  have heq1 : (fun p : ℝ × ℝ => c₁ (f p)) =ᶠ[𝓝 p₀] Prod.fst :=
    hzero.mono fun p hp => hp.1
  have heq2 : (fun p : ℝ × ℝ => c₂ (f p)) =ᶠ[𝓝 p₀] Prod.snd :=
    hzero.mono fun p hp => hp.2
  have hderiv1 : HasFDerivAt (fun p : ℝ × ℝ => c₁ (f p))
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p₀ :=
    hasFDerivAt_fst.congr_of_eventuallyEq heq1
  have hderiv2 : HasFDerivAt (fun p : ℝ × ℝ => c₂ (f p))
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p₀ :=
    hasFDerivAt_snd.congr_of_eventuallyEq heq2
  have hCLM1 : (fderiv ℝ c₁ (f p₀)).comp (fderiv ℝ f p₀) =
      ContinuousLinearMap.fst ℝ ℝ ℝ :=
    hcomp1.fderiv.symm.trans hderiv1.fderiv
  have hCLM2 : (fderiv ℝ c₂ (f p₀)).comp (fderiv ℝ f p₀) =
      ContinuousLinearMap.snd ℝ ℝ ℝ :=
    hcomp2.fderiv.symm.trans hderiv2.fderiv
  rw [hS1] at hCLM1
  rw [hS2] at hCLM2
  have app1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hCLM1
  have app2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hCLM2
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, smul_eq_mul] at app1 app2
  have eq1 : aL₁ * (fderiv ℝ f p₀ (0, 1)).1 + aK₁ * (fderiv ℝ f p₀ (0, 1)).2 = 0 := app1
  have eq2 : aL₂ * (fderiv ℝ f p₀ (0, 1)).1 + aK₂ * (fderiv ℝ f p₀ (0, 1)).2 = 1 := app2
  have hD : 0 < aL₁ * aK₂ - aL₂ * aK₁ := sub_pos.mpr hint
  have hp0 := hzero.self_of_nhds
  have hp1 : p₀.1 = (f p₀).1 * aL₁ + (f p₀).2 * aK₁ := by
    rw [← hp0.1, h₁.eq_bundle_cost]
  have hp2 : p₀.2 = (f p₀).1 * aL₂ + (f p₀).2 * aK₂ := by
    rw [← hp0.2, h₂.eq_bundle_cost]
  have haL₁ : 0 < aL₁ := by
    have hpos : 0 < aL₁ * aK₂ :=
      lt_of_le_of_lt (le_of_lt (mul_pos haL₂ haK₁)) hint
    have hpos' : 0 < aK₂ * aL₁ := by
      rw [mul_comm]
      exact hpos
    exact pos_of_mul_pos_right hpos' (le_of_lt haK₂)
  have hDdw : (aL₁ * aK₂ - aL₂ * aK₁) * (fderiv ℝ f p₀ (0, 1)).1 = -aK₁ := by
    linear_combination aK₂ * eq1 - aK₁ * eq2
  have hDdr : (aL₁ * aK₂ - aL₂ * aK₁) * (fderiv ℝ f p₀ (0, 1)).2 = aL₁ := by
    linear_combination -aL₂ * eq1 + aL₁ * eq2
  have hDX : (aL₁ * aK₂ - aL₂ * aK₁) *
      (p₀.2 * (fderiv ℝ f p₀ (0, 1)).2 - (f p₀).2) = aL₂ * p₀.1 := by
    linear_combination p₀.2 * hDdr + aL₁ * hp2 - aL₂ * hp1
  have hp1pos : 0 < p₀.1 := by
    rw [hp1]
    exact add_pos (mul_pos hw haL₁) (mul_pos hr haK₁)
  have hP : 0 < aL₂ * p₀.1 := mul_pos haL₂ hp1pos
  have hmag : 0 < p₀.2 * (fderiv ℝ f p₀ (0, 1)).2 - (f p₀).2 := by
    by_contra hcon
    replace hcon := le_of_not_gt hcon
    have hle : (aL₁ * aK₂ - aL₂ * aK₁) *
        (p₀.2 * (fderiv ℝ f p₀ (0, 1)).2 - (f p₀).2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD) hcon
    rw [hDX] at hle
    linarith
  have hfall : (fderiv ℝ f p₀ (0, 1)).1 < 0 := by
    by_contra hcon
    replace hcon := le_of_not_gt hcon
    have hle : 0 ≤ (aL₁ * aK₂ - aL₂ * aK₁) * (fderiv ℝ f p₀ (0, 1)).1 :=
      mul_nonneg (le_of_lt hD) hcon
    rw [hDdw] at hle
    have : 0 < aK₁ := haK₁
    linarith
  exact ⟨by linarith, hfall⟩

end MathlibExt.Economics.StolperSamuelson
