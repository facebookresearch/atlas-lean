/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 15, inverse series

The branch `u < 1` of `u - log u = 1 + x ^ 2 / 2` as a convergent power series near `x = 0`, from
B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15InverseSeries

open Filter Topology

private noncomputable def hfun (t : ℝ) : ℝ := t - Real.log (1 + t)

private theorem hfun_id2 : iteratedDeriv 2 hfun 0 = 1 := by
  have hev : deriv hfun =ᶠ[𝓝 0] fun t => 1 - (1+t)⁻¹ := by
    have hmem : Set.Ioi (-1:ℝ) ∈ 𝓝 (0:ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [hmem] with t ht
    have htne : (1:ℝ) + t ≠ 0 := by intro h; have : (-1:ℝ) < t := ht; linarith
    have h1 : HasDerivAt (fun s : ℝ => (1:ℝ)+s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    have hl0 := (Real.hasDerivAt_log htne).comp t h1
    have hl : HasDerivAt (fun s : ℝ => Real.log (1+s)) ((1+t)⁻¹) t := by
      convert hl0 using 1 <;> first | rfl | ring
    have hH : HasDerivAt hfun (1 - (1+t)⁻¹) t := by
      have := (hasDerivAt_id t).sub hl; convert this using 1; ext s; simp [hfun]
    exact hH.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  have h1 : HasDerivAt (fun s : ℝ => (1:ℝ)+s) 1
      0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add 1
  have hinv : HasDerivAt (fun t : ℝ => (1+t)⁻¹) (-1) 0 := by
    have := h1.inv (by norm_num : (fun s : ℝ => (1:ℝ)+s) 0 ≠ 0); convert this using 1; norm_num
  have hfin : HasDerivAt (fun t : ℝ => 1 - (1+t)⁻¹) 1 0 := by
    have := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub hinv; convert this using 1; norm_num
  exact hfin.deriv

private theorem hfun_analytic : AnalyticAt ℝ hfun 0 := by unfold hfun; fun_prop (disch := norm_num)

private theorem hfun_deriv0 : HasDerivAt hfun 0 0 := by
  have h1' : HasDerivAt (fun s : ℝ => (1:ℝ)+s) 1
      0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add 1
  have hl0 := (Real.hasDerivAt_log (by norm_num : (1:ℝ)+0 ≠ 0)).comp 0 h1'
  have hl : HasDerivAt (fun s : ℝ => Real.log (1+s)) ((1+(0:ℝ))⁻¹) 0 := by
    convert hl0 using 1 <;> first | rfl | ring
  have := (hasDerivAt_id (0:ℝ)).sub hl
  convert this using 1 <;> first | (ext s; simp [hfun]) | norm_num

private theorem F_props : ∃ F : ℝ → ℝ, AnalyticAt ℝ F 0 ∧ (∀ t, hfun t = t^2 * F t) ∧ F 0 =
    1/2 := by
  obtain ⟨F, hFa, hF2⟩ := hfun_analytic.exists_eq_sum_add_pow_mul 2
  have h0 : iteratedDeriv 0 hfun 0 = 0 := by rw [iteratedDeriv_zero]; simp [hfun]
  have h1 : iteratedDeriv 1 hfun 0 = 0 := by rw [iteratedDeriv_one]; exact hfun_deriv0.deriv
  have hFeq : ∀ t, hfun t = t^2 * F t := by
    intro t
    have ht := hF2 t
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1] at ht
    simpa using ht
  obtain ⟨G, hGa, hG3⟩ := hfun_analytic.exists_eq_sum_add_pow_mul 3
  have hkey : ∀ t : ℝ, t ≠ 0 → F t - 1/2 = t * G t := by
    intro t ht
    have hg := hG3 t
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, hfun_id2,
      smul_eq_mul, mul_zero, mul_one] at hg
    norm_num at hg
    have hf := hFeq t
    rw [hf] at hg
    have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht
    have key : t^2 * (F t - 1/2) = t^2 * (t * G t) := by linear_combination hg
    exact mul_left_cancel₀ ht2 key
  have hc1 : ContinuousAt (fun t => F t - 1/2) 0 := (hFa.continuousAt).sub continuousAt_const
  have hc2 : ContinuousAt (fun t => t * G t) 0 := by have := hGa.continuousAt; fun_prop
  have hev : (fun t => F t - 1/2) =ᶠ[𝓝[≠] 0] (fun t => t * G t) :=
    eventually_nhdsWithin_of_forall (fun t ht => hkey t ht)
  have hlim1 : Tendsto (fun t => F t - 1/2) (𝓝[≠] 0) (𝓝 (F 0 - 1/2)) :=
      hc1.continuousWithinAt.tendsto
  have hlim2 : Tendsto (fun t => t * G t) (𝓝[≠] 0) (𝓝 (0 * G 0)) := hc2.continuousWithinAt.tendsto
  have : F 0 - 1/2 = 0 * G 0 := tendsto_nhds_unique (hlim1.congr' hev) hlim2
  exact ⟨F, hFa, hFeq, by linarith [this]⟩

private theorem Ucascade (U : ℝ → ℝ) (hana : ∀ᶠ x in 𝓝 (0 : ℝ), AnalyticAt ℝ U x)
    (hU0 : U 0 = 1) (hD10 : deriv U 0 = -1)
    (hODE0 : (fun x => deriv U x * (U x - 1)) =ᶠ[𝓝 0] fun x => x * U x) :
    deriv (deriv U) 0 = 2/3 ∧ deriv (deriv (deriv U)) 0 = -1/6
      ∧ deriv (deriv (deriv (deriv U))) 0 = -4/45 := by
  have hAU  : ∀ᶠ x in 𝓝 (0:ℝ), AnalyticAt ℝ U x := hana
  have hAU1 : ∀ᶠ x in 𝓝 (0:ℝ), AnalyticAt ℝ (deriv U) x := hana.mono (fun _ h => h.deriv)
  have hAU2 : ∀ᶠ x in 𝓝 (0:ℝ), AnalyticAt ℝ (deriv (deriv U)) x := hAU1.mono (fun _ h => h.deriv)
  have hAU3 : ∀ᶠ x in 𝓝 (0:ℝ), AnalyticAt ℝ (deriv (deriv (deriv U))) x := hAU2.mono
      (fun _ h => h.deriv)
  have hAU4 : ∀ᶠ x in 𝓝 (0:ℝ), AnalyticAt ℝ (deriv (deriv (deriv (deriv U)))) x := hAU3.mono
      (fun _ h => h.deriv)
  have hODE : (fun x => deriv U x * U x - deriv U x) =ᶠ[𝓝 0] fun x => x * U x := by
    filter_upwards [hODE0] with x h; rw [← h]; ring
  have hL1 : (fun x => deriv (deriv U) x * U x + deriv U x * deriv U x - deriv (deriv U) x)
      =ᶠ[𝓝 0] (fun x => U x + x * deriv U x) := by
    have e1 : deriv (fun x => deriv U x * U x - deriv U x)
        =ᶠ[𝓝 0] (fun x => deriv (deriv U) x * U x + deriv U x * deriv U x - deriv (deriv U) x) := by
      filter_upwards [hAU, hAU1] with x hx hx1
      have d0 : DifferentiableAt ℝ U x := hx.differentiableAt
      have d1 : DifferentiableAt ℝ (deriv U) x := hx1.differentiableAt
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
      try ring
    have e2 : deriv (fun x => x * U x) =ᶠ[𝓝 0] (fun x => U x + x * deriv U x) := by
      filter_upwards [hAU] with x hx
      have d0 : DifferentiableAt ℝ U x := hx.differentiableAt
      rw [deriv_fun_mul (by fun_prop) (by fun_prop)]; simp only [deriv_id'']; try ring
    exact (e1.symm.trans hODE.deriv).trans e2
  have hL2 : (fun x => deriv (deriv (deriv U)) x * U x + 3 * (deriv U x * deriv (deriv U) x)
        - deriv (deriv (deriv U)) x)
      =ᶠ[𝓝 0] (fun x => 2 * deriv U x + x * deriv (deriv U) x) := by
    have e1 : deriv (fun x => deriv (deriv U) x * U x + deriv U x * deriv U x - deriv (deriv U) x)
        =ᶠ[𝓝 0] (fun x => deriv (deriv (deriv U)) x * U x + 3 * (deriv U x * deriv (deriv U) x)
          - deriv (deriv (deriv U)) x) := by
      filter_upwards [hAU, hAU1, hAU2] with x hx hx1 hx2
      have d0 : DifferentiableAt ℝ U x := hx.differentiableAt
      have d1 : DifferentiableAt ℝ (deriv U) x := hx1.differentiableAt
      have d2 : DifferentiableAt ℝ (deriv (deriv U)) x := hx2.differentiableAt
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
        deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
      try ring
    have e2 : deriv (fun x => U x + x * deriv U x)
        =ᶠ[𝓝 0] (fun x => 2 * deriv U x + x * deriv (deriv U) x) := by
      filter_upwards [hAU, hAU1] with x hx hx1
      have d0 : DifferentiableAt ℝ U x := hx.differentiableAt
      have d1 : DifferentiableAt ℝ (deriv U) x := hx1.differentiableAt
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
      simp only [deriv_id'']; try ring
    exact (e1.symm.trans hL1.deriv).trans e2
  have hL3 : (fun x => deriv (deriv (deriv (deriv U))) x * U x + 4 *
      (deriv U x * deriv (deriv (deriv U)) x)
        + 3 * (deriv (deriv U) x * deriv (deriv U) x) - deriv (deriv (deriv (deriv U))) x)
      =ᶠ[𝓝 0] (fun x => 3 * deriv (deriv U) x + x * deriv (deriv (deriv U)) x) := by
    have e1 : deriv (fun x => deriv (deriv (deriv U)) x * U x + 3 * (deriv U x * deriv (deriv U) x)
          - deriv (deriv (deriv U)) x)
        =ᶠ[𝓝 0] (fun x => deriv (deriv (deriv (deriv U))) x * U x + 4 *
            (deriv U x * deriv (deriv (deriv U)) x)
          + 3 * (deriv (deriv U) x * deriv (deriv U) x) - deriv (deriv (deriv (deriv U))) x) := by
      filter_upwards [hAU, hAU1, hAU2, hAU3] with x hx hx1 hx2 hx3
      have d0 : DifferentiableAt ℝ U x := hx.differentiableAt
      have d1 : DifferentiableAt ℝ (deriv U) x := hx1.differentiableAt
      have d2 : DifferentiableAt ℝ (deriv (deriv U)) x := hx2.differentiableAt
      have d3 : DifferentiableAt ℝ (deriv (deriv (deriv U))) x := hx3.differentiableAt
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
        deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const_mul_field,
        deriv_fun_mul (by fun_prop) (by fun_prop)]
      try ring
    have e2 : deriv (fun x => 2 * deriv U x + x * deriv (deriv U) x)
        =ᶠ[𝓝 0] (fun x => 3 * deriv (deriv U) x + x * deriv (deriv (deriv U)) x) := by
      filter_upwards [hAU1, hAU2] with x hx1 hx2
      have d1 : DifferentiableAt ℝ (deriv U) x := hx1.differentiableAt
      have d2 : DifferentiableAt ℝ (deriv (deriv U)) x := hx2.differentiableAt
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const_mul_field,
        deriv_fun_mul (by fun_prop) (by fun_prop)]
      simp only [deriv_id'']; try ring
    exact (e1.symm.trans hL2.deriv).trans e2
  have hL4 : (fun x => deriv (deriv (deriv (deriv (deriv U)))) x * U x
        + 5 * (deriv U x * deriv (deriv (deriv (deriv U))) x)
        + 10 * (deriv (deriv U) x * deriv (deriv (deriv U)) x)
        - deriv (deriv (deriv (deriv (deriv U)))) x)
      =ᶠ[𝓝 0] (fun x => 4 * deriv (deriv (deriv U)) x + x * deriv (deriv (deriv (deriv U))) x) := by
    have e1 : deriv (fun x => deriv (deriv (deriv (deriv U))) x * U x + 4 *
        (deriv U x * deriv (deriv (deriv U)) x)
          + 3 * (deriv (deriv U) x * deriv (deriv U) x) - deriv (deriv (deriv (deriv U))) x)
        =ᶠ[𝓝 0] (fun x => deriv (deriv (deriv (deriv (deriv U)))) x * U x
          + 5 * (deriv U x * deriv (deriv (deriv (deriv U))) x)
          + 10 * (deriv (deriv U) x * deriv (deriv (deriv U)) x)
          - deriv (deriv (deriv (deriv (deriv U)))) x) := by
      filter_upwards [hAU, hAU1, hAU2, hAU3, hAU4] with x hx hx1 hx2 hx3 hx4
      have d0 : DifferentiableAt ℝ U x := hx.differentiableAt
      have d1 : DifferentiableAt ℝ (deriv U) x := hx1.differentiableAt
      have d2 : DifferentiableAt ℝ (deriv (deriv U)) x := hx2.differentiableAt
      have d3 : DifferentiableAt ℝ (deriv (deriv (deriv U))) x := hx3.differentiableAt
      have d4 : DifferentiableAt ℝ (deriv (deriv (deriv (deriv U)))) x := hx4.differentiableAt
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
        deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_const_mul_field, deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_const_mul_field, deriv_fun_mul (by fun_prop) (by fun_prop)]
      try ring
    have e2 : deriv (fun x => 3 * deriv (deriv U) x + x * deriv (deriv (deriv U)) x)
        =ᶠ[𝓝 0] (fun x => 4 * deriv (deriv (deriv U)) x + x * deriv (deriv (deriv (deriv U)))
            x) := by
      filter_upwards [hAU2, hAU3] with x hx2 hx3
      have d2 : DifferentiableAt ℝ (deriv (deriv U)) x := hx2.differentiableAt
      have d3 : DifferentiableAt ℝ (deriv (deriv (deriv U))) x := hx3.differentiableAt
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const_mul_field,
        deriv_fun_mul (by fun_prop) (by fun_prop)]
      simp only [deriv_id'']; try ring
    exact (e1.symm.trans hL3.deriv).trans e2
  have E2 := hL2.eq_of_nhds; rw [hU0, hD10] at E2
  have hD2 : deriv (deriv U) 0 = 2/3 := by nlinarith [E2]
  have E3 := hL3.eq_of_nhds; rw [hU0, hD10, hD2] at E3
  have hD3 : deriv (deriv (deriv U)) 0 = -1/6 := by nlinarith [E3]
  have E4 := hL4.eq_of_nhds; rw [hU0, hD10, hD2, hD3] at E4
  have hD4 : deriv (deriv (deriv (deriv U))) 0 = -4/45 := by nlinarith [E4]
  exact ⟨hD2, hD3, hD4⟩

/-- **Ramanujan's inverse series for $u - \log u$.** There exist a real number $r > 0$ and real
coefficients $b_0, b_1, b_2, \dots$ with $b_0 = 1$, $b_1 = -1$, $b_2 = 1/3$, $b_3 = -1/36$ and
$b_4 = -1/270$ such that the power series $\sum_k b_k x^k$ is summable for every real $x$ with
$|x| < r$, and for every real $x$ with $0 < x < r$ the sum $u$ of this series satisfies
$0 < u < 1$ and $u - \log u = 1 + x^2/2$, and the series $\sum_{j \ge 2} (1 - u)^j / j$ converges
unconditionally to $x^2/2$.

Proves `Wanted` entry `ramanujan_part1_ch3_entry15_inverse_series`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 15, local inverse-series
    clause, printed p. 73 / PDF p. 83.
-/
theorem ramanujan_part1_ch3_entry15_inverse_series :
    ∃ (r : ℝ) (b : ℕ → ℝ),
      0 < r ∧ b 0 = 1 ∧ b 1 = -1 ∧ b 2 = (1 : ℝ) / 3 ∧ b 3 = -(1 : ℝ) / 36 ∧
        b 4 = -(1 : ℝ) / 270 ∧
        (∀ x : ℝ, |x| < r → ∃ u : ℝ, HasSum (fun k : ℕ => b k * x ^ k) u) ∧
        ∀ x : ℝ, 0 < x → x < r → ∀ u : ℝ, HasSum (fun k : ℕ => b k * x ^ k) u →
          0 < u ∧ u < 1 ∧ u - Real.log u = 1 + x ^ 2 / 2 ∧
            HasSum (fun j : ℕ => (1 - u) ^ (j + 2) / (↑(j + 2) : ℝ)) (x ^ 2 / 2) := by
  obtain ⟨F, hFa, hFeq, hF0⟩ := F_props
  set E : ℝ → ℝ := fun u => Real.exp (Real.log (2 * F (u-1)) / 2) with hEdef
  set X : ℝ → ℝ := fun u => -(u-1) * E u with hXdef
  have hsub_ana : AnalyticAt ℝ (fun u:ℝ => u - 1) 1 := by fun_prop
  have h2F_ana : AnalyticAt ℝ (fun u:ℝ => 2 * F (u-1)) 1 :=
    analyticAt_const.mul (hFa.comp_of_eq hsub_ana (by norm_num))
  have hpos1 : (0:ℝ) < 2 * F ((1:ℝ)-1) := by rw [show (1:ℝ)-1 = 0 by ring, hF0]; norm_num
  have hcpos : ContinuousAt (fun u:ℝ => 2 * F (u-1)) 1 :=
    continuousAt_const.mul (hFa.continuousAt.comp_of_eq (by fun_prop) (by norm_num))
  have hposev : ∀ᶠ u in 𝓝 (1:ℝ), 0 < 2 * F (u-1) := continuousAt_const.eventually_lt hcpos hpos1
  have hE1 : E 1 = 1 := by
    simp only [hEdef, show (1:ℝ)-1 = 0 by ring, hF0]; norm_num [Real.log_one, Real.exp_zero]
  have hEana : AnalyticAt ℝ E 1 := by
    rw [hEdef]; exact ((h2F_ana.log hpos1).div_const).rexp'
  have hXana1 : AnalyticAt ℝ X 1 := by
    rw [hXdef]; exact (by fun_prop : AnalyticAt ℝ (fun u:ℝ => -(u-1)) 1).mul hEana
  have hX1 : X 1 = 0 := by simp [hXdef]
  have hXderiv : deriv X 1 = -1 := by
    have hlin : HasDerivAt (fun u:ℝ => -(u-1)) (-1) 1 := ((hasDerivAt_id (1:ℝ)).sub_const 1).neg
    have hmul : HasDerivAt X (-1 * E 1 + -(1-1) * deriv E 1) 1 :=
      hlin.mul hEana.hasStrictDerivAt.hasDerivAt
    rw [hmul.deriv, hE1]; ring
  have hXsq : ∀ᶠ u in 𝓝 (1:ℝ), X u ^ 2 = 2 * (u - Real.log u - 1) := by
    filter_upwards [hposev, eventually_gt_nhds (show (0:ℝ) < 1 by norm_num)] with u hu hu0
    have hls : Real.log (2 * F (u-1)) / 2 + Real.log (2 * F (u-1)) / 2 = Real.log
        (2 * F (u-1)) := by ring
    have hEsq : (E u)^2 = 2 * F (u-1) := by
      simp only [hEdef]; rw [sq, ← Real.exp_add, hls]; exact Real.exp_log hu
    have hh : (u-1) - Real.log u = (u-1)^2 * F (u-1) := by
      have h := hFeq (u-1); simp only [hfun] at h
      rw [show (1:ℝ)+(u-1) = u by ring] at h; linarith [h]
    simp only [hXdef]
    have hexp : (-(u-1) * E u)^2 = (u-1)^2 * (E u)^2 := by ring
    rw [hexp, hEsq]; linear_combination -2 * hh
  -- local inverse
  have hX' : deriv X 1 ≠ 0 := by rw [hXderiv]; norm_num
  have hsX : HasStrictDerivAt X (deriv X 1) 1 := hXana1.hasStrictDerivAt
  set U : ℝ → ℝ := hsX.localInverse X (deriv X 1) 1 hX' with hUdef
  have hUana : AnalyticAt ℝ U 0 := by
    have h := hXana1.analyticAt_localInverse hX'; rw [hX1] at h; exact h
  have hleft : ∀ᶠ x in 𝓝 (1:ℝ), U (X x) = x := hsX.eventually_left_inverse hX'
  have hright : ∀ᶠ x in 𝓝 (0:ℝ), X (U x) = x := by
    have h := hsX.eventually_right_inverse hX'; rwa [hX1] at h
  have hU0 : U 0 = 1 := by have h := hleft.self_of_nhds; rwa [hX1] at h
  have hUderiv : deriv U 0 = -1 := by
    have hto : HasStrictDerivAt U (deriv X 1)⁻¹ (X 1) := hsX.to_localInverse hX'
    rw [hX1] at hto; rw [hto.hasDerivAt.deriv, hXderiv]; norm_num
  have hUtend : Tendsto U (𝓝 0) (𝓝 1) := by
    have h := hUana.continuousAt.tendsto; rw [hU0] at h; exact h
  have hUpos : ∀ᶠ x in 𝓝 (0:ℝ), 0 < U x :=
    hUtend.eventually (eventually_gt_nhds (show (0:ℝ) < 1 by norm_num))
  have hcomp : ∀ᶠ x in 𝓝 (0:ℝ), X (U x) ^ 2 = 2 * (U x - Real.log (U x) - 1) := hUtend.eventually
      hXsq
  have hFE : ∀ᶠ x in 𝓝 (0:ℝ), U x - Real.log (U x) = 1 + x ^ 2 / 2 := by
    filter_upwards [hright, hcomp] with x hr hc; rw [hr] at hc; linarith [hc]
  have hana : ∀ᶠ x in 𝓝 (0:ℝ), AnalyticAt ℝ U x := hUana.eventually_analyticAt
  have hODE0 : (fun x => deriv U x * (U x - 1)) =ᶠ[𝓝 0] fun x => x * U x := by
    filter_upwards [hFE.eventually_nhds, hana, hUpos] with x hFEx hax hpx
    have hdU : HasDerivAt U (deriv U x) x := hax.differentiableAt.hasDerivAt
    have hUne : U x ≠ 0 := ne_of_gt hpx
    have hdlog : HasDerivAt (fun y => Real.log (U y)) ((U x)⁻¹ * deriv U x) x :=
      (Real.hasDerivAt_log hUne).comp x hdU
    have hdLHS : HasDerivAt (fun y => U y - Real.log (U y)) (deriv U x - (U x)⁻¹ * deriv U x) x :=
      hdU.sub hdlog
    have hdRHS : HasDerivAt (fun y:ℝ => 1 + y^2/2) x x := by
      have h := ((hasDerivAt_pow 2 x).div_const 2).const_add 1; convert h using 1; ring
    have key : deriv U x - (U x)⁻¹ * deriv U x = x := by
      have hee : (fun y => U y - Real.log (U y)) =ᶠ[𝓝 x] (fun y => 1 + y ^ 2 / 2) := hFEx
      have h := hee.deriv_eq; rw [hdLHS.deriv, hdRHS.deriv] at h; exact h
    field_simp at key
    linear_combination key
  -- coefficients
  obtain ⟨hd2, hd3, hd4⟩ := Ucascade U hana hU0 hUderiv hODE0
  set b : ℕ → ℝ := fun n => iteratedDeriv n U 0 / (n.factorial : ℝ) with hbdef
  have hb0 : b 0 = 1 := by simp [hbdef, iteratedDeriv_zero, hU0]
  have hb1 : b 1 = -1 := by simp [hbdef, iteratedDeriv_one, hUderiv]
  have hb2 : b 2 = (1:ℝ)/3 := by
    have : iteratedDeriv 2 U 0 = deriv (deriv U) 0 := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    simp only [hbdef, this, hd2]; norm_num [Nat.factorial]
  have hb3 : b 3 = -(1:ℝ)/36 := by
    have : iteratedDeriv 3 U 0 = deriv (deriv (deriv U)) 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    simp only [hbdef, this, hd3]; norm_num [Nat.factorial]
  have hb4 : b 4 = -(1:ℝ)/270 := by
    have : iteratedDeriv 4 U 0 = deriv (deriv (deriv (deriv U))) 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    simp only [hbdef, this, hd4]; norm_num [Nat.factorial]
  -- HasSum
  have hHS : ∀ᶠ x in 𝓝 (0:ℝ), HasSum (fun k => b k * x ^ k) (U x) := by
    have hpq := hUana.hasFPowerSeriesAt
    obtain ⟨rp, hball⟩ := hpq
    have hmem : Metric.eball (0:ℝ) rp ∈ 𝓝 (0:ℝ) := Metric.eball_mem_nhds _ hball.r_pos
    filter_upwards [hmem] with x hx
    have hs := hball.hasSum hx; rw [zero_add] at hs
    convert hs using 2 with n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hbdef]
  -- |1 - U x| < 1 near 0
  have habs' : ∀ᶠ x in 𝓝 (0:ℝ), |1 - U x| < 1 := by
    have hc : ContinuousAt (fun x => |1 - U x|) 0 := by
      have := hUana.continuousAt; fun_prop
    have hval : |1 - U 0| < 1 := by rw [hU0]; norm_num
    exact hc.eventually_lt continuousAt_const hval |>.mono (fun x hx => hx)
  -- u < 1 for x > 0 small
  have hderivneg : ∀ᶠ x in 𝓝 (0:ℝ), deriv U x < 0 := by
    have hcd : ContinuousAt (deriv U) 0 := (hUana.deriv).continuousAt
    have : deriv U 0 < 0 := by rw [hUderiv]; norm_num
    exact hcd.eventually_lt continuousAt_const (by rw [hUderiv]; norm_num) |>.mono (fun x hx => hx)
  -- combine
  have hAll : ∀ᶠ x in 𝓝 (0:ℝ), (HasSum (fun k => b k * x ^ k) (U x)) ∧
      (U x - Real.log (U x) = 1 + x ^ 2 / 2) ∧ (0 < U x) ∧ (|1 - U x| < 1) :=
    (hHS.and (hFE.and (hUpos.and habs')))
  obtain ⟨ε1, hε1pos, hε1⟩ := Metric.eventually_nhds_iff.1 hAll
  -- radius for U<1
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.1 (hderivneg.and hana)
  set r : ℝ := min ε1 δ with hrdef
  have hrpos : 0 < r := lt_min hε1pos hδpos
  refine ⟨r, b, hrpos, hb0, hb1, hb2, hb3, hb4, ?_, ?_⟩
  · intro x hx
    have hxε : dist x 0 < ε1 := by
      rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hx (min_le_left _ _)
    exact ⟨U x, (hε1 hxε).1⟩
  · intro x hx0 hxr u hu
    have hxε : dist x 0 < ε1 := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]; exact lt_of_lt_of_le hxr (min_le_left _ _)
    obtain ⟨hHSx, hFEx, hposx, habsx⟩ := hε1 hxε
    have hueq : u = U x := hu.unique hHSx
    subst hueq
    refine ⟨hposx, ?_, hFEx, ?_⟩
    · -- U x < 1 via strict antitone
      have hballδ : ∀ y, dist y 0 < δ → deriv U y < 0 ∧ AnalyticAt ℝ U y := hδ
      have hcont : ContinuousOn U (Set.Ioo (-δ) δ) := by
        apply ContinuousOn.mono (s := Set.Ioo (-δ) δ)
        · intro y hy
          have : dist y 0 < δ := by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨hy.1, hy.2⟩
          exact (hballδ y this).2.continuousAt.continuousWithinAt
        · exact le_refl _
      have hderiv : ∀ y ∈ interior (Set.Ioo (-δ) δ), deriv U y < 0 := by
        rw [interior_Ioo]; intro y hy
        have : dist y 0 < δ := by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨hy.1, hy.2⟩
        exact (hballδ y this).1
      have hanti : StrictAntiOn U (Set.Ioo (-δ) δ) :=
        strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont hderiv
      have h0mem : (0:ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδpos⟩
      have hxmem : x ∈ Set.Ioo (-δ) δ := ⟨by linarith, lt_of_lt_of_le hxr (min_le_right _ _)⟩
      have := hanti h0mem hxmem hx0
      rw [hU0] at this; exact this
    · -- log series
      have hlem := Real.hasSum_pow_div_log_of_abs_lt_one habsx
      rw [show (1:ℝ) - (1 - U x) = U x by ring] at hlem
      have hval : -Real.log (U x) = x^2/2 + (1 - U x) := by
        have h : Real.log (U x) = U x - 1 - x^2/2 := by linarith [hFEx]
        rw [h]; ring
      rw [hval] at hlem
      set f : ℕ → ℝ := fun n => (1 - U x)^(n+1)/((n:ℝ)+1) with hf
      have hf0 : (∑ i ∈ Finset.range 1, f i) = 1 - U x := by simp [hf]
      have hshift : HasSum (fun n => f (n+1)) (x^2/2) := by
        rw [hasSum_nat_add_iff 1, hf0]; exact hlem
      convert hshift using 2 with j
      push_cast [hf]; ring_nf

end Entry15InverseSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
