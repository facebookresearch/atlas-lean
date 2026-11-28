/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.WrightFisher
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Selection monotonicity of Kimura's fixation formula

Kimura's fixation probability `kimuraFixation σ x` is the probability that an allele at
initial frequency `x ∈ [0, 1]` is eventually fixed, with scaled genic selection coefficient
`σ = 2Ns` for a diploid population of `N` individuals and time in units of `2N` generations:
`(1 - e^{-2σx}) / (1 - e^{-2σ})` for `σ ≠ 0`, and `x` in the neutral case (M. Kimura, *On the
probability of fixation of mutant genes in a population*, Genetics 47 (1962) 713–719). The
formula is defined and studied in `WrightFisher`; the statements below are derived facts about
that formula in the repository scaling — allele-label symmetry, the deleterious comparison,
strict increase in the selection coefficient, and the first neutral perturbation
coefficient — rather than quotations from the 1962 paper. These are formula-level statements
only; no stochastic process is mentioned.

## Main results

* `kimuraFixation_neg`: `kimuraFixation σ x = 1 - kimuraFixation (-σ) (1 - x)`.
* `kimuraFixation_lt`: `kimuraFixation σ x < x` for `σ < 0` and `x ∈ (0, 1)`.
* `strictMono_kimuraFixation_in_sigma`: `σ ↦ kimuraFixation σ x` is strictly monotone for
  `x ∈ (0, 1)`.
* `hasDerivAt_kimuraFixation_sigma_zero`: `σ ↦ kimuraFixation σ x` has derivative `x (1 - x)`
  at `σ = 0` for `x ∈ [0, 1]`.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a population*,
  Genetics 47 (1962), 713–719.
-/

@[expose] public section

open Set MathlibExt.Biology.PopulationGenetics.Diffusion

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

-- Neutral perturbation at interior frequencies: the slope of `σ ↦ kimuraFixation σ x`
-- at `σ = 0` is a `0/0` limit, resolved by one mean-value step and first-order limits.
private theorem hasDerivAt_kimuraFixation_sigma_zero_aux {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun σ => kimuraFixation σ x) (x * (1 - x)) 0 := by
  have hE1 : ∀ t : ℝ, HasDerivAt (fun σ => Real.exp (-2*σ*x))
      (Real.exp (-2*t*x)*(-2*x)) t := by
    intro t
    have hinner1 : HasDerivAt (fun σ : ℝ => -2*σ*x) (-2*x) t := by
      simpa using ((hasDerivAt_id t).const_mul (-2)).mul_const x
    exact hinner1.exp
  have hE2 : ∀ t : ℝ, HasDerivAt (fun σ => Real.exp (-2*σ)) (Real.exp (-2*t)*(-2)) t := by
    intro t
    have hinner2 : HasDerivAt (fun σ : ℝ => -2*σ) (-2) t := by
      simpa using (hasDerivAt_id t).const_mul (-2)
    exact hinner2.exp
  have hN : ∀ t : ℝ, HasDerivAt (fun σ => 1 - Real.exp (-2*σ*x))
      (0 - Real.exp (-2*t*x)*(-2*x)) t :=
    fun t => (hasDerivAt_const _ _).sub (hE1 t)
  have hD : ∀ t : ℝ, HasDerivAt (fun σ => 1 - Real.exp (-2*σ)) (0 - Real.exp (-2*t)*(-2)) t :=
    fun t => (hasDerivAt_const _ _).sub (hE2 t)
  have hF : ∀ t : ℝ, HasDerivAt (fun σ => (1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ)))
      ((0 - Real.exp (-2*t*x)*(-2*x)) - x*(0 - Real.exp (-2*t)*(-2))) t :=
    fun t => (hN t).sub ((hD t).const_mul x)
  have hG : ∀ t : ℝ, HasDerivAt (fun σ => σ * (1 - Real.exp (-2*σ)))
      (1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2))) t :=
    fun t => (hasDerivAt_id' t).mul (hD t)
  have hF0 : (1 - Real.exp (-2*(0:ℝ)*x)) - x*(1 - Real.exp (-2*(0:ℝ))) = 0 := by simp
  have hG0 : (0:ℝ) * (1 - Real.exp (-2*(0:ℝ))) = 0 := by simp
  have hGne : ∀ t : ℝ, t ≠ 0 → t * (1 - Real.exp (-2*t)) ≠ 0 :=
    fun t ht => mul_ne_zero ht (one_sub_exp_ne_zero ht)
  have hG'ne : ∀ t : ℝ, t ≠ 0 →
      1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2)) ≠ 0 := by
    intro t ht
    have epos : (0:ℝ) < Real.exp (-2*t) := Real.exp_pos _
    have h2e : (0:ℝ) < 0 - Real.exp (-2*t)*(-2) := by linarith
    obtain hneg | hpos := lt_or_gt_of_ne ht
    · have e1 : (1:ℝ) < Real.exp (-2*t) := Real.one_lt_exp_iff.mpr (by linarith)
      have h1 : (1:ℝ) * (1 - Real.exp (-2*t)) < 0 := by linarith
      have h2 : t * (0 - Real.exp (-2*t)*(-2)) < 0 := mul_neg_of_neg_of_pos hneg h2e
      have hsum : 1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2)) < 0 := by
        linarith
      exact ne_of_lt hsum
    · have e1 : Real.exp (-2*t) < (1:ℝ) := Real.exp_lt_one_iff.mpr (by linarith)
      have h1 : (0:ℝ) < 1 * (1 - Real.exp (-2*t)) := by linarith
      have h2 : (0:ℝ) < t * (0 - Real.exp (-2*t)*(-2)) := mul_pos hpos h2e
      have hsum : (0:ℝ) < 1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2)) := by
        linarith
      exact ne_of_gt hsum
  have hP1 := (hE1 0).tendsto_slope_zero
  have hP2 := (hE2 0).tendsto_slope_zero
  have hP3 := (hD 0).tendsto_slope_zero
  have hE2tend : Filter.Tendsto (fun t => Real.exp (-2*t)) (nhds 0)
      (nhds (Real.exp (-2*0))) :=
    (hE2 0).continuousAt
  have hE2lim : Filter.Tendsto (fun t => Real.exp (-2*t)) (nhds 0) (nhds 1) := by
    simpa using hE2tend
  have hE2p : Filter.Tendsto (fun t => Real.exp (-2*t)) (nhdsWithin (0:ℝ) ({0}ᶜ : Set ℝ))
      (nhds 1) :=
    hE2lim.mono_left
      (show nhdsWithin (0:ℝ) ({0}ᶜ : Set ℝ) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hnum := (hP1.sub hP2).const_mul (2*x)
  have hden := hP3.add (hE2p.const_mul 2)
  have hden_ne : (0 - Real.exp (-2*0)*(-2)) + 2*1 ≠ 0 := by
    have e0 : Real.exp (-2*0) = 1 := by
      rw [show (-2:ℝ)*0 = 0 by ring]
      exact Real.exp_zero
    linarith
  have hlim0 := hnum.div hden hden_ne
  have hVAL : ((2*x)*((Real.exp (-2*0*x)*(-2*x)) - (Real.exp (-2*0)*(-2)))) /
      ((0 - Real.exp (-2*0)*(-2)) + 2*1) = x*(1-x) := by
    rw [show (-2:ℝ)*0*x = 0 by ring, show (-2:ℝ)*0 = 0 by ring, Real.exp_zero]
    ring
  rw [hVAL] at hlim0
  have hlim0' : Filter.Tendsto (fun t => ((2*x)*(t⁻¹ • (Real.exp (-2*t*x) - Real.exp (-2*0*x)) -
      t⁻¹ • (Real.exp (-2*t) - Real.exp (-2*0)))) /
      ((t⁻¹ • ((1 - Real.exp (-2*t)) - (1 - Real.exp (-2*0)))) + 2 * Real.exp (-2*t)))
      (nhdsWithin (0:ℝ) ({0}ᶜ : Set ℝ)) (nhds (x*(1-x))) :=
    hlim0.congr' (by filter_upwards with t; simp only [Pi.div_apply, zero_add])
  have hfactor : ∀ t : ℝ, ((0 - Real.exp (-2*t*x)*(-2*x)) - x*(0 - Real.exp (-2*t)*(-2))) /
      (1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2))) =
      ((2*x)*(t⁻¹ • (Real.exp (-2*t*x) - Real.exp (-2*0*x)) -
        t⁻¹ • (Real.exp (-2*t) - Real.exp (-2*0)))) /
      ((t⁻¹ • ((1 - Real.exp (-2*t)) - (1 - Real.exp (-2*0)))) + 2 * Real.exp (-2*t)) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    · simp only [show (-2:ℝ)*0 = 0 by ring, Real.exp_zero,
        sub_self, sub_zero, smul_eq_mul, zero_mul]
      have hGt : 1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2)) ≠ 0 :=
        hG'ne t ht
      have hDen : (t⁻¹ * (1 - Real.exp (-2*t)) + 2 * Real.exp (-2*t)) ≠ 0 := by
        have hlink : (t⁻¹ * (1 - Real.exp (-2*t)) + 2 * Real.exp (-2*t))
            = (1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2))) / t := by
          field_simp
          ring
        rw [hlink]
        exact div_ne_zero hGt ht
      field_simp [ht, hGt, hDen]
      ring
  have hFGlim := hlim0'.congr' (Filter.Eventually.of_forall (fun t => (hfactor t).symm))
  apply hasDerivAt_iff_tendsto_slope.2
  have hslope_eq : ∀ σ : ℝ, slope (fun σ => kimuraFixation σ x) 0 σ =
      (((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) / (σ * (1 - Real.exp (-2*σ)))) := by
    intro σ
    by_cases hσ : σ = 0
    · subst hσ
      simp
    · have hD : (1:ℝ) - Real.exp (-2*σ) ≠ 0 := one_sub_exp_ne_zero hσ
      simp only [slope_def_field, kimuraFixation, hσ, ↓reduceIte, sub_zero]
      set E1 : ℝ := Real.exp (-2*σ*x) with hE1def
      set E2 : ℝ := Real.exp (-2*σ) with hE2def
      have hσD : σ * (1 - E2) ≠ 0 := mul_ne_zero hσ hD
      field_simp [hσ, hD, hσD]
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun σ => (hslope_eq σ).symm)) ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hFGε := (Metric.tendsto_nhds.mp hFGlim) ε hε
  rw [eventually_nhdsWithin_iff] at hFGε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hFGε
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with σ hσball
  rw [Metric.mem_ball] at hσball
  intro hσ0
  have hσ : σ ≠ 0 := by simpa using hσ0
  set ψ : ℝ → ℝ := (fun t => ((1 - Real.exp (-2*t*x)) - x*(1 - Real.exp (-2*t))) *
      (σ * (1 - Real.exp (-2*σ))) -
      ((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) * (t * (1 - Real.exp (-2*t))))
    with hψdef
  have hψderiv : ∀ t : ℝ, HasDerivAt ψ
      ((((0 - Real.exp (-2*t*x)*(-2*x)) - x*(0 - Real.exp (-2*t)*(-2))) *
        (σ * (1 - Real.exp (-2*σ)))) -
        (((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) *
        (1 * (1 - Real.exp (-2*t)) + t * (0 - Real.exp (-2*t)*(-2))))) t :=
    fun t => ((hF t).mul_const _).sub ((hG t).const_mul _)
  have hψσ : ψ σ = 0 := by
    simp only [hψdef]
    ring
  have hψ0 : ψ 0 = 0 := by
    simp only [hψdef, hF0, hG0]
    ring
  obtain hnegσ | hposσ := lt_or_gt_of_ne hσ
  · have hψcont : ContinuousOn ψ (Icc σ 0) :=
      fun t _ => (hψderiv t).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope ψ hnegσ hψcont
      (fun t _ => (hψderiv t).differentiableAt.differentiableWithinAt)
    rw [hψσ, hψ0, sub_self, zero_div, (hψderiv c).deriv] at hcd
    have hc0 : c ≠ 0 := ne_of_lt hc.2
    have hceq : ((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) / (σ * (1 - Real.exp (-2*σ))) =
        (((0 - Real.exp (-2*c*x)*(-2*x)) - x*(0 - Real.exp (-2*c)*(-2))) /
        (1 * (1 - Real.exp (-2*c)) + c * (0 - Real.exp (-2*c)*(-2)))) := by
      rw [div_eq_div_iff (hGne σ hσ) (hG'ne c hc0)]
      linarith
    have hσabs : |σ| < δ := by
      have htmp := hσball
      rwa [Real.dist_eq, sub_zero] at htmp
    have hcabs : |c| < |σ| := by
      rw [abs_of_neg hc.2, abs_of_neg hnegσ]
      linarith [hc.1]
    have hcball : dist c 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      linarith [hcabs, hσabs]
    have htmp := hball (Metric.mem_ball.mpr hcball)
    show dist (((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) /
        (σ * (1 - Real.exp (-2*σ)))) (x*(1-x)) < ε
    rw [hceq]
    exact htmp (by simpa using hc0)
  · have hψcont : ContinuousOn ψ (Icc 0 σ) :=
      fun t _ => (hψderiv t).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope ψ hposσ hψcont
      (fun t _ => (hψderiv t).differentiableAt.differentiableWithinAt)
    rw [hψσ, hψ0, sub_self, zero_div, (hψderiv c).deriv] at hcd
    have hc0 : c ≠ 0 := hc.1.ne'
    have hceq : ((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) / (σ * (1 - Real.exp (-2*σ))) =
        (((0 - Real.exp (-2*c*x)*(-2*x)) - x*(0 - Real.exp (-2*c)*(-2))) /
        (1 * (1 - Real.exp (-2*c)) + c * (0 - Real.exp (-2*c)*(-2)))) := by
      rw [div_eq_div_iff (hGne σ hσ) (hG'ne c hc0)]
      linarith
    have hσabs : |σ| < δ := by
      have htmp := hσball
      rwa [Real.dist_eq, sub_zero] at htmp
    have hcabs : |c| < |σ| := by
      rw [abs_of_pos hc.1, abs_of_pos hposσ]
      exact hc.2
    have hcball : dist c 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      linarith [hcabs, hσabs]
    have htmp := hball (Metric.mem_ball.mpr hcball)
    show dist (((1 - Real.exp (-2*σ*x)) - x*(1 - Real.exp (-2*σ))) /
        (σ * (1 - Real.exp (-2*σ)))) (x*(1-x)) < ε
    rw [hceq]
    exact htmp (by simpa using hc0)

/-- Allele-label symmetry of Kimura's formula, for all real `σ` and `x`: relabeling the two
alleles sends frequency `x` to `1 - x` and selection `σ` to `-σ`; formula level only, a statement
about fixation probabilities for `x ∈ [0, 1]`. -/
theorem kimuraFixation_neg (σ x : ℝ) :
    kimuraFixation σ x = 1 - kimuraFixation (-σ) (1 - x) := by
  by_cases h : σ = 0
  · subst h
    simp only [kimuraFixation_neutral, neg_zero]
    ring
  · have h' : -σ ≠ 0 := neg_ne_zero.2 h
    have e1 : Real.exp (-2 * (-σ) * (1 - x)) = Real.exp (-2 * σ * x) / Real.exp (-2 * σ) := by
      rw [show -2 * (-σ) * (1 - x) = -2 * σ * x - (-2 * σ) by ring, Real.exp_sub]
    have e2 : Real.exp (-2 * (-σ)) = 1 / Real.exp (-2 * σ) := by
      rw [show -2 * (-σ) = 0 - (-2 * σ) by ring, Real.exp_sub, Real.exp_zero]
    have hden : (1 : ℝ) - Real.exp (-2 * σ) ≠ 0 := one_sub_exp_ne_zero h
    have hexp : Real.exp (-2 * σ) ≠ 0 := (Real.exp_pos _).ne'
    have hB1 : Real.exp (-2 * σ) - 1 ≠ 0 := by
      intro hcon
      apply hden
      linarith [hcon]
    unfold kimuraFixation
    rw [ite_eq_right h, ite_eq_right h', e1, e2]
    have h1 : (1:ℝ) - Real.exp (-2 * σ * x) / Real.exp (-2 * σ)
        = (Real.exp (-2 * σ) - Real.exp (-2 * σ * x)) / Real.exp (-2 * σ) := by
      rw [eq_div_iff hexp, sub_mul, one_mul, div_mul_cancel₀ _ hexp]
    have h2 : (1:ℝ) - 1 / Real.exp (-2 * σ)
        = (Real.exp (-2 * σ) - 1) / Real.exp (-2 * σ) := by
      rw [eq_div_iff hexp, sub_mul, one_mul, div_mul_cancel₀ _ hexp]
    have h3 : (1 - Real.exp (-2 * σ * x) / Real.exp (-2 * σ)) / (1 - 1 / Real.exp (-2 * σ))
        = (Real.exp (-2 * σ) - Real.exp (-2 * σ * x)) / (Real.exp (-2 * σ) - 1) := by
      rw [h1, h2, div_eq_div_iff (div_ne_zero hB1 hexp) hB1,
        div_mul_eq_mul_div, mul_div_assoc]
    have h41 : (1:ℝ) - (Real.exp (-2 * σ) - Real.exp (-2 * σ * x)) / (Real.exp (-2 * σ) - 1)
        = ((Real.exp (-2 * σ) - 1) - (Real.exp (-2 * σ) - Real.exp (-2 * σ * x)))
          / (Real.exp (-2 * σ) - 1) := by
      rw [eq_div_iff hB1, sub_mul, one_mul, div_mul_cancel₀ _ hB1]
    rw [h3, h41, div_eq_div_iff hden hB1]
    ring

/-- Deleterious alleles (`σ < 0`) are fixed with probability strictly smaller than their
initial frequency `x ∈ (0, 1)`. -/
theorem kimuraFixation_lt {σ x : ℝ} (hσ : σ < 0) (hx : x ∈ Ioo (0 : ℝ) 1) :
    kimuraFixation σ x < x := by
  have hx1 : (0:ℝ) < x := hx.1
  have hx2 : x < (1:ℝ) := hx.2
  have h1 : (1 : ℝ) - x ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hx2, by linarith [hx1]⟩
  have hσ' : (0:ℝ) < -σ := by linarith [hσ]
  have h2 : (1 : ℝ) - x < kimuraFixation (-σ) (1 - x) :=
    lt_kimuraFixation hσ' h1
  rw [kimuraFixation_neg]
  linarith [h2]

/-- Kimura's fixation probability is strictly increasing in the selection coefficient at every
interior frequency. The endpoints are excluded on purpose: at `x = 0` the value is constantly
`0` and at `x = 1` constantly `1`. -/
theorem strictMono_kimuraFixation_in_sigma {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    StrictMono (fun σ => kimuraFixation σ x) := by
  have hall : ∀ s : ℝ, HasDerivAt (fun σ => kimuraFixation σ x)
      (if s = 0 then x*(1-x) else ((0 - Real.exp (-2*s*x)*(-2*x))*(1 - Real.exp (-2*s)) -
        (1 - Real.exp (-2*s*x))*(0 - Real.exp (-2*s)*(-2)))/(1 - Real.exp (-2*s))^2) s := by
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [ite_eq_left rfl]
      exact hasDerivAt_kimuraFixation_sigma_zero_aux hx
    · rw [ite_eq_right hs]
      have hinner1 : HasDerivAt (fun σ : ℝ => -2*σ*x) (-2*x) s := by
        simpa using ((hasDerivAt_id s).const_mul (-2)).mul_const x
      have hinner2 : HasDerivAt (fun σ : ℝ => -2*σ) (-2) s := by
        simpa using (hasDerivAt_id s).const_mul (-2)
      have hE1 : HasDerivAt (fun σ => Real.exp (-2*σ*x)) (Real.exp (-2*s*x)*(-2*x)) s :=
        hinner1.exp
      have hE2 : HasDerivAt (fun σ => Real.exp (-2*σ)) (Real.exp (-2*s)*(-2)) s :=
        hinner2.exp
      have hN : HasDerivAt (fun σ => 1 - Real.exp (-2*σ*x)) (0 - Real.exp (-2*s*x)*(-2*x)) s :=
        (hasDerivAt_const _ _).sub hE1
      have hD : HasDerivAt (fun σ => 1 - Real.exp (-2*σ)) (0 - Real.exp (-2*s)*(-2)) s :=
        (hasDerivAt_const _ _).sub hE2
      have hDne : (1:ℝ) - Real.exp (-2*s) ≠ 0 := one_sub_exp_ne_zero hs
      have hdivPi : HasDerivAt ((fun σ => 1 - Real.exp (-2*σ*x)) / (fun σ => 1 - Real.exp (-2*σ)))
          (((0 - Real.exp (-2*s*x)*(-2*x))*(1 - Real.exp (-2*s)) -
            (1 - Real.exp (-2*s*x))*(0 - Real.exp (-2*s)*(-2)))/(1 - Real.exp (-2*s))^2) s :=
        hN.div hD hDne
      have heq : (fun σ => (1 - Real.exp (-2*σ*x)) / (1 - Real.exp (-2*σ)))
          = ((fun σ => 1 - Real.exp (-2*σ*x)) / (fun σ => 1 - Real.exp (-2*σ))) := by
        funext σ
        simp only [Pi.div_apply]
      have hdiv : HasDerivAt (fun σ => (1 - Real.exp (-2*σ*x)) / (1 - Real.exp (-2*σ)))
          (((0 - Real.exp (-2*s*x)*(-2*x))*(1 - Real.exp (-2*s)) -
            (1 - Real.exp (-2*s*x))*(0 - Real.exp (-2*s)*(-2)))/(1 - Real.exp (-2*s))^2) s := by
        rw [heq]
        exact hdivPi
      have hev : Filter.EventuallyEq (nhds s) (fun σ => kimuraFixation σ x)
          (fun σ => (1 - Real.exp (-2*σ*x)) / (1 - Real.exp (-2*σ))) := by
        filter_upwards [eventually_ne_nhds hs] with σ hσ
        unfold kimuraFixation
        rw [ite_eq_right hσ]
      exact hdiv.congr_of_eventuallyEq hev
  have hpos : ∀ s : ℝ, 0 < (if s = 0 then x*(1-x) else
      ((0 - Real.exp (-2*s*x)*(-2*x))*(1 - Real.exp (-2*s)) -
      (1 - Real.exp (-2*s*x))*(0 - Real.exp (-2*s)*(-2)))/(1 - Real.exp (-2*s))^2) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [ite_eq_left rfl]
      exact mul_pos hx.1 (sub_pos.2 hx.2)
    · rw [ite_eq_right hs]
      have hB : (1:ℝ) - Real.exp (-2*s) ≠ 0 := one_sub_exp_ne_zero hs
      have hsq : (0:ℝ) < (1 - Real.exp (-2*s))^2 := by
        rw [pow_two]
        exact mul_self_pos.2 hB
      apply div_pos _ hsq
      have hne : (-2*s*x) ≠ (-2*s*x + -2*s) := by
        intro hcon
        apply hs
        linarith
      have hconv := strictConvexOn_exp.2 (mem_univ (-2*s*x)) (mem_univ (-2*s*x + -2*s))
        hne hx.1 (sub_pos.2 hx.2) (by ring)
      simp only [smul_eq_mul] at hconv
      rw [show x * (-2*s*x) + (1-x) * (-2*s*x + -2*s) = -2*s by ring] at hconv
      have hR : Real.exp (-2*s*x) * Real.exp (-2*s) = Real.exp (-2*s*x + -2*s) :=
        (Real.exp_add _ _).symm
      have heq : (0 - Real.exp (-2*s*x)*(-2*x))*(1 - Real.exp (-2*s)) -
          (1 - Real.exp (-2*s*x))*(0 - Real.exp (-2*s)*(-2))
          = 2*(x*Real.exp (-2*s*x) + (1-x)*Real.exp (-2*s*x + -2*s) - Real.exp (-2*s)) := by
        linear_combination 2*(1-x)*hR
      rw [heq]
      linarith [hconv]
  exact strictMono_of_hasDerivAt_pos hall hpos

/-- Neutral perturbation: for `x ∈ [0, 1]`, the first-order effect of weak genic selection on
the fixation probability at neutrality is `x (1 - x)`; endpoints give derivative `0`, matching
the constant values there. -/
theorem hasDerivAt_kimuraFixation_sigma_zero {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun σ => kimuraFixation σ x) (x * (1 - x)) 0 := by
  obtain rfl | h0 := eq_or_lt_of_le hx.1
  · have hfun : (fun σ => kimuraFixation σ 0) = fun _ => (0:ℝ) :=
      funext fun σ => kimuraFixation_zero_right σ
    rw [hfun]
    simpa using hasDerivAt_const _ _
  · obtain rfl | h1 := eq_or_lt_of_le hx.2
    · have hfun : (fun σ => kimuraFixation σ 1) = fun _ => (1:ℝ) :=
        funext fun σ => kimuraFixation_one_right σ
      rw [hfun]
      simpa using hasDerivAt_const _ _
    · exact hasDerivAt_kimuraFixation_sigma_zero_aux ⟨h0, h1⟩

end MathlibExt.Biology.PopulationGenetics.Diffusion
