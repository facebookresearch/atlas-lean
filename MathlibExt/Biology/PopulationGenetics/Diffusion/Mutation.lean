/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Binomial
import MathlibExt.Probability.Distributions.BinomialMoments

/-!
# The Wright–Fisher diffusion with two-way mutation: Wright's Beta stationary law

Consider a biallelic locus in a diploid population of size `N`. Each generation an `a` copy
mutates to `A` with probability `u₁` and an `A` copy mutates to `a` with probability `u₂`. With
time in units of `2N` generations and scaled mutation rates `θ₁ = 4N u₁`, `θ₂ = 4N u₂`, the
frequency `x ∈ [0, 1]` of `A` is approximated by the Wright–Fisher diffusion with infinitesimal
variance `a(x) = x (1 - x)` and drift `b(x) = (θ₁ (1 - x) - θ₂ x) / 2`, whose backward generator is

  `(L f)(x) = x (1 - x) / 2 · f''(x) + (θ₁ (1 - x) - θ₂ x) / 2 · f'(x)`.

For `θ₁, θ₂ > 0` its stationary law is Wright's Beta`(θ₁, θ₂)` distribution, with density
`π(x) = x ^ (θ₁ - 1) (1 - x) ^ (θ₂ - 1) / B(θ₁, θ₂)` on `(0, 1)` (Mathlib's `betaPDFReal` and
`betaMeasure`). In the scaled rates `α = θ₁ / 2`, `β = θ₂ / 2` used by `wrightDensity`, the
unnormalized density is `wrightDensity (θ₁ / 2) (θ₂ / 2)`.

The diffusion process itself is **not** formalized (Mathlib has no diffusion processes). This
file proves the analytic stationarity statements:

* the density solves the stationary forward (Fokker–Planck) equation
  `½ (a π)'' - (b π)' = 0` on `(0, 1)` and has zero probability flux `½ (a π)' - b π = 0`;
* weak stationarity: `∫ L f dπ = 0` for every `f` that is `C²` on `[0, 1]` (integration by parts;
  the boundary term `½ a π f'` vanishes at `0` and `1` because `a π ∝ x ^ θ₁ (1 - x) ^ θ₂`);
* the stationary mean `θ₁ / (θ₁ + θ₂)` and expected heterozygosity
  `2 θ₁ θ₂ / ((θ₁ + θ₂) (θ₁ + θ₂ + 1))`, obtained from weak stationarity applied to `x` and
  `2 x (1 - x)`;
* the link with the Wright–Fisher chain on `M = 2N` gene copies (mutation, then binomial
  sampling) with `uᵢ = θᵢ / (2M)`: the scaled mean change of frequency in one generation is
  exactly the drift `(θ₁ (1 - x) - θ₂ x) / 2`, and the scaled second moment is given exactly
  (it tends to `x (1 - x)` as `M → ∞`; that limit is not stated).

## Main results

* `mutationGenerator`: the backward generator `L` above; `mutationGenerator_zero_zero` recovers
  the neutral generator `generator 0`.
* `betaPDFReal_eq_wrightDensity`, `contDiffOn_betaPDFReal`.
* `flux_betaPDFReal`, `forwardEquation_betaPDFReal`: zero flux and the stationary forward
  equation on `(0, 1)`.
* `intervalIntegrable_mutationGenerator_mul_betaPDFReal`,
  `integral_mutationGenerator_mul_betaPDFReal`, `integrable_mutationGenerator_betaMeasure`,
  `integral_mutationGenerator_betaMeasure`: weak stationarity.
* `mutationGenerator_id`, `mutationGenerator_heterozygosity`, `integral_id_betaMeasure`,
  `integral_heterozygosity_betaMeasure`: the stationary mean and heterozygosity.
* `mutatedFreq`, `integral_binomial_mutatedFreq_drift`, `integral_binomial_mutatedFreq_sq`:
  one generation of the Wright–Fisher chain with mutation.

## References

* S. Wright, *Evolution in Mendelian populations*, Genetics 16 (1931) 97–159.
* S. Wright, *The distribution of gene frequencies in populations*, PNAS 23 (1937) 307–320.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4–5.
* S. N. Ethier and T. G. Kurtz, *Markov Processes*, Wiley (1986), ch. 10.
-/

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The backward generator of the Wright–Fisher diffusion with two-way mutation, time in units of
`2N` generations and scaled mutation rates `θ₁ = 4N u₁` (towards the allele) and `θ₂ = 4N u₂`
(away from it): `(L f)(x) = x (1 - x) / 2 · f''(x) + (θ₁ (1 - x) - θ₂ x) / 2 · f'(x)`. -/
noncomputable def mutationGenerator (θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (1 - x) / 2 * deriv (deriv f) x + (θ₁ * (1 - x) - θ₂ * x) / 2 * deriv f x

/-- Without mutation the generator is the neutral Wright–Fisher generator `generator 0`. -/
theorem mutationGenerator_zero_zero (f : ℝ → ℝ) (x : ℝ) :
    mutationGenerator 0 0 f x = generator 0 f x := by
  simp [mutationGenerator, generator]

/-- On `(0, 1)` the Beta`(θ₁, θ₂)` density is Wright's unnormalized density in the scaled rates
`α = θ₁ / 2`, `β = θ₂ / 2`, divided by the Beta function `B(θ₁, θ₂)`. -/
theorem betaPDFReal_eq_wrightDensity (θ₁ θ₂ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal θ₁ θ₂ x = wrightDensity (θ₁ / 2) (θ₂ / 2) x / beta θ₁ θ₂ := by
  rw [betaPDFReal, ite_eq_left ⟨hx.1, hx.2⟩, wrightDensity, show 2 * (θ₁ / 2) - 1 = θ₁ - 1 by ring,
    show 2 * (θ₂ / 2) - 1 = θ₂ - 1 by ring]
  ring

/-- The Beta`(θ₁, θ₂)` density is analytic (`C^ω`), in particular smooth, on `(0, 1)`, so the
derivatives in `flux_betaPDFReal` and `forwardEquation_betaPDFReal` exist. -/
theorem contDiffOn_betaPDFReal (θ₁ θ₂ : ℝ) :
    ContDiffOn ℝ ⊤ (betaPDFReal θ₁ θ₂) (Ioo 0 1) := by
  intro x hx
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hf : ContDiffAt ℝ ⊤ (fun y => 1 / beta θ₁ θ₂ * y ^ (θ₁ - 1) * (1 - y) ^ (θ₂ - 1)) x :=
    (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hx.1.ne')).mul
      ((contDiffAt_rpow_const_of_ne hx1).comp x (contDiffAt_const.sub contDiffAt_id))
  refine (hf.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [betaPDFReal, ite_eq_left ⟨hy.1, hy.2⟩]

/-- On `(0, 1)`, `x (1 - x) π(x)` is locally `(1 / B) · x (1 - x) · wrightDensity`. -/
private theorem flux_eventuallyEq (θ₁ θ₂ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y => y * (1 - y) * betaPDFReal θ₁ θ₂ y) =ᶠ[nhds x]
      fun y => 1 / beta θ₁ θ₂ * (y * (1 - y) * wrightDensity (θ₁ / 2) (θ₂ / 2) y) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [betaPDFReal_eq_wrightDensity θ₁ θ₂ hy]
  ring

/-- **Zero probability flux (Wright 1931).** On `(0, 1)` the Beta`(θ₁, θ₂)` density `π`
satisfies `½ (x (1 - x) π)' - (θ₁ (1 - x) - θ₂ x) / 2 · π = 0`. The identity holds for all real
`θ₁, θ₂` (it is linear in `π`; Mathlib's density is identically `0` when `B(θ₁, θ₂) = 0`);
`π` is a probability density when `θ₁, θ₂ > 0` (`isProbabilityMeasureBeta`). -/
theorem flux_betaPDFReal (θ₁ θ₂ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (fun y => y * (1 - y) * betaPDFReal θ₁ θ₂ y) x / 2 -
      (θ₁ * (1 - x) - θ₂ * x) / 2 * betaPDFReal θ₁ θ₂ x = 0 := by
  rw [(flux_eventuallyEq θ₁ θ₂ hx).deriv_eq, deriv_const_mul_field']
  simp only
  rw [deriv_flux_wrightDensity _ _ hx, betaPDFReal_eq_wrightDensity θ₁ θ₂ hx]
  ring

/-- **Stationary forward equation (Wright 1931).** On `(0, 1)` the Beta`(θ₁, θ₂)` density `π`
solves the stationary Fokker–Planck equation `½ (a π)'' - (b π)' = 0` with `a(x) = x (1 - x)` and
`b(x) = (θ₁ (1 - x) - θ₂ x) / 2`. Holds for all real `θ₁, θ₂` (see `flux_betaPDFReal`). -/
theorem forwardEquation_betaPDFReal (θ₁ θ₂ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (fun y => y * (1 - y) * betaPDFReal θ₁ θ₂ y)) x / 2 -
      deriv (fun y => (θ₁ * (1 - y) - θ₂ * y) / 2 * betaPDFReal θ₁ θ₂ y) x = 0 := by
  have h : deriv (fun y => y * (1 - y) * betaPDFReal θ₁ θ₂ y) =ᶠ[nhds x]
      fun y => 2 * ((θ₁ * (1 - y) - θ₂ * y) / 2 * betaPDFReal θ₁ θ₂ y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    linarith [flux_betaPDFReal θ₁ θ₂ hy]
  rw [h.deriv_eq, deriv_const_mul_field']
  ring

private theorem betaPDFReal_nonneg' {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (x : ℝ) :
    0 ≤ betaPDFReal θ₁ θ₂ x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hθ₁ hθ₂).le
  · simp [betaPDFReal, hx]

private theorem intervalIntegrable_betaPDFReal {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IntervalIntegrable (betaPDFReal θ₁ θ₂) volume 0 1 := by
  have h := ((intervalIntegrable_wrightDensity (α := θ₁ / 2) (β := θ₂ / 2) (by linarith)
    (by linarith)).div_const (beta θ₁ θ₂))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h ⊢
  exact h.congr_fun (fun x hx => (betaPDFReal_eq_wrightDensity θ₁ θ₂ hx).symm) measurableSet_Ioo

/-- Integrals against `betaMeasure θ₁ θ₂` are interval integrals against the density. -/
private theorem integral_betaMeasure {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (g : ℝ → ℝ) :
    ∫ x, g x ∂(betaMeasure θ₁ θ₂) = ∫ x in (0 : ℝ)..1, g x * betaPDFReal θ₁ θ₂ x := by
  rw [betaMeasure, show betaPDF θ₁ θ₂ = fun x => ENNReal.ofReal (betaPDFReal θ₁ θ₂ x) from rfl,
    integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal θ₁ θ₂).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le zero_le_one]
  simp_rw [ENNReal.toReal_ofReal (betaPDFReal_nonneg' hθ₁ hθ₂ _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 1)]
  · exact setIntegral_congr_fun measurableSet_Ioc fun x _ => mul_comm _ _
  · intro x hx
    have : ¬ (0 < x ∧ x < 1) := fun h => hx ⟨h.1, h.2.le⟩
    simp [betaPDFReal, this]

/-- Integrability against `betaMeasure θ₁ θ₂` is interval integrability against the density. -/
private theorem integrable_betaMeasure_iff {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (g : ℝ → ℝ) : Integrable g (betaMeasure θ₁ θ₂) ↔
      IntervalIntegrable (fun x => g x * betaPDFReal θ₁ θ₂ x) volume 0 1 := by
  rw [betaMeasure, show betaPDF θ₁ θ₂ = fun x => ENNReal.ofReal (betaPDFReal θ₁ θ₂ x) from rfl,
    integrable_withDensity_iff_integrable_smul'
    (measurable_betaPDFReal θ₁ θ₂).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  simp_rw [ENNReal.toReal_ofReal (betaPDFReal_nonneg' hθ₁ hθ₂ _), smul_eq_mul]
  rw [← integrableOn_iff_integrable_of_support_subset (s := Ioc 0 1)]
  · exact ⟨fun h => h.congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioc,
      fun h => h.congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioc⟩
  · intro x hx
    by_contra h
    have : ¬ (0 < x ∧ x < 1) := fun h' => h ⟨h'.1, h'.2.le⟩
    exact hx (by simp [betaPDFReal, this])

/-- First and second derivatives of a function `C²` on `[0, 1]`, read off at interior points. -/
private theorem contDiffOn_Icc_facts {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    ContinuousOn (derivWithin f (Icc 0 1)) (Icc 0 1) ∧
      ContinuousOn (derivWithin (derivWithin f (Icc 0 1)) (Icc 0 1)) (Icc 0 1) ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, deriv f x = derivWithin f (Icc 0 1) x ∧
        deriv (deriv f) x = derivWithin (derivWithin f (Icc 0 1)) (Icc 0 1) x ∧
        HasDerivAt (derivWithin f (Icc 0 1))
          (derivWithin (derivWithin f (Icc 0 1)) (Icc 0 1) x) x := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h1 : ContDiffOn ℝ 1 (derivWithin f (Icc 0 1)) (Icc 0 1) :=
    hf.derivWithin hs (by norm_num)
  have h2 : ContDiffOn ℝ 0 (derivWithin (derivWithin f (Icc 0 1)) (Icc 0 1)) (Icc 0 1) :=
    h1.derivWithin hs (by norm_num)
  refine ⟨h1.continuousOn, h2.continuousOn, fun x hx => ?_⟩
  have hn : Icc (0 : ℝ) 1 ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have hD : deriv f =ᶠ[nhds x] derivWithin f (Icc 0 1) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)).symm
  have hd1 : DifferentiableAt ℝ (derivWithin f (Icc 0 1)) x :=
    ((h1.differentiableOn one_ne_zero) x (Ioo_subset_Icc_self hx)).differentiableAt hn
  refine ⟨hD.eq_of_nhds, ?_, ?_⟩
  · rw [hD.deriv_eq, derivWithin_of_mem_nhds hn]
  · exact hd1.hasDerivAt.congr_deriv (derivWithin_of_mem_nhds hn).symm

/-- For `θ₁, θ₂ > 0` and `f` twice continuously differentiable on `[0, 1]`, `L f · π` is
integrable on `[0, 1]`, so the integral in `integral_mutationGenerator_mul_betaPDFReal` is a
genuine (not junk) value. -/
theorem intervalIntegrable_mutationGenerator_mul_betaPDFReal {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    IntervalIntegrable (fun x => mutationGenerator θ₁ θ₂ f x * betaPDFReal θ₁ θ₂ x)
      volume 0 1 := by
  obtain ⟨hc1, hc2, hint⟩ := contDiffOn_Icc_facts hf
  have hG : ContinuousOn (fun x => x * (1 - x) / 2 * derivWithin (derivWithin f (Icc 0 1))
      (Icc 0 1) x + (θ₁ * (1 - x) - θ₂ * x) / 2 * derivWithin f (Icc 0 1) x) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).div_const 2).mul hc2
      |>.add ((((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).sub
        (continuousOn_const.mul continuousOn_id)).div_const 2).mul hc1)
  have h := (intervalIntegrable_betaPDFReal hθ₁ hθ₂).continuousOn_mul hG
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h ⊢
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  obtain ⟨e1, e2, -⟩ := hint x hx
  simp only [mutationGenerator, e1, e2]

/-- **Weak stationarity of Wright's law (density form).** For `θ₁, θ₂ > 0` and every `f` twice
continuously differentiable on `[0, 1]`, `∫₀¹ (L f)(x) π(x) dx = 0` for the Beta`(θ₁, θ₂)`
density `π`. (`L f` uses `deriv`, which agrees with the one-sided derivatives inside `(0, 1)`;
its values at the endpoints do not affect the integral.) The proof is integration by parts:
`L f · π = (x ^ θ₁ (1 - x) ^ θ₂ f' / (2 B(θ₁, θ₂)))'` on `(0, 1)` because the flux vanishes, and
this boundary term is `0` at both endpoints since `θ₁, θ₂ > 0`. -/
theorem integral_mutationGenerator_mul_betaPDFReal {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    ∫ x in (0 : ℝ)..1, mutationGenerator θ₁ θ₂ f x * betaPDFReal θ₁ θ₂ x = 0 := by
  obtain ⟨hc1, -, hint⟩ := contDiffOn_Icc_facts hf
  have hB : 0 < beta θ₁ θ₂ := beta_pos hθ₁ hθ₂
  have hcont : ContinuousOn (fun x => x ^ θ₁ * (1 - x) ^ θ₂ * derivWithin f (Icc 0 1) x /
      (2 * beta θ₁ θ₂)) (Icc 0 1) :=
    (((continuous_rpow_const hθ₁.le).continuousOn.mul
      ((continuous_rpow_const hθ₂.le).comp (continuous_const.sub continuous_id)).continuousOn).mul
        hc1).div_const _
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => x ^ θ₁ * (1 - x) ^ θ₂ *
      derivWithin f (Icc 0 1) x / (2 * beta θ₁ θ₂))
      (mutationGenerator θ₁ θ₂ f x * betaPDFReal θ₁ θ₂ x) x := by
    intro x hx
    obtain ⟨e1, e2, hd⟩ := hint x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
    have hA : HasDerivAt (fun z : ℝ => z ^ θ₁) (θ₁ * x ^ (θ₁ - 1)) x :=
      hasDerivAt_rpow_const (Or.inl hx0)
    have hA' := ((hasDerivAt_id' x).const_sub 1).rpow_const (p := θ₂) (Or.inl hx1)
    have h := ((hA.mul hA').mul hd).div_const (2 * beta θ₁ θ₂)
    convert h using 1
    simp only [Pi.mul_apply]
    rw [mutationGenerator, e1, e2, betaPDFReal, ite_eq_left ⟨hx.1, hx.2⟩, rpow_sub_one hx0,
      rpow_sub_one hx1]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    (intervalIntegrable_mutationGenerator_mul_betaPDFReal hθ₁ hθ₂ hf)]
  simp [zero_rpow hθ₁.ne', zero_rpow hθ₂.ne']

/-- For `θ₁, θ₂ > 0` and `f` twice continuously differentiable on `[0, 1]`, `L f` is integrable
against Wright's stationary law `Beta(θ₁, θ₂)`. -/
theorem integrable_mutationGenerator_betaMeasure {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    Integrable (mutationGenerator θ₁ θ₂ f) (betaMeasure θ₁ θ₂) :=
  (integrable_betaMeasure_iff hθ₁ hθ₂ _).2
    (intervalIntegrable_mutationGenerator_mul_betaPDFReal hθ₁ hθ₂ hf)

/-- **Weak stationarity of Wright's law (Wright 1931; Ewens 2004, ch. 4).** For `θ₁, θ₂ > 0`
and every `f` twice continuously differentiable on `[0, 1]`, `∫ L f d(Beta(θ₁, θ₂)) = 0`. -/
theorem integral_mutationGenerator_betaMeasure {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    ∫ x, mutationGenerator θ₁ θ₂ f x ∂(betaMeasure θ₁ θ₂) = 0 := by
  rw [integral_betaMeasure hθ₁ hθ₂, integral_mutationGenerator_mul_betaPDFReal hθ₁ hθ₂ hf]

/-- The generator applied to the frequency itself is the mutation drift:
`L x = (θ₁ (1 - x) - θ₂ x) / 2`. -/
theorem mutationGenerator_id (θ₁ θ₂ x : ℝ) :
    mutationGenerator θ₁ θ₂ id x = (θ₁ * (1 - x) - θ₂ * x) / 2 := by
  simp [mutationGenerator]

/-- The generator applied to the heterozygosity `H(x) = 2x (1 - x)`:
`L H = -2x (1 - x) + (θ₁ (1 - x) - θ₂ x) (1 - 2x)` (drift decreases `H` at rate `1`, mutation
restores it). -/
theorem mutationGenerator_heterozygosity (θ₁ θ₂ x : ℝ) :
    mutationGenerator θ₁ θ₂ (fun y => 2 * y * (1 - y)) x =
      -(2 * x * (1 - x)) + (θ₁ * (1 - x) - θ₂ * x) * (1 - 2 * x) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => 2 * y * (1 - y)) (2 - 4 * y) y := fun y => by
    convert ((hasDerivAt_id' y).const_mul 2).mul ((hasDerivAt_id' y).const_sub 1) using 1
    ring
  have hD : deriv (fun y : ℝ => 2 * y * (1 - y)) = fun y => 2 - 4 * y :=
    funext fun y => (hd y).deriv
  have h2 : HasDerivAt (fun y : ℝ => 2 - 4 * y) (-4) x := by
    simpa using ((hasDerivAt_id' x).const_mul 4).const_sub 2
  rw [mutationGenerator, hD, h2.deriv]
  ring

/-- Quadratic moments under `betaMeasure θ₁ θ₂`, by linearity. -/
private theorem integral_quadratic_betaMeasure {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (a b c : ℝ) : ∫ x, (a + b * x + c * x ^ 2) ∂(betaMeasure θ₁ θ₂) =
      a + b * (∫ x, x ∂(betaMeasure θ₁ θ₂)) + c * ∫ x, x ^ 2 ∂(betaMeasure θ₁ θ₂) := by
  have := isProbabilityMeasureBeta hθ₁ hθ₂
  have hI : ∀ g : ℝ → ℝ, Continuous g → Integrable g (betaMeasure θ₁ θ₂) := fun g hg =>
    (integrable_betaMeasure_iff hθ₁ hθ₂ g).2
      ((intervalIntegrable_betaPDFReal hθ₁ hθ₂).continuousOn_mul hg.continuousOn)
  have h1 := hI (fun x => x) continuous_id
  have h2 := hI (fun x => x ^ 2) (continuous_pow 2)
  have hab : Integrable (fun x : ℝ => a + b * x) (betaMeasure θ₁ θ₂) :=
    (integrable_const a).add (h1.const_mul b)
  have hc : Integrable (fun x : ℝ => c * x ^ 2) (betaMeasure θ₁ θ₂) := h2.const_mul c
  have hb : Integrable (fun x : ℝ => b * x) (betaMeasure θ₁ θ₂) := h1.const_mul b
  rw [integral_add hab hc, integral_add (integrable_const a) hb, integral_const, integral_const_mul,
    integral_const_mul]
  simp

/-- **Stationary mean (Wright 1931).** Under Wright's stationary law `Beta(θ₁, θ₂)` with
`θ₁, θ₂ > 0` the mean allele frequency is `θ₁ / (θ₁ + θ₂)`. -/
theorem integral_id_betaMeasure {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    ∫ x, x ∂(betaMeasure θ₁ θ₂) = θ₁ / (θ₁ + θ₂) := by
  have h := integral_mutationGenerator_betaMeasure hθ₁ hθ₂ (f := id) contDiffOn_id
  simp_rw [mutationGenerator_id] at h
  rw [integral_congr_ae (g := fun x => θ₁ / 2 + (-(θ₁ + θ₂) / 2) * x + 0 * x ^ 2)
    (ae_of_all _ fun x => by ring), integral_quadratic_betaMeasure hθ₁ hθ₂] at h
  field_simp
  linarith

/-- **Stationary heterozygosity (Wright 1931; Ewens 2004, ch. 5).** Under Wright's stationary law
`Beta(θ₁, θ₂)` with `θ₁, θ₂ > 0` the expected heterozygosity is
`E[2x (1 - x)] = 2 θ₁ θ₂ / ((θ₁ + θ₂) (θ₁ + θ₂ + 1))`. -/
theorem integral_heterozygosity_betaMeasure {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    ∫ x, 2 * x * (1 - x) ∂(betaMeasure θ₁ θ₂) =
      2 * θ₁ * θ₂ / ((θ₁ + θ₂) * (θ₁ + θ₂ + 1)) := by
  have hf : ContDiffOn ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) (Icc 0 1) :=
    ((contDiff_const.mul contDiff_id).mul (contDiff_const.sub contDiff_id)).contDiffOn
  have h := integral_mutationGenerator_betaMeasure hθ₁ hθ₂ hf
  simp_rw [mutationGenerator_heterozygosity] at h
  rw [integral_congr_ae (g := fun x => θ₁ + (-2 - 3 * θ₁ - θ₂) * x + (2 + 2 * θ₁ + 2 * θ₂) * x ^ 2)
    (ae_of_all _ fun x => by ring), integral_quadratic_betaMeasure hθ₁ hθ₂,
    integral_id_betaMeasure hθ₁ hθ₂] at h
  rw [integral_congr_ae (g := fun x => 0 + 2 * x + (-2) * x ^ 2) (ae_of_all _ fun x => by ring),
    integral_quadratic_betaMeasure hθ₁ hθ₂, integral_id_betaMeasure hθ₁ hθ₂]
  have hS : 0 < θ₁ + θ₂ := by linarith
  have hm2 : ∫ x, x ^ 2 ∂(betaMeasure θ₁ θ₂) = θ₁ * (θ₁ + 1) / ((θ₁ + θ₂) * (θ₁ + θ₂ + 1)) := by
    field_simp at h ⊢
    nlinarith [h]
  rw [hm2]
  field_simp
  ring

/-- Allele frequency after one generation of two-way mutation, before random sampling: an `a`
copy mutates to `A` with probability `u₁` and an `A` copy to `a` with probability `u₂`, so the
frequency `x` of `A` becomes `(1 - u₂) x + u₁ (1 - x) ∈ [0, 1]`. -/
noncomputable def mutatedFreq (u₁ u₂ x : unitInterval) : unitInterval :=
  ⟨(1 - u₂) * x + u₁ * (1 - x), by
    obtain ⟨hu₁, hu₁'⟩ := u₁.2
    obtain ⟨hu₂, hu₂'⟩ := u₂.2
    obtain ⟨hx, hx'⟩ := x.2
    constructor
    · nlinarith
    · nlinarith⟩

/-- Integrals against `Bin(M, p)` of `a + b k + c (M p - k) ^ 2`, from the binomial mean
(`integral_of_hasLaw_binomial`) and second moment (`integral_sq_map_cast_binomial`). -/
private theorem integral_binomial_quadratic (M : ℕ) (p : unitInterval) (a b c : ℝ) :
    ∫ k, (a + b * (k : ℝ) + c * (M * (p : ℝ) - k) ^ 2) ∂(binomial M p) =
      a + b * (M * p) + c * (M * p * (1 - p)) := by
  rw [integral_binomial, ← integral_map_cast_binomial (R := ℝ)
    (fun x : ℝ => a + b * x + c * (M * (p : ℝ) - x) ^ 2)]
  have hmean : ∫ x, x ∂Bin(ℝ, M, p) = (p : ℝ) * M := integral_of_hasLaw_binomial HasLaw.id
  have hsq := integral_sq_map_cast_binomial (n := M) (p := p)
  have he : (fun x : ℝ => a + b * x + c * (M * (p : ℝ) - x) ^ 2) =
      fun x => (a + c * (M * (p : ℝ)) ^ 2) + ((b - 2 * c * (M * p)) * x + c * x ^ 2) := by
    funext x
    ring
  rw [he]
  generalize hK : a + c * (M * (p : ℝ)) ^ 2 = K
  generalize hB : b - 2 * c * (M * (p : ℝ)) = B
  rw [integral_add (integrable_map_cast_binomial _) (integrable_map_cast_binomial _),
    integral_add (integrable_map_cast_binomial _) (integrable_map_cast_binomial _),
    integral_const, integral_const_mul, integral_const_mul, hmean, hsq]
  simp only [probReal_univ, one_smul]
  rw [← hK, ← hB]
  ring

/-- **Drift of the Wright–Fisher chain with mutation (Ewens 2004, ch. 4).** One generation of the
Wright–Fisher chain on `M` gene copies (`M = 2N`): mutation moves the frequency `x` to
`p' = mutatedFreq u₁ u₂ x`, then the new count is `Binomial(M, p')`. With `u₁ = θ₁ / (2M)`,
`u₂ = θ₂ / (2M)` (`θᵢ = 4N uᵢ`), the expected change of frequency per `2N = M` generations is
exactly the drift coefficient of `mutationGenerator`:
`M · (E[k / M] - x) = (θ₁ (1 - x) - θ₂ x) / 2`, for every `M`. -/
theorem integral_binomial_mutatedFreq_drift {M : ℕ} (hM : M ≠ 0) {θ₁ θ₂ : ℝ}
    {u₁ u₂ : unitInterval} (hu₁ : (u₁ : ℝ) = θ₁ / (2 * M)) (hu₂ : (u₂ : ℝ) = θ₂ / (2 * M))
    (x : unitInterval) :
    M * (∫ k, (k : ℝ) / M ∂(binomial M (mutatedFreq u₁ u₂ x)) - x) =
      (θ₁ * (1 - x) - θ₂ * x) / 2 := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h := integral_binomial_quadratic M (mutatedFreq u₁ u₂ x) 0 (1 / M) 0
  rw [show (fun k : ℕ => (k : ℝ) / M) = fun k : ℕ => 0 + 1 / (M : ℝ) * k +
      0 * (M * (mutatedFreq u₁ u₂ x : ℝ) - k) ^ 2 from funext fun k => by ring, h]
  simp only [mutatedFreq, hu₁, hu₂]
  field_simp
  ring

/-- **Infinitesimal variance of the Wright–Fisher chain with mutation.** In the setting of
`integral_binomial_mutatedFreq_drift`, the scaled second moment of the frequency change is
`M · E[(k / M - x) ^ 2] = p' (1 - p') + (θ₁ (1 - x) - θ₂ x) ^ 2 / (4M)` with
`p' = mutatedFreq u₁ u₂ x = x + (θ₁ (1 - x) - θ₂ x) / (2M)`. As `M → ∞` with `θ₁, θ₂, x` fixed
this tends to `x (1 - x)`, the diffusion coefficient of `mutationGenerator` (the limit itself is
not stated here). -/
theorem integral_binomial_mutatedFreq_sq {M : ℕ} (hM : M ≠ 0) {θ₁ θ₂ : ℝ}
    {u₁ u₂ : unitInterval} (hu₁ : (u₁ : ℝ) = θ₁ / (2 * M)) (hu₂ : (u₂ : ℝ) = θ₂ / (2 * M))
    (x : unitInterval) :
    M * ∫ k, ((k : ℝ) / M - x) ^ 2 ∂(binomial M (mutatedFreq u₁ u₂ x)) =
      (mutatedFreq u₁ u₂ x : ℝ) * (1 - mutatedFreq u₁ u₂ x) +
        (θ₁ * (1 - x) - θ₂ * x) ^ 2 / (4 * M) := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM
  set p := mutatedFreq u₁ u₂ x
  have hp : (p : ℝ) = x + (θ₁ * (1 - x) - θ₂ * x) / (2 * M) := by
    simp only [p, mutatedFreq, hu₁, hu₂]
    field_simp
    ring
  have h := integral_binomial_quadratic M p (((p : ℝ) - x) ^ 2 - 2 * ((p : ℝ) - x) * p)
    (2 * ((p : ℝ) - x) / M) (1 / (M : ℝ) ^ 2)
  rw [show (fun k : ℕ => ((k : ℝ) / M - x) ^ 2) = fun k : ℕ =>
      ((p : ℝ) - x) ^ 2 - 2 * ((p : ℝ) - x) * p + 2 * ((p : ℝ) - x) / M * k +
        1 / (M : ℝ) ^ 2 * (M * (p : ℝ) - k) ^ 2 from funext fun k => by field_simp; ring, h,
    hp]
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
