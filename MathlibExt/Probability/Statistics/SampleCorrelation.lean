/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Slutsky
public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.Integration

/-!
# Squared sample correlation is asymptotically `χ²₁` under independence

For i.i.d. square-integrable real pairs `(A, B)` with `A ⟂ B` and positive variances,
`N r_N² → χ²₁` in distribution, where `r_N` is the sample correlation of the
first `N` pairs. The same limit holds for the oracle statistic with known means and
variances, so fitting the means and variances costs the contrast no degree of freedom.

This is the domain-independent API used, for example, by the Cochran–Armitage trend
test (`MathlibExt.Biology.StatisticalGenetics.AssociationTests.CochranArmitage`), where
the statistic is `N r²` for genotype score and case indicator.

## Main results

* `sampleMean`: the sample mean of the first `N` terms.
* `sampleCorrSq`: the squared sample correlation of the first `N` pairs.
* `tendstoInDistribution_oracleStat`: the oracle statistic with known means and variances
  is asymptotically `χ²₁`.
* `tendstoInDistribution_mul_sampleCorrSq`: `N r² → χ²₁` under independence.

## Source receipt

The proof is the standard central limit theorem + strong law + Slutsky argument (van der
Vaart 1998, Lemma 2.8 for Slutsky), using Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum_sub` and `strong_law_ae_real`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace MathlibExt.Probability.Statistics.SampleCorrelation

/-! ### Sample moments -/

/-- The sample mean `(∑_{m < N} f m) / N` of the first `N` terms of `f`. -/
noncomputable def sampleMean (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ m ∈ range N, f m) / N

/-- The squared sample correlation of the first `N` pairs `(a m, b m)`, in moment form:
`(mean(ab) - mean(b) mean(a))² / ((mean(b²) - mean(b)²) (mean(a²) - mean(a)²))`. Where a sample
variance vanishes the value is `0`, by `x / 0 = 0`. -/
noncomputable def sampleCorrSq (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  (sampleMean (fun m ↦ a m * b m) N - sampleMean b N * sampleMean a N) ^ 2 /
    ((sampleMean (fun m ↦ b m ^ 2) N - sampleMean b N ^ 2) *
      (sampleMean (fun m ↦ a m ^ 2) N - sampleMean a N ^ 2))

/-! ### Asymptotics of `N r²` under independence -/

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Convergence in distribution depends on the limit only through its law. -/
private theorem tendstoInDistribution_of_hasLaw {Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₂]
    [IsProbabilityMeasure P₃] {T : ℕ → Ω → ℝ} {Y : Ω₂ → ℝ} {Z : Ω₃ → ℝ} {ρ : Measure ℝ}
    (h : TendstoInDistribution T atTop Y (fun _ ↦ P) P₂) (hY : HasLaw Y ρ P₂)
    (hZ : HasLaw Z ρ P₃) :
    TendstoInDistribution T atTop Z (fun _ ↦ P) P₃ where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    convert h.tendsto using 3
    exact congrArg 𝓝 (Subtype.ext (hZ.map_eq.trans hY.map_eq.symm))

/-- Under the standard Gaussian, `x ↦ √c x` has law `N(0, c)`. -/
private theorem hasLaw_sqrt_mul {c : ℝ} (hc : 0 ≤ c) :
    HasLaw (fun x : ℝ ↦ √c * x) (gaussianReal 0 c.toNNReal) (gaussianReal 0 1) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt hc, Real.coe_toNNReal _ hc]

variable {X : ℕ → Ω → ℝ × ℝ}

omit [IsProbabilityMeasure P] in
/-- A measurable function of an i.i.d. sequence obeys the strong law of large numbers. -/
private theorem ae_tendsto_sampleMean (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P) {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hint : Integrable (fun ω ↦ φ (X 0 ω)) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N ↦ sampleMean (fun m ↦ φ (X m ω)) N) atTop
      (𝓝 (∫ ω, φ (X 0 ω) ∂P)) :=
  strong_law_ae_real (fun m ω ↦ φ (X m ω)) hint
    (fun _ _ hij ↦ (hindep.indepFun hij).comp hφ hφ) (fun m ↦ (hident m).comp hφ)

/-- The central limit theorem for a measurable function of an i.i.d. sequence, with the limit
`√(Var) x` under the standard Gaussian. -/
private theorem tendstoInDistribution_clt (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P) {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hL2 : MemLp (fun ω ↦ φ (X 0 ω)) 2 P) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ (√N)⁻¹ * (∑ m ∈ range N, φ (X m ω) - N * ∫ ω, φ (X 0 ω) ∂P)) atTop
      (fun x : ℝ ↦ √(Var[fun ω ↦ φ (X 0 ω); P]) * x) (fun _ ↦ P) (gaussianReal 0 1) :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun m ω ↦ φ (X m ω))
    (hasLaw_sqrt_mul (variance_nonneg _ _)) hL2 (hindep.comp (fun _ ↦ φ) fun _ ↦ hφ)
    (fun m ↦ (hident m).comp hφ)

/-- The exact decomposition of the scaled sample covariance:
`√N (mean(ab) - mean(b) mean(a)) = N^{-1/2} ∑ (a - μ)(b - ν) - N^{-1/2} (∑ a - N μ) (mean(b) - ν)`.
It holds for every `N`, including `N = 0` where all three terms are `0`. -/
private theorem sqrt_mul_cov_eq (a b : ℕ → ℝ) (μ ν : ℝ) (N : ℕ) :
    √N * (sampleMean (fun m ↦ a m * b m) N - sampleMean b N * sampleMean a N) =
      (√N)⁻¹ * (∑ m ∈ range N, (a m - μ) * (b m - ν) - N * 0) +
        ((√N)⁻¹ * (∑ m ∈ range N, a m - N * μ)) * (ν - sampleMean b N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hs : (√N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hN)
  have hss : (√N : ℝ) * √N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hsum : ∑ m ∈ range N, (a m - μ) * (b m - ν) =
      ∑ m ∈ range N, a m * b m - ν * ∑ m ∈ range N, a m - μ * ∑ m ∈ range N, b m +
        N * (μ * ν) := by
    simp only [sub_mul, mul_sub, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      ← mul_sum, ← sum_mul]
    ring
  rw [hsum]
  simp only [sampleMean]
  generalize ∑ m ∈ range N, a m * b m = sab
  generalize ∑ m ∈ range N, a m = sa
  generalize ∑ m ∈ range N, b m = sb
  generalize √(N : ℝ) = t at hs hss ⊢
  rw [← hss]
  field_simp
  ring

/-- The CLT for the centered product `(A - μ_A)(B - μ_B)` of independent coordinates: it has
mean `0` and variance `Var A · Var B`, so its scaled sum is asymptotically `N(0, Var A · Var B)`. -/
private theorem tendstoInDistribution_centered (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    (hnull : IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P)
    (hA : MemLp (fun ω ↦ (X 0 ω).1) 2 P) (hB : MemLp (fun ω ↦ (X 0 ω).2) 2 P) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ (√N)⁻¹ * (∑ m ∈ range N,
        ((X m ω).1 - ∫ ω, (X 0 ω).1 ∂P) * ((X m ω).2 - ∫ ω, (X 0 ω).2 ∂P) - N * 0)) atTop
      (fun x : ℝ ↦ √(Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P]) * x)
      (fun _ ↦ P) (gaussianReal 0 1) := by
  set μA := ∫ ω, (X 0 ω).1 ∂P with hμA
  set μB := ∫ ω, (X 0 ω).2 ∂P with hμB
  set vA := Var[fun ω ↦ (X 0 ω).1; P] with hvA_def
  set vB := Var[fun ω ↦ (X 0 ω).2; P] with hvB_def
  have hXm : ∀ m, AEMeasurable (X m) P := fun m ↦ (hident m).aemeasurable_fst
  have hAm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).1) P := fun m ↦ (hXm m).fst
  have hBm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).2) P := fun m ↦ (hXm m).snd
  -- The centered product `W = (A - μA)(B - μB)`: mean `0`, variance `vA vB`.
  set φW : ℝ × ℝ → ℝ := fun x ↦ (x.1 - μA) * (x.2 - μB) with hφW
  have hφW_meas : Measurable φW := by fun_prop
  have hcA : IndepFun (fun ω ↦ (X 0 ω).1 - μA) (fun ω ↦ (X 0 ω).2 - μB) P :=
    hnull.comp (φ := fun x ↦ x - μA) (ψ := fun x ↦ x - μB) (by fun_prop) (by fun_prop)
  have hcA2 : IndepFun (fun ω ↦ ((X 0 ω).1 - μA) ^ 2) (fun ω ↦ ((X 0 ω).2 - μB) ^ 2) P :=
    hnull.comp (φ := fun x ↦ (x - μA) ^ 2) (ψ := fun x ↦ (x - μB) ^ 2) (by fun_prop)
      (by fun_prop)
  have hAc : MemLp (fun ω ↦ (X 0 ω).1 - μA) 2 P := hA.sub (memLp_const μA)
  have hBc : MemLp (fun ω ↦ (X 0 ω).2 - μB) 2 P := hB.sub (memLp_const μB)
  have hmeanW : ∫ ω, φW (X 0 ω) ∂P = 0 := by
    simp only [hφW]
    rw [IndepFun.integral_fun_mul_eq_mul_integral hcA ((hAm 0).sub_const μA).aestronglyMeasurable
      ((hBm 0).sub_const μB).aestronglyMeasurable]
    rw [integral_sub (hA.integrable one_le_two) (integrable_const _), integral_const]
    simp [← hμA]
  have hW2 : Integrable (fun ω ↦ φW (X 0 ω) ^ 2) P := by
    refine (IndepFun.integrable_mul hcA2 hAc.integrable_sq hBc.integrable_sq).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp [hφW, mul_pow]
  have hWL2 : MemLp (fun ω ↦ φW (X 0 ω)) 2 P :=
    (memLp_two_iff_integrable_sq (hφW_meas.comp_aemeasurable (hXm 0)).aestronglyMeasurable).2 hW2
  have hvarW : Var[fun ω ↦ φW (X 0 ω); P] = vA * vB := by
    rw [variance_eq_integral (X := fun ω ↦ φW (X 0 ω)) (hφW_meas.comp_aemeasurable (hXm 0)), hmeanW,
      hvA_def, hvB_def, variance_eq_integral (hAm 0), variance_eq_integral (hBm 0), ← hμA, ← hμB]
    simp only [sub_zero, hφW, mul_pow]
    exact IndepFun.integral_fun_mul_eq_mul_integral hcA2
      (((hAm 0).sub_const _).pow_const 2).aestronglyMeasurable
      (((hBm 0).sub_const _).pow_const 2).aestronglyMeasurable
  have h1 := tendstoInDistribution_clt hindep hident hφW_meas hWL2
  rw [hmeanW, hvarW] at h1
  exact h1

/-- **The oracle statistic is asymptotically `χ²₁`.** With the means `μ_A, μ_B` and variances
`Var A, Var B` known instead of fitted, `(N^{-1/2} ∑ (A - μ_A)(B - μ_B))² / (Var A · Var B)`
converges in distribution to `χ²₁`: the same limit as the fitted statistic of
`tendstoInDistribution_mul_sampleCorrSq`, so fitting the nuisance parameters costs the
contrast no degree of freedom. -/
theorem tendstoInDistribution_oracleStat (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    (hnull : IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P)
    (hA : MemLp (fun ω ↦ (X 0 ω).1) 2 P) (hB : MemLp (fun ω ↦ (X 0 ω).2) 2 P)
    (hvA : 0 < Var[fun ω ↦ (X 0 ω).1; P]) (hvB : 0 < Var[fun ω ↦ (X 0 ω).2; P])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ ((√N)⁻¹ * ∑ m ∈ range N,
        ((X m ω).1 - ∫ ω, (X 0 ω).1 ∂P) * ((X m ω).2 - ∫ ω, (X 0 ω).2 ∂P)) ^ 2 /
          (Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P]))
      atTop Z (fun _ ↦ P) P' := by
  set c := Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P] with hc
  have hc0 : 0 < c := mul_pos hvA hvB
  have h := (tendstoInDistribution_centered hindep hident hnull hA hB).continuous_comp
    (g := fun x : ℝ ↦ x ^ 2 / c) (by fun_prop)
  refine tendstoInDistribution_of_hasLaw (Y := fun x : ℝ ↦ x ^ 2)
    (h.congr (fun N ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun x ↦ ?_))
    ⟨by fun_prop, gaussianReal_map_sq⟩ hZ
  · simp
  · simp only [Function.comp_apply]
    rw [mul_pow, Real.sq_sqrt hc0.le]
    field_simp

/-- **`N r² → χ²₁` under independence.** Let `X m = (A m, B m)` be i.i.d. pairs of real random
variables with `A 0 ⟂ B 0`, both square integrable with positive variance. Then `N` times the
squared sample correlation of the first `N` pairs converges in distribution to `χ²₁`. -/
theorem tendstoInDistribution_mul_sampleCorrSq (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    (hnull : IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P)
    (hA : MemLp (fun ω ↦ (X 0 ω).1) 2 P) (hB : MemLp (fun ω ↦ (X 0 ω).2) 2 P)
    (hvA : 0 < Var[fun ω ↦ (X 0 ω).1; P]) (hvB : 0 < Var[fun ω ↦ (X 0 ω).2; P])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun N ω ↦ N * sampleCorrSq (fun m ↦ (X m ω).1) (fun m ↦ (X m ω).2) N)
      atTop Z (fun _ ↦ P) P' := by
  set μA := ∫ ω, (X 0 ω).1 ∂P with hμA
  set μB := ∫ ω, (X 0 ω).2 ∂P with hμB
  set vA := Var[fun ω ↦ (X 0 ω).1; P] with hvA_def
  set vB := Var[fun ω ↦ (X 0 ω).2; P] with hvB_def
  have hXm : ∀ m, AEMeasurable (X m) P := fun m ↦ (hident m).aemeasurable_fst
  have hAm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).1) P := fun m ↦ (hXm m).fst
  have hBm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).2) P := fun m ↦ (hXm m).snd
  -- Step 1: the oracle numerator is asymptotically `N(0, vA vB)`.
  have h1 := tendstoInDistribution_centered hindep hident hnull hA hB
  -- Step 2: the correction `N^{-1/2} (∑ A - N μA) (μB - B̄)` tends to `0` in probability.
  have hAclt := tendstoInDistribution_clt hindep hident (φ := Prod.fst) measurable_fst hA
  have hBbar : TendstoInMeasure P (fun N ω ↦ μB - sampleMean (fun m ↦ (X m ω).2) N) atTop
      (fun _ ↦ 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N ↦ ?_) ?_
    · refine (aemeasurable_const.sub ?_).aestronglyMeasurable
      exact (Finset.aemeasurable_fun_sum _ fun m _ ↦ hBm m).div_const _
    · filter_upwards [ae_tendsto_sampleMean hindep hident (φ := Prod.snd) measurable_snd
        (hB.integrable one_le_two)] with ω hω
      have := (tendsto_const_nhds (x := μB)).sub hω
      rwa [← hμB, sub_self] at this
  have h2 : TendstoInMeasure P
      (fun (N : ℕ) ω ↦ ((√N)⁻¹ * (∑ m ∈ range N, (X m ω).1 - N * μA)) *
        (μB - sampleMean (fun m ↦ (X m ω).2) N)) atTop (fun _ ↦ 0) := by
    have hprod := hAclt.mul_of_tendstoInMeasure_const hBbar fun N ↦
      aemeasurable_const.sub ((Finset.aemeasurable_fun_sum _ fun m _ ↦ hBm m).div_const _)
    refine tendstoInMeasure_of_tendstoInDistribution_const (P' := gaussianReal 0 1) ?_
    exact hprod.congr (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ zero_mul _)
  -- Step 3: the scaled sample covariance is asymptotically `N(0, vA vB)`.
  have h3 : TendstoInDistribution
      (fun (N : ℕ) ω ↦ √N * (sampleMean (fun m ↦ (X m ω).1 * (X m ω).2) N -
        sampleMean (fun m ↦ (X m ω).2) N * sampleMean (fun m ↦ (X m ω).1) N))
      atTop (fun x : ℝ ↦ √(vA * vB) * x) (fun _ ↦ P) (gaussianReal 0 1) := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h1 ?_ fun N ↦ ?_
    · convert h2 using 1
      funext N ω
      simp only [Pi.sub_apply]
      rw [sqrt_mul_cov_eq (fun m ↦ (X m ω).1) (fun m ↦ (X m ω).2) μA μB N]
      ring
    · refine aemeasurable_const.mul ?_
      refine AEMeasurable.sub ?_ ?_
      · exact (Finset.aemeasurable_fun_sum _ fun m _ ↦ (hAm m).mul (hBm m)).div_const _
      · exact ((Finset.aemeasurable_fun_sum _ fun m _ ↦ hBm m).div_const _).mul
          ((Finset.aemeasurable_fun_sum _ fun m _ ↦ hAm m).div_const _)
  -- Step 4: the product of the sample variances tends to `vB vA` in probability.
  have hmeas : ∀ f : ℝ × ℝ → ℝ, Measurable f → ∀ N, AEMeasurable
      (fun ω ↦ sampleMean (fun m ↦ f (X m ω)) N) P := fun f hf N ↦
    (Finset.aemeasurable_fun_sum _ fun m _ ↦ hf.comp_aemeasurable (hXm m)).div_const _
  have hDmeas : ∀ N, AEMeasurable (fun ω ↦
      (sampleMean (fun m ↦ (X m ω).2 ^ 2) N - sampleMean (fun m ↦ (X m ω).2) N ^ 2) *
        (sampleMean (fun m ↦ (X m ω).1 ^ 2) N - sampleMean (fun m ↦ (X m ω).1) N ^ 2)) P :=
    fun N ↦ ((hmeas (fun x ↦ x.2 ^ 2) (by fun_prop) N).sub
      ((hmeas Prod.snd measurable_snd N).pow_const 2)).mul
      ((hmeas (fun x ↦ x.1 ^ 2) (by fun_prop) N).sub
      ((hmeas Prod.fst measurable_fst N).pow_const 2))
  have hD : TendstoInMeasure P
      (fun N ω ↦ (sampleMean (fun m ↦ (X m ω).2 ^ 2) N - sampleMean (fun m ↦ (X m ω).2) N ^ 2) *
        (sampleMean (fun m ↦ (X m ω).1 ^ 2) N - sampleMean (fun m ↦ (X m ω).1) N ^ 2))
      atTop (fun _ ↦ vB * vA) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N ↦ (hDmeas N).aestronglyMeasurable) ?_
    · filter_upwards [ae_tendsto_sampleMean hindep hident (φ := fun x ↦ x.2 ^ 2) (by fun_prop)
          hB.integrable_sq,
        ae_tendsto_sampleMean hindep hident (φ := Prod.snd) measurable_snd
          (hB.integrable one_le_two),
        ae_tendsto_sampleMean hindep hident (φ := fun x ↦ x.1 ^ 2) (by fun_prop)
          hA.integrable_sq,
        ae_tendsto_sampleMean hindep hident (φ := Prod.fst) measurable_fst
          (hA.integrable one_le_two)] with ω hB2 hB1 hA2 hA1
      have hvA' : vA = ∫ ω, (X 0 ω).1 ^ 2 ∂P - μA ^ 2 := variance_eq_sub hA
      have hvB' : vB = ∫ ω, (X 0 ω).2 ^ 2 ∂P - μB ^ 2 := variance_eq_sub hB
      rw [hvA', hvB']
      exact (hB2.sub (hB1.pow 2)).mul (hA2.sub (hA1.pow 2))
  -- Step 5: Slutsky, then identify the limit law.
  have hc : vB * vA ≠ 0 := (mul_pos hvB hvA).ne'
  have h5 := h3.continuous_comp (g := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    |>.div_of_tendstoInMeasure_const hc hD hDmeas
  refine tendstoInDistribution_of_hasLaw (Y := fun x : ℝ ↦ x ^ 2)
    (h5.congr (fun N ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun x ↦ ?_))
    ⟨by fun_prop, gaussianReal_map_sq⟩ hZ
  · simp only [sampleCorrSq, Function.comp_apply]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), mul_div_assoc]
  · simp only [Function.comp_apply]
    rw [mul_pow, Real.sq_sqrt (mul_pos hvA hvB).le]
    field_simp

end Asymptotics


end MathlibExt.Probability.Statistics.SampleCorrelation
