/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGrayBands
public import MathlibExt.Probability.Statistics.Survival.FineGrayPHFamily
public import MathlibExtTest.Probability.Statistics.Survival.FineGrayScoreCLT

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.FineGrayAsymptotics
open MathlibExt.Probability.Statistics.FineGrayScoreCLT
open MathlibExt.Probability.Statistics.FineGrayPHFamily
open MathlibExt.Probability.Statistics.SimultaneousBands
open MathlibExt.Probability.Statistics.FineGrayBands
open MathlibExtTest.Probability.Statistics.FineGrayScoreCLT

namespace MathlibExtTest.Probability.Statistics.FineGrayBands

/-! ### The CIF map, computed from the definition -/

/-- Boundary: a zero baseline gives a zero CIF. -/
example (x b : ℝ) : fgCif x b (0 : Fin 3 → ℝ) = 0 := by
  funext j
  simp [fgCif]

/-- Boundary: at covariate value `0` the coefficient drops out, `F_j = 1 - exp (-Λ j)`. -/
example (b : ℝ) (Λ : Fin 3 → ℝ) (j : Fin 3) : fgCif 0 b Λ j = 1 - Real.exp (-Λ j) := by
  simp [fgCif]

/-- A concrete value: `exp (log 2 · 1) = 2` and `Λ = log 2`, so `F = 1 - exp (-2 log 2) = 3/4`. -/
example : fgCif 1 (Real.log 2) (fun _ : Unit => Real.log 2) () = 3 / 4 := by
  simp only [fgCif, mul_one, Real.exp_log two_pos]
  rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log two_pos]
  norm_num

/-- The slope `s_j = (1 - F_j) exp (b x)` at the same point: `(1/4) · 2 = 1/2`. -/
example : fgCifSlope 1 (Real.log 2) (fun _ : Unit => Real.log 2) () = 1 / 2 := by
  simp only [fgCifSlope, mul_one, Real.exp_log two_pos]
  rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log two_pos]
  norm_num

/-- Boundary: at a zero baseline a coefficient perturbation has no first-order effect on the
CIF; only the baseline perturbation `H` enters, scaled by `exp (b x)`. -/
example (x b h : ℝ) (H : Fin 2 → ℝ) :
    fgCifDeriv x b 0 (h, H) = fun j => Real.exp (b * x) * H j := by
  funext j
  simp [fgCifDeriv_apply, fgCifSlope]

/-- The derivative on a concrete direction, from `fgCifDeriv_apply`: at `x = 1`, `b = log 2`,
`Λ = log 2`, the direction `(1, 0)` has image `s · Λ = (1/2) log 2`. -/
example : fgCifDeriv 1 (Real.log 2) (fun _ : Unit => Real.log 2) (1, 0) () =
    Real.log 2 / 2 := by
  rw [fgCifDeriv_apply]
  simp only [fgCifSlope, mul_one, Real.exp_log two_pos, Pi.zero_apply, add_zero]
  rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log two_pos]
  ring

/-- The weighted sup of a rank-one vector, computed from the definition:
`max(|6| / 2, |-3| / 1) = 3`, the value `weightedSup_abs_mul` gives. -/
example : weightedSup (fun j => |(![2, -1] : Fin 2 → ℝ) j|) (fun j => (![2, -1] : Fin 2 → ℝ) j * 3)
    = 3 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    fin_cases i <;> norm_num
  · have h := norm_le_pi_norm (fun i => (![2, -1] : Fin 2 → ℝ) i * 3 / |(![2, -1] : Fin 2 → ℝ) i|) 0
    norm_num at h
    exact h

example : weightedSup (fun j => |(![2, -1] : Fin 2 → ℝ) j|) (fun j => (![2, -1] : Fin 2 → ℝ) j * 3)
    = |3| :=
  weightedSup_abs_mul (fun j => by fin_cases j <;> norm_num) 3

/-! ### `fgCif` is the model CIF: the explicit PH family

`FineGrayPHFamily` is a proportional subdistribution hazards model with baseline hazard
`λ₀(t) = 1 / (1 + t)²`; on the grid `t = (1, 2)` its CIF at covariate value `x` is `fgCif`. -/

example (b x : ℝ) :
    (fun j => cif (phMeasure (fun _ : Fin 1 => b) fun _ => x) phTime phCause true
        ((![1, 2] : Fin 2 → ℝ) j)) =
      fgCif x b (fun j => ∫ s in (0 : ℝ)..(![1, 2] : Fin 2 → ℝ) j, phBaseline s) := by
  have ht : ∀ j, 0 ≤ (![1, 2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> norm_num
  exact cif_eq_fgCif (isPropSubdistHazards_phMeasure (fun _ : Fin 1 => b)) measurable_phTime
    measurableSet_phCause x (ae_phTime_pos _ _) _ ht
    (fun _ => phCifDeriv (Real.exp ((fun _ : Fin 1 => b) ⬝ᵥ fun _ => x)))
    (fun j => continuousOn_cif_phMeasure _ _ _)
    (fun j s hs => hasDerivAt_cif_phMeasure _ _ hs.1)
    (fun j => intervalIntegrable_phCifDeriv _ (ht j))
    (fun j => cif_phMeasure_lt_one _ _ (ht j))

/-! ### Non-vacuity of the known-baseline band at `σ² = 1/18 > 0`

The concrete paired product model of `FineGrayScoreCLT` satisfies `FineGrayConditions` with a
Gaussian score limit of variance `1/18` and information limit `v = 1/12`. On the grid `Fin 2` with
baseline values `Λ₀ = (1, 2)` and covariate value `1`, the band with the natural weights has
limiting coverage `P(|Z / v| ≤ q)`, `Z ~ N(0, 1/18)`. -/

/-- Baseline values on the grid. -/
def Λ₁ : Fin 2 → ℝ := ![1, 2]

/-- The natural weights `|s_j · 1 · Λ₀_j|`. -/
noncomputable def wU : Fin 2 → ℝ := fun j => |fgCifSlope 1 β₀U Λ₁ j * (1 * Λ₁ j)|

/-- The two-point set `{|ω / a| = q}` is null for the nondegenerate Gaussian `N(0, 1/18)`. -/
theorem gaussianReal_abs_div_eq_null {a q : ℝ} (ha : a ≠ 0) :
    gaussianReal 0 (1 / 18) {ω : ℝ | |ω / a| = q} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := (1 / 18 : NNReal)) (by norm_num)
  refine measure_mono_null (t := {q * a, -q * a}) (fun ω hω => ?_)
    ((Set.toFinite _).measure_zero _)
  have hω : |ω / a| = q := hω
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases le_total 0 (ω / a) with h | h
  · rw [abs_of_nonneg h] at hω
    exact Or.inl (by rw [← hω, div_mul_cancel₀ ω ha])
  · rw [abs_of_nonpos h] at hω
    exact Or.inr (by rw [← hω, neg_neg, div_mul_cancel₀ ω ha])

/-- **The known-baseline Fine–Gray CIF band in the concrete model**: for any estimator that
maximizes the weighted log partial likelihood whenever a maximizer exists, the band
`fgCif 1 (βhat n) Λ₀ ± q · wU / √n` covers `fgCif 1 (log 2) Λ₀` at both grid points with
probability tending to `P(|Z / (1/12)| ≤ q)`, `Z ~ N(0, 1/18)`. -/
theorem tendsto_coverage_fgCifBand_U (βhat : ℕ → (ℕ → Fin 4 × Fin 4) → ℝ)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1)
        (pairCov n)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1)
          (pairCov n)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) (pairModel μU)) (q : ℝ) :
    Tendsto (fun n => pairModel μU {ω | fgCif 1 β₀U Λ₁ ∈
        simultaneousBand (fgCif 1 (βhat n ω) Λ₁) wU q n}) atTop
      (𝓝 (gaussianReal 0 (1 / 18) {ω | |id ω / ((1 / 12 : NNReal) : ℝ)| ≤ q})) := by
  have h := fineGrayConditions_pair (G := fun _ _ _ => 1) (r := 1) (measurableSet_any _)
    (measurableSet_any _) (by rw [pairProbB_U]; norm_num) hβ₀U (fun _ _ _ => zero_le_one)
    one_pos hasLaw_id_U
  have hv : ((pairV μU εA εB 0 β₀U : NNReal) : ℝ) ≠ 0 := by rw [pairV_U]; norm_num
  have key := tendsto_coverage_fgCifBand_knownBaseline_abs h hβhat hβhat_meas one_ne_zero
    (Λ₀ := Λ₁) (fun j => by fin_cases j <;> norm_num [Λ₁])
    (ŵ := fun _ _ => wU) (tendstoInMeasure_const_self _) (fun _ => aemeasurable_const)
    (qhat := fun _ _ => q) (tendstoInMeasure_const_self _) (fun _ => aemeasurable_const)
    (gaussianReal_abs_div_eq_null hv)
  rw [pairV_U] at key
  exact key

/-- The no-atom hypothesis of the band theorem holds in the concrete model, here at `q = 1`. -/
example : gaussianReal 0 (1 / 18) {ω : ℝ | |ω / ((1 / 12 : NNReal) : ℝ)| = 1} = 0 :=
  gaussianReal_abs_div_eq_null (by norm_num)

end MathlibExtTest.Probability.Statistics.FineGrayBands
