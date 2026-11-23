/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FisherInformation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Tests for Fisher information, the Cramér–Rao bound, and consistency of maximum likelihood

* A two-point model `p θ = ((1 + sin θ) / 2, (1 - sin θ) / 2)` under counting measure satisfies
  every hypothesis of `cramerRao` at `θ = 0` (including `0 < I(0)`, with `I(0) = 1`); the
  indicator estimator attains the bound `1 / 4` with equality.
* Boundary case: for a constant family `I = 0` and the left side of the bound is the junk
  value `0`.
* The Bernoulli family `p θ = ((2 - θ) / 3, (1 + θ) / 3)` on the parameter interval `[0, 1]`
  satisfies every hypothesis of `ae_tendsto_maximumLikelihood` for an i.i.d. sample on the
  product space `ℕ → Fin 2`, with an actual maximizer of the likelihood (by compactness); the
  theorem gives its almost sure consistency.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Statistics.FisherInformation

namespace FisherInformationTest

/-! ## Cramér–Rao on a two-point model -/

/-- The signs `+1, -1` of the two outcomes. -/
noncomputable def sgn : Fin 2 → ℝ := ![1, -1]

/-- The two-point family `p θ x = (1 + sgn x * sin θ) / 2`. -/
noncomputable def pSin (θ : ℝ) (x : Fin 2) : ℝ := (1 + sgn x * Real.sin θ) / 2

/-- The indicator of the first outcome, an unbiased estimator of `(1 + sin θ) / 2`. -/
noncomputable def tInd (x : Fin 2) : ℝ := (1 + sgn x) / 2

/-- The estimand `g θ = (1 + sin θ) / 2`. -/
noncomputable def gSin (θ : ℝ) : ℝ := (1 + Real.sin θ) / 2

theorem pSin_nonneg (θ : ℝ) (x : Fin 2) : 0 ≤ pSin θ x := by
  fin_cases x <;> simp [pSin, sgn] <;> linarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]

theorem hasDerivAt_pSin (θ : ℝ) (x : Fin 2) :
    HasDerivAt (fun θ' => pSin θ' x) (sgn x * Real.cos θ / 2) θ :=
  (((Real.hasDerivAt_sin θ).const_mul (sgn x)).const_add 1).div_const 2

theorem deriv_pSin_zero (x : Fin 2) : deriv (fun θ' => pSin θ' x) 0 = sgn x / 2 := by
  rw [(hasDerivAt_pSin 0 x).deriv, Real.cos_zero, mul_one]

theorem integral_pSin (θ : ℝ) : ∫ x, pSin θ x ∂Measure.count = 1 := by
  simp [pSin, sgn, Fin.sum_univ_two]; ring

theorem integral_tInd_pSin (θ : ℝ) : ∫ x, tInd x * pSin θ x ∂Measure.count = gSin θ := by
  simp [pSin, sgn, tInd, gSin, Fin.sum_univ_two]

theorem fisherInformation_pSin_zero : fisherInformation Measure.count pSin 0 = 1 := by
  simp only [fisherInformation, deriv_pSin_zero, integral_count, Fin.sum_univ_two]
  simp [pSin, sgn]; norm_num

theorem deriv_gSin_zero : deriv gSin 0 = 1 / 2 := by
  have h : HasDerivAt gSin (Real.cos 0 / 2) 0 :=
    ((Real.hasDerivAt_sin 0).const_add 1).div_const 2
  rw [h.deriv, Real.cos_zero]

theorem variance_tInd_zero :
    ∫ x, (tInd x - gSin 0) ^ 2 * pSin 0 x ∂Measure.count = 1 / 4 := by
  simp [tInd, gSin, pSin, sgn, Fin.sum_univ_two]; norm_num

/-- Every hypothesis of `cramerRao` holds for the two-point model at `θ = 0`, so the bound
`g'(0)² / I(0) ≤ Var_0 T` applies; here both sides equal `1 / 4`. -/
theorem cramerRao_pSin :
    deriv gSin 0 ^ 2 / fisherInformation Measure.count pSin 0 ≤
      ∫ x, (tInd x - gSin 0) ^ 2 * pSin 0 x ∂Measure.count :=
  cramerRao (fun θ x => pSin_nonneg θ x) (Integrable.of_finite).aestronglyMeasurable
    (Eventually.of_forall integral_pSin) (fun x => (hasDerivAt_pSin 0 x).differentiableAt)
    (Integrable.of_finite).aestronglyMeasurable Integrable.of_finite
    (by rw [fisherInformation_pSin_zero]; exact one_pos)
    (Integrable.of_finite).aestronglyMeasurable Integrable.of_finite
    (Eventually.of_forall integral_tInd_pSin)
    (by
      have h : (fun θ' => ∫ x, pSin θ' x ∂Measure.count) = fun _ => 1 :=
        funext integral_pSin
      rw [h]
      simp only [deriv_pSin_zero, integral_count, Fin.sum_univ_two]
      convert hasDerivAt_const (0 : ℝ) (1 : ℝ) using 1
      simp [sgn]; norm_num)
    (by
      have h : (fun θ' => ∫ x, tInd x * pSin θ' x ∂Measure.count) = gSin :=
        funext integral_tInd_pSin
      rw [h]
      simp only [deriv_pSin_zero, integral_count, Fin.sum_univ_two]
      have hg : HasDerivAt gSin (Real.cos 0 / 2) 0 :=
        ((Real.hasDerivAt_sin 0).const_add 1).div_const 2
      convert hg using 1
      simp [tInd, sgn])

/-- The indicator estimator is efficient: the Cramér–Rao bound is attained. -/
theorem cramerRao_pSin_eq :
    deriv gSin 0 ^ 2 / fisherInformation Measure.count pSin 0 =
      ∫ x, (tInd x - gSin 0) ^ 2 * pSin 0 x ∂Measure.count := by
  rw [deriv_gSin_zero, fisherInformation_pSin_zero, variance_tInd_zero]; norm_num

/-- Boundary case: a constant family has zero Fisher information, and the left side of the
bound is the junk value `g'(θ)² / 0 = 0`. -/
example (g : ℝ → ℝ) :
    deriv g 0 ^ 2 / fisherInformation Measure.count (fun _ (_ : Fin 2) => (1 / 2 : ℝ)) 0 =
      0 := by
  simp [fisherInformation]

/-! ## Wald consistency on the parameter interval `[0, 1]` -/

/-- The parameter space `[0, 1]`. -/
abbrev Θi := Set.Icc (0 : ℝ) 1

/-- The true parameter `0`. -/
def θzero : Θi := ⟨0, by norm_num, by norm_num⟩

/-- The Bernoulli densities `p θ = ((2 - θ) / 3, (1 + θ) / 3)` on `Fin 2`, `θ ∈ [0, 1]`. -/
noncomputable def pLin (θ : Θi) (x : Fin 2) : ℝ :=
  if x = 0 then (2 - (θ : ℝ)) / 3 else (1 + (θ : ℝ)) / 3

theorem pLin_pos (θ : Θi) (x : Fin 2) : 0 < pLin θ x := by
  obtain ⟨h0, h1⟩ := θ.2
  unfold pLin; split_ifs <;> linarith

theorem continuous_pLin (x : Fin 2) : Continuous fun θ => pLin θ x := by
  by_cases hx : x = 0 <;> simp only [pLin, hx, ↓reduceIte] <;> fun_prop

theorem integral_pLin (θ : Θi) : ∫ x, pLin θ x ∂Measure.count = 1 := by
  simp [pLin, Fin.sum_univ_two]; ring

theorem pLin_ident (θ : Θi) (h : pLin θ =ᵐ[Measure.count] pLin θzero) : θ = θzero := by
  have h1 := Measure.ae_count_iff.1 h 1
  simp only [pLin, θzero, one_ne_zero, ↓reduceIte] at h1
  exact Subtype.ext (by simp only [θzero]; linarith)

/-- The constant envelope `log (2/3) - log (1/3)`. -/
noncomputable def kLin : Fin 2 → ℝ := fun _ => Real.log (2 / 3) - Real.log (1 / 3)

theorem logRatio_le_kLin (θ : Θi) (x : Fin 2) :
    Real.log (pLin θ x) - Real.log (pLin θzero x) ≤ kLin x := by
  obtain ⟨h0, h1⟩ := θ.2
  have hl : Real.log (1 / 3) ≤ Real.log (2 / 3) := Real.log_le_log (by norm_num) (by norm_num)
  by_cases hx : x = 0
  · have : Real.log ((2 - (θ : ℝ)) / 3) ≤ Real.log (2 / 3) :=
      Real.log_le_log (by linarith) (by linarith)
    simp only [pLin, θzero, hx, ↓reduceIte, kLin, sub_zero]
    linarith
  · have : Real.log ((1 + (θ : ℝ)) / 3) ≤ Real.log (2 / 3) :=
      Real.log_le_log (by linarith) (by linarith)
    simp only [pLin, θzero, hx, ↓reduceIte, kLin, add_zero]
    linarith

instance isProbabilityMeasure_lawOf_pLin :
    IsProbabilityMeasure (lawOf Measure.count pLin θzero) := by
  constructor
  rw [lawOf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
    tsum_fintype, Fin.sum_univ_two, ← ENNReal.ofReal_add (pLin_pos _ 0).le (pLin_pos _ 1).le]
  simp [pLin, θzero]; norm_num

/-- The law of the i.i.d. sample: the infinite product of `lawOf count pLin θzero`, observed
through its coordinates. -/
noncomputable def sampleP : Measure (ℕ → Fin 2) :=
  Measure.infinitePi fun _ => lawOf Measure.count pLin θzero

instance : IsProbabilityMeasure sampleP := by unfold sampleP; infer_instance

/-- The log-likelihood of `θ` on the first `n` coordinates. -/
noncomputable def logLik (n : ℕ) (ω : ℕ → Fin 2) (θ : Θi) : ℝ :=
  ∑ i ∈ Finset.range n, Real.log (pLin θ (ω i))

theorem continuous_logLik (n : ℕ) (ω : ℕ → Fin 2) : Continuous (logLik n ω) :=
  continuous_finsetSum _ fun i _ =>
    (continuous_pLin (ω i)).log fun θ => (pLin_pos θ (ω i)).ne'

theorem exists_mle (n : ℕ) (ω : ℕ → Fin 2) : ∃ θ ∈ Set.univ, IsMaxOn (logLik n ω) Set.univ θ :=
  isCompact_univ.exists_isMaxOn ⟨θzero, Set.mem_univ _⟩ (continuous_logLik n ω).continuousOn

/-- A maximizer of the likelihood over `[0, 1]` (it exists by compactness). -/
noncomputable def mle (n : ℕ) (ω : ℕ → Fin 2) : Θi := (exists_mle n ω).choose

theorem logLik_le_mle (n : ℕ) (ω : ℕ → Fin 2) (θ : Θi) :
    logLik n ω θ ≤ logLik n ω (mle n ω) :=
  (exists_mle n ω).choose_spec.2 (Set.mem_univ θ)

/-- Every hypothesis of `ae_tendsto_maximumLikelihood` holds for this model on `[0, 1]`, so the
maximum-likelihood estimator is almost surely consistent. -/
theorem ae_tendsto_mle :
    ∀ᵐ ω ∂sampleP, Tendsto (fun n => mle n ω) atTop (𝓝 θzero) :=
  ae_tendsto_maximumLikelihood (p := pLin) pLin_pos (fun _ => measurable_of_finite _)
    continuous_pLin integral_pLin pLin_ident Integrable.of_finite logRatio_le_kLin
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩)
    (iIndepFun_infinitePi (P := fun _ => lawOf Measure.count pLin θzero) (X := fun _ => id)
      fun _ => measurable_id)
    (fun n ω θ => logLik_le_mle n ω θ)

end FisherInformationTest
