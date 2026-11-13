/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountEfficiency

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function
open scoped RealInnerProductSpace
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExtTest.Biology.Omics.HierarchicalCountEfficiency

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-! ### The per-count score, its derivative and the Fisher information -/

/-- One zero count at `a = b = σ = 1`: the score is `(log (1/2), 1 - 1/2) = (-log 2, 1/2)`,
computed from the definition. -/
example : countScore 1 !₂[1, 1] 0 = !₂[-log 2, 1 / 2] := by
  ext i
  fin_cases i
  · simp [countScore, digammaIncrement, ← log_inv]
    norm_num
  · simp [countScore]
    norm_num

/-- It is the gradient of `log (marginalLik a b 1 0) = a log (b / (b + 1))` at `(1, 1)`, whose
partial derivatives are `log (1/2)` and `a/b - a/(b+1) = 1/2`. -/
example : MathlibExt.Probability.Statistics.VectorInference.score
    (fun (t : E₂) (j : ℕ) => marginalLik (t 0) (t 1) 1 j) !₂[1, 1] 0 = !₂[-log 2, 1 / 2] := by
  rw [score_marginalLik_eq_countScore one_pos (by simp) (by simp)]
  ext i
  fin_cases i
  · simp [countScore, digammaIncrement, ← log_inv]
    norm_num
  · simp [countScore]
    norm_num

/-- Summed over the sample `(0, 1)` at `a = b = σ = 1`, the rate components are
`(1 - 1/2) + (1 - 1) = 1/2`, which is `rateScore`. -/
example : (∑ i, countScore 1 !₂[1, 1] (![0, 1] i)) 1 =
    rateScore 1 1 (fun _ : Fin 2 => (1 : ℝ)) ![0, 1] := by
  rw [sum_countScore]
  simp

example : rateScore 1 1 (fun _ : Fin 2 => (1 : ℝ)) ![0, 1] = 1 / 2 := by
  norm_num [rateScore, Fin.sum_univ_two]

/-- The trigamma increment at `a = 1`, `k = 3` is `1 + 1/4 + 1/9 = 49/36`. -/
example : trigammaIncrement 1 3 = 49 / 36 := by
  norm_num [trigammaIncrement, sum_range_succ]

/-- The score derivative at `a = b = σ = 1`, `k = 1`, on the first basis vector: its first column
`(-1, 1 - 1/2)`. -/
example : countHessian 1 !₂[1, 1] 1 !₂[1, 0] = !₂[-1, 1 / 2] := by
  ext i
  fin_cases i <;> simp [countHessian, trigammaIncrement]
  all_goals norm_num

example : HasFDerivAt (fun t => countScore 1 t 1) (countHessian 1 !₂[1, 1] 1) !₂[1, 1] :=
  hasFDerivAt_countScore zero_le_one (by simp) (by simp) 1

/-- **Boundary of positive definiteness.** At `a = b = σ = 1` the threshold is
`σ / (a (b + σ)) = 1/2`; at `τ = 1/2` the information `[[1/2, -1/2], [-1/2, 1/2]]` is singular,
with `⟪I u, u⟫ = 0` for `u = (1, 1)`, computed from the definition. So the strict inequality
in `isUnit_countFisherInfo` cannot be relaxed. -/
example : ⟪countFisherInfo 1 1 1 (1 / 2) !₂[1, 1], !₂[1, 1]⟫ = 0 := by
  rw [real_inner_comm, countFisherInfo, Matrix.inner_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

example : ¬ IsUnit (countFisherInfo 1 1 1 (1 / 2)) := by
  intro h
  have h0 : countFisherInfo 1 1 1 (1 / 2) !₂[1, 1] = 0 := by
    ext i
    fin_cases i <;> simp [countFisherInfo]
    all_goals norm_num
  have := MathlibExt.Probability.Statistics.VectorInference.inverse_apply_apply h !₂[1, 1]
  rw [h0, map_zero] at this
  have h1 := congrArg (fun v : E₂ => v 0) this
  simp at h1

/-- Above the threshold the information is invertible. -/
example : IsUnit (countFisherInfo 1 1 1 1) :=
  isUnit_countFisherInfo one_pos one_pos one_pos (by norm_num)

/-! ### A two-point count law with the negative binomial mean and second moment -/

/-- The two-point law on `Bool`: `false ↦ 0` with probability `2/3`, `true ↦ 3` with `1/3`. -/
noncomputable def ν : Measure Bool :=
  (2 / 3 : ENNReal) • Measure.dirac false + (1 / 3 : ENNReal) • Measure.dirac true

instance : IsProbabilityMeasure ν := ⟨by
  simp only [ν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]; norm_num; exact ENNReal.div_self (by norm_num) (by norm_num)⟩

/-- The count read from one coordinate. -/
def g : Bool → ℕ := fun b => if b then 3 else 0

private lemma hg : Measurable g := measurable_of_finite g

/-- The count law `(2/3) δ₀ + (1/3) δ₃` on `ℕ`. It has mean `1` and second moment `3`, the
mean `σ a / b` and second moment `m + m² / a + m²` of `NB(1, 1)` at `a = b = σ = 1`, but it is
not negative binomial. -/
noncomputable def μX : Measure ℕ := ν.map g

instance : IsProbabilityMeasure μX := by rw [μX]; infer_instance

private lemma integral_μX (F : ℕ → ℝ) : ∫ k, F k ∂μX = 2 / 3 * F 0 + 1 / 3 * F 3 := by
  rw [μX, integral_map hg.aemeasurable (measurable_of_countable F).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp [ν, Measure.real, g, ENNReal.toReal_div]
  ring

private lemma integrable_μX (F : ℕ → ℝ) : Integrable F μX := by
  rw [μX, integrable_map_measure (measurable_of_countable F).aestronglyMeasurable hg.aemeasurable]
  exact Integrable.of_finite

private lemma mean_μX : ∫ k, (k : ℝ) ∂μX = 1 * 1 / 1 := by
  rw [integral_μX]; norm_num

private lemma sq_μX : ∫ k, (k : ℝ) ^ 2 ∂μX =
    1 * 1 / 1 + (1 * 1 / 1) ^ 2 / 1 + (1 * 1 / 1) ^ 2 := by
  rw [integral_μX]; norm_num

/-- The expected score derivative under this law is `-countFisherInfo 1 1 1 τ` with
`τ = (1/3) (1 + 1/4 + 1/9) = 49/108`. Independently of `integral_countHessian`, its rate entry is
`E[(1 + K)/4 - 1] = (1 + 1)/4 - 1 = -1/2 = -a σ / (b² (b + σ))`. -/
example : ∫ k, countHessian 1 !₂[1, 1] k ∂μX = -countFisherInfo 1 1 1 (49 / 108) := by
  have h := integral_countHessian (σ := 1) (θ₀ := !₂[1, 1]) (by simp) (by simp) zero_le_one
    (integrable_μX _) (by simpa using mean_μX)
  have hτ : ∫ k, trigammaIncrement 1 k ∂μX = 49 / 108 := by
    rw [integral_μX]; norm_num [trigammaIncrement, sum_range_succ]
  simpa [hτ] using h

example : ∫ k, ((1 + (k : ℝ)) / (1 + 1) ^ 2 - 1 / 1 ^ 2) ∂μX = -(1 * 1 / (1 ^ 2 * (1 + 1))) := by
  rw [integral_μX]; norm_num

/-- For this law the profile-information condition fails (`49/108 < 1/2`): the condition is a
genuine restriction on the count law, met by negative binomial laws but not by every law with
the right first two moments. -/
example : (49 / 108 : ℝ) < 1 / (1 * (1 + 1)) := by norm_num

/-! ### The moment estimating equations -/

/-- The overdispersed sample `(0, 3)` (`M = 3/2`, `V = 9/4`) has moment estimates
`momShape = (9/4) / (3/4) = 3` and `momRate = (3/2) / (3/4) = 2` at `σ = 1`. -/
example : momShape (3 / 2) (9 / 4) = 3 ∧ momRate 1 (3 / 2) (9 / 4) = 2 := by
  norm_num [momShape, momRate]

/-- At `(3, 2)` the moment estimating function of the two counts sums to zero, computed from the
definition: `g(0) = (-3, -18)`, `g(3) = (3, 18)`. -/
example : momEstFun 1 !₂[3, 2] 0 + momEstFun 1 !₂[3, 2] 3 = 0 := by
  ext i
  fin_cases i <;> simp [momEstFun] <;> norm_num

/-- The sample `(0, 3)` as a sequence. -/
def kk : ℕ → ℕ := fun i => if i = 0 then 0 else 3

/-- `sum_momEstFun_mom_eq_zero` on the same sample; its sample mean and variance are `3/2` and
`9/4`, so the root is `(3, 2)` as computed above. -/
example : ∑ i ∈ range 2, momEstFun 1 !₂[momShape (3 / 2) (9 / 4), momRate 1 (3 / 2) (9 / 4)]
    (kk i) = 0 := by
  have hM : ((2 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range 2, (kk i : ℝ) = 3 / 2 := by
    norm_num [kk, sum_range_succ]
  have hQ : ((2 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range 2, (kk i : ℝ) ^ 2 = 9 / 2 := by
    norm_num [kk, sum_range_succ]
  have h := sum_momEstFun_mom_eq_zero 1 (n := 2) kk (by rw [hM]; norm_num)
    (by rw [hM, hQ]; norm_num)
  rw [hM, hQ] at h
  norm_num at h ⊢
  exact h

/-- **Overdispersion is needed.** For the underdispersed sample `(1, 1)` (`V = 0 < M = 1`) the
moment estimating equations at `σ = 1` have no solution with `a > 0`: the first forces `b = a`,
and then the second is `-2a² - 2a ≠ 0`. -/
example {a b : ℝ} (ha : 0 < a) : momEstFun 1 !₂[a, b] 1 + momEstFun 1 !₂[a, b] 1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : E₂ => v 0) h
  have h1 := congrArg (fun v : E₂ => v 1) h
  simp [momEstFun] at h0 h1
  have hb : b = a := by linarith
  subst hb
  nlinarith

/-- The Jacobian of the moment equations under the two-point law is `momJacobian 1 1 1`
`= [[-1, 1], [-4, 5]]`, with determinant `-1 = -σ³ a / b`. -/
example : ∫ k, momEstDeriv 1 !₂[1, 1] k ∂μX = momJacobian 1 1 1 :=
  integral_momEstDeriv one_pos one_pos (integrable_μX _) mean_μX sq_μX

example : Matrix.det !![(-1 : ℝ), 1 * 1 / 1; -(1 * 1) - 1 ^ 2 - 2 * 1 ^ 2 * 1,
    1 * 1 + 2 * 1 ^ 2 * 1 * (1 + 1) / 1] = -(1 ^ 3 * 1 / 1) := by
  rw [Matrix.det_fin_two_of]; norm_num

example : IsUnit (momJacobian 1 1 1) := isUnit_momJacobian one_pos one_pos one_pos

/-- **Boundary `σ = 0`.** Without exposure the Jacobian is the zero operator, so `hσ` cannot be
dropped from `isUnit_momJacobian`. -/
example (a b : ℝ) : momJacobian a b 0 = 0 := by
  rw [momJacobian]
  convert map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2))
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The moment equations hold at the truth for the two-point law; independently,
`(2/3) g(0) + (1/3) g(3) = (2/3)(-1, -3) + (1/3)(2, 6) = 0` at `a = b = σ = 1`. -/
example : ∫ k, momEstFun 1 !₂[1, 1] k ∂μX = 0 :=
  integral_momEstFun one_pos (integrable_μX _) mean_μX sq_μX

example : (2 / 3 : ℝ) • momEstFun 1 !₂[1, 1] 0 + (1 / 3 : ℝ) • momEstFun 1 !₂[1, 1] 3 = 0 := by
  ext i
  fin_cases i <;> simp [momEstFun] <;> norm_num

/-! ### Asymptotic normality of the moment estimator for an i.i.d. sequence -/

/-- I.i.d. coordinates with law `ν`. -/
noncomputable abbrev P : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => ν)

/-- The `i`-th count. -/
def X (i : ℕ) (ω : ℕ → Bool) : ℕ := g (ω i)

private lemma hasLaw_X (i : ℕ) : HasLaw (X i) μX P :=
  (hasLaw_map hg.aemeasurable).comp
    (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) i).hasLaw

private lemma iIndepFun_X : iIndepFun X P :=
  iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => g) (fun _ => hg)

/-- **`tendstoInDistribution_mom` is non-vacuous.** For i.i.d. counts with the two-point law
above, every count-side hypothesis is discharged: the moment estimates are asymptotically normal
with limit `-J⁻¹ Y` for any Gaussian vector `Y` with covariance `E[g gᵀ]`. -/
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → E₂} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪momEstFun 1 !₂[1, 1] k, t⟫ ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (momEstimator 1 X n ω - !₂[1, 1])) atTop
      (fun ω => -Ring.inverse (momJacobian 1 1 1) (Y ω)) (fun _ => P) P' :=
  tendstoInDistribution_mom one_pos one_pos one_pos hasLaw_X iIndepFun_X (integrable_μX _)
    mean_μX sq_μX hY_meas hY

/-! ### A count law satisfying the hypotheses of `tendstoInDistribution_countMLE`

At `a = b = σ = 1`, the three-point law `p₀ δ₀ + p₁ δ₁ + p₃ δ₃` with `p₃ = 6 (1 - log 2) / 7`,
`p₁ = 1 - 3 p₃`, `p₀ = 2 p₃` has `E K = 1` and `E[∑_{j<K} 1/(1+j)] = log 2`, so both score
equations hold at `(1, 1)`, and `τ = 1 - (59/42)(1 - log 2) ≈ 0.569 > 1/2`, so the
profile-information condition holds too. (Witness due to the T118 reviewer.) -/

/-- The weight of `3`. -/
noncomputable def pW3 : ℝ := 6 * (1 - log 2) / 7
/-- The weight of `1`. -/
noncomputable def pW1 : ℝ := 1 - 3 * pW3
/-- The weight of `0`. -/
noncomputable def pW0 : ℝ := 1 - pW1 - pW3

private lemma hlog : 0.6931471803 < log 2 ∧ log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

private lemma pW3_pos : 0 < pW3 := by have := hlog; unfold pW3; linarith
private lemma pW1_pos : 0 < pW1 := by have := hlog; unfold pW1 pW3; linarith
private lemma pW0_pos : 0 < pW0 := by have := hlog; unfold pW0 pW1 pW3; linarith

/-- The three-point count law. -/
noncomputable def μW : Measure ℕ :=
  ENNReal.ofReal pW0 • Measure.dirac 0 + ENNReal.ofReal pW1 • Measure.dirac 1 +
    ENNReal.ofReal pW3 • Measure.dirac 3

private lemma integrable_μW {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) :
    Integrable F μW := by
  unfold μW
  refine ((Integrable.smul_measure ?_ ENNReal.ofReal_ne_top).add_measure
    (Integrable.smul_measure ?_ ENNReal.ofReal_ne_top)).add_measure
    (Integrable.smul_measure ?_ ENNReal.ofReal_ne_top) <;>
  exact integrable_dirac enorm_lt_top

private lemma integral_μW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℕ → E) : ∫ k, F k ∂μW = pW0 • F 0 + pW1 • F 1 + pW3 • F 3 := by
  have i := fun c (k : ℕ) => (integrable_dirac (a := k) (f := F) enorm_lt_top).smul_measure
    (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top
  unfold μW
  rw [integral_add_measure ((i _ _).add_measure (i _ _)) (i _ _),
    integral_add_measure (i _ _) (i _ _), integral_smul_measure, integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal pW0_pos.le, ENNReal.toReal_ofReal pW1_pos.le,
    ENNReal.toReal_ofReal pW3_pos.le]

instance : IsProbabilityMeasure μW := ⟨by
  unfold μW
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add pW0_pos.le pW1_pos.le,
    ← ENNReal.ofReal_add (by linarith [pW0_pos, pW1_pos]) pW3_pos.le]
  simp only [pW0]; ring_nf; simp⟩

/-- The score equations hold at `(1, 1)`: the shape component is
`p₁ + p₃ (1 + 1/2 + 1/3) - log 2 = 0` and the rate component is `1 - (1 + E K)/2 = 0`. -/
private lemma integral_countScore_μW : ∫ k, countScore 1 !₂[1, 1] k ∂μW = 0 := by
  rw [integral_μW]
  ext i
  fin_cases i
  · simp [countScore, digammaIncrement, sum_range_succ, pW0, pW1, pW3]
    norm_num; ring_nf
  · simp [countScore, pW0, pW1]; norm_num; ring

/-- The profile-information condition `τ > 1/2` holds: `τ = p₁ + p₃ (49/36) ≈ 0.569`. -/
private lemma profile_μW : 1 / ((!₂[1, 1] : E₂) 0 * ((!₂[1, 1] : E₂) 1 + 1)) <
    ∫ k, trigammaIncrement ((!₂[1, 1] : E₂) 0) k ∂μW := by
  rw [integral_μW]
  have := hlog
  simp [trigammaIncrement, sum_range_succ, pW1, pW3]
  norm_num
  linarith

/-- Independently of the theorems, the mean is `p₁ + 3 p₃ = 1 = σ a / b`. -/
example : ∫ k, (k : ℝ) ∂μW = 1 := by
  rw [integral_μW]; simp [pW1]; ring

/-- I.i.d. counts with law `μW`. -/
noncomputable abbrev PW : Measure (ℕ → ℕ) := Measure.infinitePi (fun _ : ℕ => μW)

/-- The `i`-th count. -/
def XW (i : ℕ) (ω : ℕ → ℕ) : ℕ := ω i

private lemma hasLaw_XW (i : ℕ) : HasLaw (XW i) μW PW :=
  (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => μW) i).hasLaw

private lemma iIndepFun_XW : iIndepFun XW PW :=
  iIndepFun_infinitePi (P := fun _ : ℕ => μW) (X := fun _ => id) (fun _ => measurable_id)

/-- **`tendstoInDistribution_countMLE` is non-vacuous.** For i.i.d. counts with the three-point
law `μW`, every count-side hypothesis (second moment, score equations at the truth,
profile information) is discharged; only the estimator-side hypotheses `hroot`, `hcons` and the
Gaussian `Y`, which the merged Z-estimator theorem also takes, remain. -/
example {θhat : ℕ → (ℕ → ℕ) → E₂} (hθ_meas : ∀ n, AEMeasurable (θhat n) PW)
    (hroot : Tendsto (fun n => PW {ω | ∑ i ∈ range n, countScore 1 (θhat n ω) (XW i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure PW θhat atTop (fun _ => !₂[1, 1]))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → E₂} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪countScore 1 !₂[1, 1] k, t⟫ ^ 2 ∂μW).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - !₂[1, 1])) atTop
      (fun ω => Ring.inverse (countFisherInfo ((!₂[1, 1] : E₂) 0) ((!₂[1, 1] : E₂) 1) 1
        (∫ k, trigammaIncrement ((!₂[1, 1] : E₂) 0) k ∂μW)) (Y ω)) (fun _ => PW) P' :=
  tendstoInDistribution_countMLE one_pos (by simp) (by simp) hasLaw_XW iIndepFun_XW
    (integrable_μW _) integral_countScore_μW profile_μW hθ_meas hroot hcons hY_meas hY

/-! ### Godambe's information inequality -/

/-- **Equality case.** On a one-point space with score `s = 2` and estimating function `g = 3`
(so `g ∝ s`) in `E = ℝ`, the information is `I = 4`, `v = E[⟪g, w⟫ s] = 6 w` and
`⟪I⁻¹ v, v⟫ = (6w)² / 4 = 9 w² = E ⟪g, w⟫²`: the bound is attained. -/
example (w : ℝ) : ⟪Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()),
      ∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()⟫ = ∫ _ : Unit, ⟪(3 : ℝ), w⟫ ^ 2
        ∂Measure.dirac () := by
  have hI : IsUnit ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) :=
    MathlibExt.Probability.Statistics.VectorInference.isUnit_of_inner_self_pos fun u hu => by
      have : 0 < ‖u‖ := norm_pos_iff.2 hu
      simp only [FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      positivity
  have hv : (∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()) =
      ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (3 / 2 * w) := by
    simp; ring
  rw [hv, MathlibExt.Probability.Statistics.VectorInference.inverse_apply_apply hI]
  simp
  ring

example (w : ℝ) : ⟪Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()),
      ∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()⟫ ≤ ∫ _ : Unit, ⟪(3 : ℝ), w⟫ ^ 2
        ∂Measure.dirac () := by
  refine inner_inverse_le_integral_inner_sq (s := fun _ => (2 : ℝ)) (g := fun _ => (3 : ℝ))
    aestronglyMeasurable_const (integrable_const _) aestronglyMeasurable_const
    (integrable_const _) ?_ (fun z => ?_) w
  · exact MathlibExt.Probability.Statistics.VectorInference.isUnit_of_inner_self_pos fun u hu => by
      have : 0 < ‖u‖ := norm_pos_iff.2 hu
      simp only [FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      positivity
  · simp; ring

end MathlibExtTest.Biology.Omics.HierarchicalCountEfficiency
