/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialDispersion

@[expose] public section

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial

namespace MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialDispersion

/-! ### One count at `θ = 1`, `η = 0` (mean `μ = 1`) -/

/-- At `y = 0` the full log mass function is `log NB(0; 1, 1) = log (1 / 2) = -log 2`. -/
example : nbLogPmf 1 0 0 = -log 2 := by
  norm_num [nbLogPmf, nbKernel]

example : log (negBinomialReal 1 (exp 0) 0) = -log 2 := by
  rw [log_negBinomialReal_exp_eq_nbLogPmf one_pos]
  norm_num [nbLogPmf, nbKernel]

/-- The shape score at `y = 1`: `1 / 1 + log 1 + 1 - log 2 - 2 / 2 = 1 - log 2`. -/
theorem nbShapeScore_one_one_zero : nbShapeScore 1 1 0 = 1 - log 2 := by
  norm_num [nbShapeScore]
  ring

/-- The joint score of `nbLogPmf` at `(θ, η) = (1, 0)`, `y = 1`: the `η`-partial is
`nbScore 1 1 0 = 0` (the count equals the mean). -/
example : HasFDerivAt (fun q : ℝ × ℝ => nbLogPmf q.1 1 q.2)
    ((1 - log 2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    (1, 0) := by
  have h := hasFDerivAt_nbLogPmf one_pos 1 0
  rw [nbShapeScore_one_one_zero] at h
  convert h using 3
  norm_num [nbScore]

/-- The mixed partial at `y = 3`: `(3 - 1) · 1 / (1 + 1)² = 1 / 2`; it is nonzero pointwise even
though its mean is zero. -/
example : nbCross 1 3 0 = 1 / 2 := by norm_num [nbCross]

example : HasSum (fun k : ℕ => nbCross 1 k 0 * negBinomialReal 1 (exp 0) k) 0 :=
  hasSum_nbCross_mul_negBinomialReal one_pos 0

/-- **No joint concavity.** At `y = 0` the observed shape information is
`0 - 1 + 1 / 2 - (0 - 1) / 4 = -1 / 4 < 0`. -/
example : nbShapeObsInfo 1 0 0 = -1 / 4 := by norm_num [nbShapeObsInfo]

example : HasFDerivAt (fun q : ℝ × ℝ => nbShapeScore q.1 0 q.2)
    ((1 / 4 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (-1 / 4 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    (1, 0) := by
  have h := hasFDerivAt_nbShapeScore one_pos 0 0
  convert h using 3 <;> norm_num [nbShapeObsInfo, nbCross]

/-- The `θ`-partial of the `η`-score is the mixed partial `nbCross`. -/
example : HasFDerivAt (fun q : ℝ × ℝ => nbScore q.1 3 q.2)
    ((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - (1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    (1, 0) := by
  have h := hasFDerivAt_nbScore_prod one_pos 3 0
  convert h using 3 <;> norm_num [nbCross, nbObsWeight]

/-! ### The shape Fisher information is positive at `θ = 1`, `η = 0` -/

private lemma negBinomialReal_one_zero : negBinomialReal 1 (exp 0) 0 = 1 / 2 := by
  norm_num [negBinomialReal]

private lemma negBinomialReal_one_two_pos : 0 < negBinomialReal 1 (exp 0) 2 := by
  have := ascPochhammer_pos 2 (1 : ℝ) one_pos
  unfold negBinomialReal
  positivity

/-- `nbShapeFisherInfo 1 0 > 0`: the series `∑ₖ (∑_{j<k} 1 / (1 + j)²) NB(k; 1, 1)` exceeds
`1 - NB(0; 1, 1) = 1 / 2` because its inner sum is at least `1` for `k ≥ 1` and `5 / 4` at `k = 2`.
This makes the hypothesis of `inv_nbJointFisherInfo` satisfiable. -/
theorem nbShapeFisherInfo_one_zero_pos : 0 < nbShapeFisherInfo 1 0 := by
  have hμ := (exp_pos (0 : ℝ)).le
  set p := negBinomialReal 1 (exp 0)
  have hf : HasSum (fun k => p k - if k = 0 then p 0 else 0) (1 - p 0) :=
    (hasSum_negBinomialReal one_pos hμ).sub (hasSum_ite_eq 0 (p 0))
  have hle : ∀ k, (p k - if k = 0 then p 0 else 0) ≤
      (∑ j ∈ range k, ((1 + (j : ℝ)) ^ 2)⁻¹) * p k := by
    intro k
    have hp := negBinomialReal_nonneg one_pos hμ k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : (1 : ℝ) ≤ ∑ j ∈ range k, ((1 + (j : ℝ)) ^ 2)⁻¹ := by
        calc (1 : ℝ) = ((1 + ((0 : ℕ) : ℝ)) ^ 2)⁻¹ := by norm_num
          _ ≤ ∑ j ∈ range k, ((1 + (j : ℝ)) ^ 2)⁻¹ :=
            single_le_sum (f := fun j : ℕ => ((1 + (j : ℝ)) ^ 2)⁻¹)
              (fun j _ => by positivity) (mem_range.2 hk)
      rw [ite_eq_right_iff.2 fun h => absurd h hk.ne', sub_zero]
      nlinarith
  have hlt : (p 2 - if 2 = 0 then p 0 else 0) <
      (∑ j ∈ range 2, ((1 + (j : ℝ)) ^ 2)⁻¹) * p 2 := by
    have := negBinomialReal_one_two_pos
    norm_num [sum_range_succ]
    nlinarith
  have hg : Summable fun k => (∑ j ∈ range k, ((1 + (j : ℝ)) ^ 2)⁻¹) * p k := by
    refine ((hasSum_nbShapeObsInfo_mul_negBinomialReal one_pos 0).summable.add
      (((hasSum_negBinomialReal one_pos hμ).mul_left (1 / 4)).add
        ((hasSum_mul_negBinomialReal one_pos hμ).mul_left (1 / 4))).summable).congr fun k => ?_
    simp only [nbShapeObsInfo, p, exp_zero]
    ring
  have h := hasSum_lt (f := fun k => p k - if k = 0 then p 0 else 0) hle hlt hf hg.hasSum
  have hp0 : p 0 = 1 / 2 := negBinomialReal_one_zero
  have heq : nbShapeFisherInfo 1 0 =
      ∑' k, (∑ j ∈ range k, ((1 + (j : ℝ)) ^ 2)⁻¹) * p k - 1 / 2 := by
    simp only [nbShapeFisherInfo, p, exp_zero]
    ring
  rw [heq]
  linarith

/-! ### Information matrices for an intercept-only model -/

/-- The expected observed-information row is the block-diagonal Fisher row. -/
example (x : Fin 2 → ℝ) (η : ℝ) :
    HasSum (fun k : ℕ => negBinomialReal 1 (exp η) k • nbObsInfoRow 1 x k η)
      (nbFisherInfoRow 1 x η) :=
  hasSum_nbObsInfoRow one_pos x η

/-- The quadratic form of an observed-information row at `θ = 1`, `y = 3`, `η = 0`, `x = 1`, along
`(u, s) = (1, 1)`: `w - 2 c + v = 1 - 1 + v` with `v = nbShapeObsInfo 1 3 0`. -/
example : Sum.elim (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Unit => 1) ⬝ᵥ
    (nbObsInfoRow 1 (fun _ => 1) 3 0 *ᵥ Sum.elim (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Unit => 1)) =
      nbShapeObsInfo 1 3 0 := by
  rw [nbObsInfoRow_quadratic]
  norm_num [nbObsWeight, nbCross, dotProduct]

/-- The intercept-only design with one observation. -/
noncomputable abbrev X₁ : Matrix (Fin 1) (Fin 1) ℝ := of fun _ _ => 1

private lemma fisherBlock_X₁ :
    X₁ᵀ * diagonal (fun i => nbFisherWeight 1 ((X₁ *ᵥ 0) i + (0 : Fin 1 → ℝ) i)) * X₁ =
      of fun _ _ => 1 / 2 := by
  ext i j
  simp [mul_apply, nbFisherWeight, X₁]
  norm_num

/-- **Non-vacuity of the block inverse.** For the intercept-only design at `θ = 1`, `β = 0`, the
`β`-block of the inverse joint Fisher information is the inverse fixed-shape information
`(1 / 2)⁻¹ = 2`. -/
example : (nbJointFisherInfo 1 X₁ 0 0)⁻¹.toBlocks₁₁ = of fun _ _ => 2 := by
  have hA : IsUnit (X₁ᵀ * diagonal (fun i => nbFisherWeight 1 ((X₁ *ᵥ 0) i + (0 : Fin 1 → ℝ) i)) *
      X₁) := by
    rw [fisherBlock_X₁, isUnit_iff_isUnit_det, det_unique]
    norm_num
  have hD : ∑ i, nbShapeFisherInfo 1 ((X₁ *ᵥ (0 : Fin 1 → ℝ)) i + (0 : Fin 1 → ℝ) i) ≠ 0 := by
    simpa using nbShapeFisherInfo_one_zero_pos.ne'
  rw [toBlocks₁₁_inv_nbJointFisherInfo 1 X₁ 0 0 hA hD, fisherBlock_X₁]
  refine inv_eq_right_inv ?_
  ext i j
  rw [Subsingleton.elim i j, one_apply_eq]
  simp [mul_apply]

/-! ### The regression: joint score, observed information, consistency -/

/-- The joint score of a three-observation, two-coefficient regression. -/
example (X : Matrix (Fin 3) (Fin 2) ℝ) (o : Fin 3 → ℝ) (y : Fin 3 → ℕ) (β : Fin 2 → ℝ) :
    HasFDerivAt (nbJointLogLik X o y)
      ((Real.dotL (nbGradient 2 X o (fun i => (y i : ℝ)) β)).comp
          (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ) +
        nbJointShapeScore X o y (β, 2) • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ) (β, 2) :=
  hasFDerivAt_nbJointLogLik X o y (p := (β, 2)) two_pos

/-- Along the pure shape direction `(0, 1)` the second derivative is `-∑ᵢ nbShapeObsInfo`. -/
example (X : Matrix (Fin 3) (Fin 2) ℝ) (o : Fin 3 → ℝ) (y : Fin 3 → ℕ) (β : Fin 2 → ℝ) :
    HasDerivAt (fun t : ℝ =>
        nbGradient ((β, 2) + t • ((0 : Fin 2 → ℝ), (1 : ℝ))).2 X o (fun i => (y i : ℝ))
          ((β, 2) + t • ((0 : Fin 2 → ℝ), (1 : ℝ))).1 ⬝ᵥ 0 +
          nbJointShapeScore X o y ((β, 2) + t • ((0 : Fin 2 → ℝ), (1 : ℝ))) * 1)
      (-∑ i, nbShapeObsInfo 2 (y i) ((X *ᵥ β) i + o i)) 0 := by
  convert hasDerivAt_nbJointScore_line X o y (p := (β, 2)) two_pos (0, 1) using 1
  simp [nbJointObsInfo, sum_mulVec, dotProduct_sum, nbObsInfoRow_quadratic]

/-- With no observations the averaged log-likelihood is `0`. -/
example {Ω : Type*} (x : ℕ → Ω → Fin 2 → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ) (ω : Ω)
    (p : (Fin 2 → ℝ) × ℝ) : nbAvgLogLik x o y 0 ω p = 0 := by
  simp [nbAvgLogLik]

/-- **Consistency of the estimated shape** for an exact maximizer over `K`: the near-maximization
hypothesis of `tendstoInMeasure_nbJointMLE` then holds with empty events. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (x : ℕ → Ω → Fin 2 → ℝ)
    (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ) {M : (Fin 2 → ℝ) × ℝ → ℝ} {K : Set ((Fin 2 → ℝ) × ℝ)}
    (hK : IsCompact K) (hM : ContinuousOn M K) {p₀ : (Fin 2 → ℝ) × ℝ} (hp₀ : p₀ ∈ K)
    (hident : ∀ p ∈ K, p ≠ p₀ → M p < M p₀)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ =>
      P {ω | ∃ p ∈ K, ε ≤ |nbAvgLogLik x o y n ω p - M p|}) atTop (𝓝 0))
    {phat : ℕ → Ω → (Fin 2 → ℝ) × ℝ} (hin : ∀ n ω, phat n ω ∈ K)
    (hopt : ∀ n ω, ∀ p ∈ K, nbAvgLogLik x o y n ω p ≤ nbAvgLogLik x o y n ω (phat n ω)) :
    TendstoInMeasure P (fun n ω => (phat n ω).2) atTop (fun _ => p₀.2) := by
  refine tendstoInMeasure_snd_of_nbJointMLE
    (tendstoInMeasure_nbJointMLE x o y hK hM hp₀ hident hunif ?_ fun δ hδ => ?_)
  · simp [hin]
  · have h : ∀ n : ℕ, {ω | nbAvgLogLik x o y n ω (phat n ω) <
        nbAvgLogLik x o y n ω p₀ - δ} = ∅ := fun n => by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith [hopt n ω p₀ hp₀]
    simp [h]

/-- Plug-in Fisher weights at a consistent `(β̂, θ̂)` with `θ₀ = 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : Matrix (Fin 3) (Fin 2) ℝ)
    (o : Fin 3 → ℝ) {phat : ℕ → Ω → (Fin 2 → ℝ) × ℝ} {β₀ : Fin 2 → ℝ}
    (h : TendstoInMeasure P phat atTop (fun _ => (β₀, 1))) :
    TendstoInMeasure P (fun n ω i => nbFisherWeight (phat n ω).2 ((X *ᵥ (phat n ω).1) i + o i))
      atTop (fun _ i => nbFisherWeight 1 ((X *ᵥ β₀) i + o i)) :=
  tendstoInMeasure_nbFisherWeight_plugIn X o (p₀ := (β₀, 1)) one_pos h

/-- The `(0, 1)` entry of the plug-in `β`-block of the Fisher information is consistent. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : Matrix (Fin 3) (Fin 2) ℝ)
    (o : Fin 3 → ℝ) {phat : ℕ → Ω → (Fin 2 → ℝ) × ℝ} {β₀ : Fin 2 → ℝ}
    (h : TendstoInMeasure P phat atTop (fun _ => (β₀, 1))) :
    TendstoInMeasure P (fun n ω =>
        (Xᵀ * diagonal (fun i => nbFisherWeight (phat n ω).2 ((X *ᵥ (phat n ω).1) i + o i)) *
          X) 0 1)
      atTop (fun _ => (Xᵀ * diagonal (fun i => nbFisherWeight 1 ((X *ᵥ β₀) i + o i)) * X) 0 1) :=
  tendstoInMeasure_nbFisherInfo_plugIn X o (p₀ := (β₀, 1)) one_pos h 0 1

/-- The joint Fisher information of the intercept-only design is block diagonal. -/
example : nbJointFisherInfo 1 X₁ 0 0 =
    fromBlocks (of fun _ _ => 1 / 2) 0 0 (of fun _ _ => nbShapeFisherInfo 1 0) := by
  rw [nbJointFisherInfo_eq_fromBlocks, fisherBlock_X₁]
  simp

end MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialDispersion
