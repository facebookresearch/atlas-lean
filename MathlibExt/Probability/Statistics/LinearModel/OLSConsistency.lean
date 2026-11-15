/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.Probability.Statistics.LinearModel.Sampling

/-!
# Consistency of OLS with i.i.d. rows (Atlas ST05.T01)

Random-design model: i.i.d. rows `(xᵢ, uᵢ)` with observed responses
`yᵢ = xᵢ ⬝ᵥ β + uᵢ`, moment exogeneity `𝔼[x₀ u₀] = 0`, and a nonsingular
population Gram `Q = 𝔼[x₀ x₀ᵀ]`. The OLS sequence `β̂ₙ` is the existing
`olsEstimator` applied to the observed design of the first `n` rows and the
first `n` responses (`olsSeqEstimator`). In normalized Gram/score form
(`olsSeqEstimator_eq`) it is `β̂ₙ = Q̂ₙ⁻¹ *ᵥ ĝₙ` with
`Q̂ₙ = n⁻¹ ∑_{i<n} xᵢ xᵢᵀ` (outer products `Matrix.vecMulVec xᵢ xᵢ`) and
`ĝₙ = n⁻¹ ∑_{i<n} yᵢ xᵢ`. Then `β̂ₙ → β` almost surely.

Proof route (do not reprove the strong law): the Banach-valued strong law
`ProbabilityTheory.strong_law_ae` (applied to the entrywise scalar
sequences, i.e. in the Pi type `k → k → ℝ`) gives `Q̂ₙ → Q` for i.i.d.
regressors and `n⁻¹ ∑ xᵢ uᵢ → 0` a.s.; hence
`ĝₙ = Q̂ₙ *ᵥ β + n⁻¹ ∑ xᵢ uᵢ → Q *ᵥ β` a.s.; continuity of matrix inversion
at the unit `Q` in the Pi topology (`continuousAt_matrix_inv`, via
`continuousAt_inv₀` on the determinant and `Ring.inverse_eq_inv'`) gives
`Q̂ₙ⁻¹ → Q⁻¹` a.s.; the composition is `β`. This is a bridge theorem: no
OLS-consistency theorem exists on main.

Note: the population Gram is defined entrywise by scalar integrals, so the
statements need no matrix norm instance.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory Filter Finset Topology

open scoped Function

namespace MathlibExt.Probability.Statistics.LinearModel

/-- The population Gram matrix, entrywise: `Q a b = 𝔼[x₀ a * x₀ b]`. -/
noncomputable def popGram {k : Type*} [Fintype k] {Ω : Type*} [MeasurableSpace Ω]
    (X0 : Ω → (k → ℝ)) (μ : Measure Ω) : Matrix k k ℝ :=
  Matrix.of fun a b => ∫ ω, X0 ω a * X0 ω b ∂μ

/-- The OLS estimator at sample size `n`: `olsEstimator` applied to the observed design of the
first `n` regressor rows `X 0 ω, …, X (n - 1) ω` and the first `n` responses `Y`. -/
noncomputable def olsSeqEstimator {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} (X : ℕ → Ω → (k → ℝ)) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : k → ℝ :=
  olsEstimator (Matrix.of fun (i : Fin n) (a : k) => X i ω a) (fun i : Fin n => Y i ω)

/-- The sequential OLS estimator in normalized Gram/score form,
`(n⁻¹ ∑_{i<n} xᵢ xᵢᵀ)⁻¹ *ᵥ (n⁻¹ ∑_{i<n} yᵢ xᵢ)`. The normalization cancels for every `n`,
including when the sample Gram matrix is singular (both inverses are then `0`). -/
theorem olsSeqEstimator_eq {k : Type*} [Fintype k] [DecidableEq k] {Ω : Type*}
    (X : ℕ → Ω → (k → ℝ)) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    olsSeqEstimator X Y n ω =
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω • X i ω) := by
  set G := ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω) with hGdef
  set S := ∑ i ∈ Finset.range n, Y i ω • X i ω with hSdef
  have hG : (Matrix.of fun (i : Fin n) (a : k) => X i ω a)ᵀ *
      (Matrix.of fun (i : Fin n) (a : k) => X i ω a) = G := by
    ext a b
    rw [hGdef, Matrix.sum_apply,
      Finset.sum_range (fun i => Matrix.vecMulVec (X i ω) (X i ω) a b)]
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hS : (Matrix.of fun (i : Fin n) (a : k) => X i ω a)ᵀ *ᵥ (fun i : Fin n => Y i ω) = S := by
    ext a
    rw [hSdef, Finset.sum_apply, Finset.sum_range (fun i => (Y i ω • X i ω) a)]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hols : olsSeqEstimator X Y n ω = G⁻¹ *ᵥ S := by
    rw [olsSeqEstimator, olsEstimator, olsMatrix_eq, ← Matrix.mulVec_mulVec, hG, hS]
  rw [hols]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [hGdef, hSdef]
  · have hc : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne')
    by_cases hGu : IsUnit G.det
    · have hinv : ((n : ℝ)⁻¹ • G)⁻¹ = (n : ℝ) • G⁻¹ := by
        have h := Matrix.inv_smul' G (Units.mk0 ((n : ℝ)⁻¹) hc) hGu
        simpa [Units.smul_def] using h
      rw [hinv, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul]
    · have hdet : ¬IsUnit ((n : ℝ)⁻¹ • G).det := by
        rw [Matrix.det_smul, isUnit_iff_ne_zero]
        rw [isUnit_iff_ne_zero, not_not] at hGu
        simp [hGu]
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hGu,
        Matrix.nonsing_inv_apply_not_isUnit _ hdet, Matrix.zero_mulVec, Matrix.zero_mulVec]

/-- **Strong law for the sample Gram matrix**: for pairwise independent,
identically distributed regressors `xᵢ` with integrable products of
coordinates, the entrywise averages `n⁻¹ ∑_{i<n} xᵢ xᵢᵀ` converge almost
surely to the population Gram `popGram`. The topology on matrices is the
entrywise (Pi) topology. -/
theorem tendsto_sampleGram_ae {k : Type*} [Fintype k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)}
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => (n : ℝ)⁻¹ •
      ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) atTop
      (𝓝 (popGram (X 0) μ)) := by
  have key : ∀ a b, ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω a * X i ω b)
      atTop (𝓝 (popGram (X 0) μ a b)) := by
    intro a b
    have hf : Measurable (fun x : k → ℝ => x a * x b) :=
      (measurable_pi_apply a).mul (measurable_pi_apply b)
    have hS := strong_law_ae
      (X := fun i => (fun x : k → ℝ => x a * x b) ∘ X i)
      (hintGram a b)
      (fun i j hij => (hindep hij).comp hf hf)
      (fun i => (hident i).comp hf)
    exact hS
  filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (key a))] with ω hω
  refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => ?_
  refine (hω a b).congr fun n => ?_
  simp [Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- **Consistency of OLS**: under i.i.d. rows, moment exogeneity, and a
nonsingular population Gram, the OLS sequence computed from the observed
responses `yᵢ = xᵢ ⬝ᵥ β + uᵢ` converges almost surely to the population
projection coefficient `β`. -/
theorem tendsto_olsSeqEstimator_ae {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ} (β : k → ℝ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω))
      (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hintScore : Integrable (fun ω => (U 0 ω) • X 0 ω) μ)
    (hmeanScore : ∫ ω, (U 0 ω) • X 0 ω ∂μ = 0)
    (hQ : IsUnit (popGram (X 0) μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) =>
      olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω) atTop (𝓝 β) := by
  have hGramMul : ∀ (x : k → ℝ), Matrix.vecMulVec x x *ᵥ β = (x ⬝ᵥ β) • x := by
    intro x
    ext a
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have halg : ∀ (ω : Ω) (n : ℕ),
      (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β + U i ω) • X i ω
      = ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) *ᵥ β
        + (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (U i ω) • X i ω := by
    intro ω n
    have h1 : ∀ i : ℕ, ((X i ω ⬝ᵥ β + U i ω) • X i ω)
        = (X i ω ⬝ᵥ β) • X i ω + (U i ω) • X i ω := fun i => add_smul _ _ _
    simp_rw [h1, Finset.sum_add_distrib, smul_add, Matrix.smul_mulVec, Matrix.sum_mulVec,
      hGramMul]
  have hscore : ∀ a, ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (U i ω) • X i ω)) a)
      atTop (𝓝 (0 : ℝ)) := by
    intro a
    have hg : Measurable (fun p : (k → ℝ) × ℝ => p.2 * p.1 a) :=
      measurable_snd.mul ((measurable_pi_apply a).comp measurable_fst)
    have hintA : Integrable ((fun p : (k → ℝ) × ℝ => p.2 * p.1 a) ∘
        fun ω => (X 0 ω, U 0 ω)) μ := by
      refine ((ContinuousLinearMap.proj a : (k → ℝ) →L[ℝ] ℝ).integrable_comp
        hintScore).congr ?_
      filter_upwards with ω
      simp [ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hS := strong_law_ae
      (X := fun i => (fun p : (k → ℝ) × ℝ => p.2 * p.1 a) ∘ fun ω => (X i ω, U i ω))
      hintA
      (fun i j hij => (hindep hij).comp hg hg)
      (fun i => (hident i).comp hg)
    have hmean : (∫ ω, ((fun p : (k → ℝ) × ℝ => p.2 * p.1 a) ∘
        fun ω => (X 0 ω, U 0 ω)) ω ∂μ) = 0 := by
      have hcomm := (ContinuousLinearMap.proj a : (k → ℝ) →L[ℝ] ℝ).integral_comp_comm
        hintScore
      rw [hmeanScore, map_zero] at hcomm
      rw [← hcomm]
      apply integral_congr_ae
      filter_upwards with ω
      simp [ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hmean] at hS
    exact hS.mono fun ω hω => hω.congr fun n => by
      simp [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hscorePi : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (U i ω) • X i ω)
      atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr hscore] with ω hω
    exact tendsto_pi_nhds.mpr hω
  have hindepX : Pairwise ((· ⟂ᵢ[μ] ·) on X) :=
    fun i j hij => (hindep hij).comp measurable_fst measurable_fst
  have hidentX : ∀ i, IdentDistrib (X i) (X 0) μ μ :=
    fun i => (hident i).comp measurable_fst
  have hQgram := tendsto_sampleGram_ae hindepX hidentX hintGram
  filter_upwards [hQgram, hscorePi] with ω hQω hSω
  have hdetU : IsUnit (popGram (X 0) μ).det := (Matrix.isUnit_iff_isUnit_det _).mp hQ
  have hdet : (popGram (X 0) μ).det ≠ 0 := hdetU.ne_zero
  have hinv : ContinuousAt Inv.inv (popGram (X 0) μ) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hQinv : Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹)
      atTop (𝓝 (popGram (X 0) μ)⁻¹) := by
    have h := hinv.tendsto.comp hQω
    simpa [Function.comp_def] using h
  have hQbeta : Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) *ᵥ β)
      atTop (𝓝 ((popGram (X 0) μ) *ᵥ β)) := by
    have hcont : Continuous (fun A : Matrix k k ℝ => A *ᵥ β) :=
      continuous_id.matrix_mulVec continuous_const
    have h := (hcont.tendsto _).comp hQω
    simpa [Function.comp_def] using h
  have hghat : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β + U i ω) • X i ω)
      atTop (𝓝 ((popGram (X 0) μ) *ᵥ β)) := by
    have h := hQbeta.add hSω
    rw [add_zero] at h
    exact h.congr fun n => (halg ω n).symm
  have hbeta : (popGram (X 0) μ)⁻¹ *ᵥ ((popGram (X 0) μ) *ᵥ β) = β := by
    calc (popGram (X 0) μ)⁻¹ *ᵥ ((popGram (X 0) μ) *ᵥ β)
        = ((popGram (X 0) μ)⁻¹ * (popGram (X 0) μ)) *ᵥ β :=
          Matrix.mulVec_mulVec β _ _
      _ = (1 : Matrix k k ℝ) *ᵥ β := by
          congr 1
          exact Matrix.nonsing_inv_mul _ hdetU
      _ = β := Matrix.one_mulVec β
  have hcont2 : Continuous (fun p : Matrix k k ℝ × (k → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hprod := hQinv.prodMk_nhds hghat
  have h := (hcont2.tendsto _).comp hprod
  have hlim : ((popGram (X 0) μ)⁻¹, (popGram (X 0) μ) *ᵥ β).1 *ᵥ
      ((popGram (X 0) μ)⁻¹, (popGram (X 0) μ) *ᵥ β).2 = β := hbeta
  rw [hlim] at h
  have hfinal : Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β + U i ω) • X i ω))
      atTop (𝓝 β) := h.congr fun n => rfl
  exact hfinal.congr fun n => (olsSeqEstimator_eq X _ n ω).symm

end MathlibExt.Probability.Statistics.LinearModel
