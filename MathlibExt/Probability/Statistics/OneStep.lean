/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.VectorInference
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Asymptotic normality of the one-step Newton estimator

Let `p θ` be a family of densities indexed by a finite-dimensional real inner product space `E`,
with Fisher information `J = fisherInformation ν p θ₀` nonsingular at an interior point `θ₀`,
and let `X i` be i.i.d. with law `lawOf ν p θ₀`. Start from any estimator `θinit n` with
`√n (θinit n - θ₀)` bounded in probability and take one Newton step with the score sum
`Sₙ(θ) = ∑_{i<n} score p θ (X i)`, `θ_os = θinit n + J⁻¹ (n⁻¹ Sₙ(θinit n))`
(`oneStepUpdate`); the step adds `J⁻¹ Sₙ / n` because the score derivative has mean `-J`.
Then `√n (θ_os - θ₀)` converges in distribution to `J⁻¹ Y`, where `Y` is the score-CLT limit
(`⟪Y, t⟫ ~ N(0, ⟪J t, t⟫)` for every `t`), without solving the likelihood equation.

The proof expands `Sₙ` about `θ₀` on a ball where the score is differentiable with a Lipschitz
derivative, makes the averaged Hessian and envelope converge by the strong law, applies the score
CLT, and assembles the limit with Slutsky's lemma; the starter leaves the ball with probability
tending to `0`.

Not covered: existence or consistency of roots of the likelihood equation (see
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation`), the information
identity `E[D score] = -J` (a hypothesis here), singular information, boundary parameters, and
iterated Newton steps.

## Main results

* `oneStepUpdate`: the Newton step `θinit + J⁻¹ (n⁻¹ • Sn)`.
* `tendstoInDistribution_oneStep`: `√n (oneStepUpdate J (θinit n) Sₙ n - θ₀) → J⁻¹ Y`.

## References

* A. W. van der Vaart, *Asymptotic Statistics* (1998), §5.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)
open MathlibExt.Probability.Statistics.VectorInference
  (score fisherInformation tendstoInDistribution_score ae_tendsto_average)

namespace MathlibExt.Probability.Statistics.OneStep

/-! ### Private helpers (Mathlib-only Slutsky/Taylor infrastructure). -/

/-- The summed first-order Taylor bridge at a point `θ` in the ball: the rescaled score sum
at `θ` equals the rescaled sum at `θ₀` plus the averaged Hessian applied to `√n • (θ - θ₀)`,
up to a remainder bounded by the averaged envelope times `‖θ - θ₀‖ • ‖√n • (θ - θ₀)‖`. -/
private theorem norm_resid_le {E 𝓧 : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace 𝓧]
    {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ}
    {M' : 𝓧 → ℝ} {H : 𝓧 → E →L[ℝ] E}
    (hdiff : ∀ x, DifferentiableOn ℝ (fun t => score p t x) (Metric.ball θ₀ δ))
    (hlip' : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M' x * ‖θ - θ₀‖)
    (hD : ∀ x, H x = fderiv ℝ (fun t => score p t x) θ₀)
    {n : ℕ} (hn : 0 < n) (xs : ℕ → 𝓧) {θ : E} (hθ : θ ∈ Metric.ball θ₀ δ) :
    ‖(√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, score p θ (xs i) -
        ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (xs i) +
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (xs i)) (√(n : ℝ) • (θ - θ₀)))‖ ≤
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (xs i)) * ‖θ - θ₀‖ *
        ‖√(n : ℝ) • (θ - θ₀)‖ := by
  set d := θ - θ₀ with hd
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hrr : (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ))⁻¹ := by
    have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    nth_rewrite 1 [← hs]
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  have htay : ∀ i ∈ Finset.range n,
      ‖score p θ (xs i) - score p θ₀ (xs i) - H (xs i) d‖ ≤ M' (xs i) * ‖d‖ ^ 2 := by
    intro i _
    have h := VectorInference.norm_sub_sub_fderiv_le (f := fun t => score p t (xs i))
      (fun θ' hθ' => (hdiff (xs i)).differentiableAt
        (IsOpen.mem_nhds Metric.isOpen_ball hθ'))
      (hlip' (xs i)) hθ
    rwa [← hD (xs i)] at h
  have e : ∑ i ∈ Finset.range n, score p θ (xs i) -
        ∑ i ∈ Finset.range n, score p θ₀ (xs i) -
        (∑ i ∈ Finset.range n, H (xs i)) d =
      ∑ i ∈ Finset.range n, (score p θ (xs i) - score p θ₀ (xs i) - H (xs i) d) := by
    rw [sum_apply, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hsum : ‖∑ i ∈ Finset.range n, score p θ (xs i) -
        ∑ i ∈ Finset.range n, score p θ₀ (xs i) -
        (∑ i ∈ Finset.range n, H (xs i)) d‖ ≤
      (∑ i ∈ Finset.range n, M' (xs i)) * ‖d‖ ^ 2 := by
    rw [e]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum htay
  have e1 : (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, score p θ (xs i) -
        ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (xs i) +
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (xs i)) (√(n : ℝ) • d)) =
      (√(n : ℝ))⁻¹ • (∑ i ∈ Finset.range n, score p θ (xs i) -
        ∑ i ∈ Finset.range n, score p θ₀ (xs i) -
        (∑ i ∈ Finset.range n, H (xs i)) d) := by
    rw [smul_apply, map_smul, smul_smul, hrr, ← smul_add, ← smul_sub]
    congr 1
    abel
  rw [e1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  have e2 : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (xs i)) * ‖d‖ * ‖√(n : ℝ) • d‖ =
      (√(n : ℝ))⁻¹ * ((∑ i ∈ Finset.range n, M' (xs i)) * ‖d‖ ^ 2) := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul]
    rw [← hrr]; ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hr.le)

/-- A tight sequence times a sequence tending to `0` in probability tends to `0` in
probability. -/
private theorem tendstoInMeasure_tight_mul_zero {Ω E : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [NormedAddCommGroup E] {T : ℕ → Ω → E} {U : ℕ → Ω → ℝ}
    (hT : ∀ δ > 0, ∃ C : ℝ, ∀ᶠ (n : ℕ) in atTop, P {ω | ‖T n ω‖ > C} < δ)
    (hU : TendstoInMeasure P U atTop 0) {κ : ℝ} (hκ : 0 < κ) :
    TendstoInMeasure P (fun n ω => κ * ‖T n ω‖ * U n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine ENNReal.tendsto_nhds_zero.2 fun a ha => ?_
  have ha2 : 0 < a / 2 := ENNReal.half_pos ha.ne'
  obtain ⟨C, hC⟩ := hT (a / 2) ha2
  set C' := max C 1 with hC'_def
  have hC'0 : 0 < C' := lt_max_iff.2 (Or.inr one_pos)
  have hCC' : C ≤ C' := le_max_left _ _
  have hU_thr := (tendstoInMeasure_iff_norm.1 hU) (ε / (κ * C'))
    (div_pos hε (mul_pos hκ hC'0))
  have hU_ev : ∀ᶠ (n : ℕ) in atTop, P {x | ε / (κ * C') ≤ ‖U n x - 0‖} < a / 2 :=
    (tendsto_order.1 hU_thr).2 _ ha2
  have hT_ev : ∀ᶠ (n : ℕ) in atTop, P {ω | ‖T n ω‖ > C'} < a / 2 := by
    refine hC.mono fun n hn => lt_of_le_of_lt (measure_mono fun ω hω => ?_) hn
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt hCC' hω
  refine (hT_ev.and hU_ev).mono fun n ⟨hnT, hnU⟩ => ?_
  have hsub : {x | ε ≤ ‖κ * ‖T n x‖ * U n x - 0‖} ⊆
      {ω | ‖T n ω‖ > C'} ∪ {x | ε / (κ * C') ≤ ‖U n x - 0‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    simp only [not_or, not_lt, not_le] at hcon
    obtain ⟨hTle, hUlt⟩ := hcon
    have hVeq : ‖κ * ‖T n ω‖ * U n ω - 0‖ = κ * ‖T n ω‖ * ‖U n ω - 0‖ := by
      rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos hκ, abs_of_nonneg (norm_nonneg _), sub_zero]
    rw [hVeq] at hω
    have hlt : κ * ‖T n ω‖ * ‖U n ω - 0‖ < ε := by
      have hne : κ * C' ≠ 0 := (mul_pos hκ hC'0).ne'
      calc κ * ‖T n ω‖ * ‖U n ω - 0‖ ≤ κ * C' * ‖U n ω - 0‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTle hκ.le)
              (norm_nonneg _)
        _ < κ * C' * (ε / (κ * C')) := mul_lt_mul_of_pos_left hUlt (mul_pos hκ hC'0)
        _ = ε := by field_simp
    exact (not_le_of_gt hlt) hω
  refine le_trans (measure_mono hsub) ?_
  calc P ({ω | ‖T n ω‖ > C'} ∪ {x | ε / (κ * C') ≤ ‖U n x - 0‖})
      ≤ P {ω | ‖T n ω‖ > C'} + P {x | ε / (κ * C') ≤ ‖U n x - 0‖} :=
        measure_union_le _ _
    _ ≤ a / 2 + a / 2 := add_le_add hnT.le hnU.le
    _ = a := ENNReal.add_halves a

/-! ### The one-step estimator -/

/-- One Newton step from `θinit` with total score `Sn` and invertible information `J`.
Since the score-derivative mean is `D = -J`, the cancelling update adds `J⁻¹ S/n`. -/
noncomputable def oneStepUpdate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (θinit Sn : E) (n : ℕ) : E :=
  θinit + Ring.inverse J ((n : ℝ)⁻¹ • Sn)

/-- **One-step estimator asymptotic normality.** From a `√n`-bounded starter, one Newton
step with the score sum (`θ_init + J⁻¹ S_n(θ_init)/n`) is asymptotically normal with the
`+J⁻¹ Y` limit law. The score CLT is `VectorInference.tendstoInDistribution_score`, and the
strong law for the envelope average `n⁻¹ ∑ |M (X i)|` is `VectorInference.ae_tendsto_average`.
`hdiff` is needed because `hlip` constrains only `fderiv`, which is `0` wherever the score is
not differentiable, so `hlip` alone allows a score with a jump; `hscore_meas` makes the score
sums at the random starter measurable. -/
theorem tendstoInDistribution_oneStep
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P)
    (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hscore_meas : Measurable fun q : E × 𝓧 => score p q.1 q.2)
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hlip : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hdiff : ∀ x, DifferentiableOn ℝ (fun t => score p t x) (Metric.ball θ₀ δ))
    {H : 𝓧 → E →L[ℝ] E}
    (hHbar : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (X i ω)) atTop
      (fun _ => ∫ x, H x ∂(lawOf ν p θ₀)))
    (hD : ∀ x, H x = fderiv ℝ (fun t => score p t x) θ₀)
    (hJ : IsUnit (fisherInformation ν p θ₀))
    (hDJ : ∫ x, H x ∂(lawOf ν p θ₀) = -fisherInformation ν p θ₀)
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (⟪fisherInformation ν p θ₀ t, t⟫).toNNReal) P')
    {θinit : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θinit n) P)
    (htight : ∀ δ > 0, ∃ C : ℝ, ∀ᶠ (n : ℕ) in atTop,
      P {ω | ‖√(n : ℝ) • (θinit n ω - θ₀)‖ > C} < δ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (oneStepUpdate (fisherInformation ν p θ₀)
        (θinit n ω) (∑ i ∈ Finset.range n, score p (θinit n ω) (X i ω)) n - θ₀))
      atTop
      (fun ω => Ring.inverse (fisherInformation ν p θ₀) (Y ω))
      (fun _ => P) P' := by
  set J : E →L[ℝ] E := fisherInformation ν p θ₀ with hJ_def
  set K : E →L[ℝ] E := Ring.inverse J with hK_def
  set κ : ℝ := ‖K‖ + 1 with hκ_def
  have hκ0 : 0 < κ := by positivity
  have hκK : ‖K‖ ≤ κ := by rw [hκ_def]; exact le_add_of_nonneg_right zero_le_one
  have hKJ : ∀ v, K (J v) = v := VectorInference.inverse_apply_apply hJ
  set M' : 𝓧 → ℝ := fun x => |M x| with hM'_def
  have hM'_meas : Measurable M' := continuous_abs.measurable.comp hM_meas
  have hM'_int : Integrable M' (lawOf ν p θ₀) := hM_int.abs
  have hM' : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M' x * ‖θ - θ₀‖ :=
    fun x θ hθ => (hlip x θ hθ).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  set A : ℕ → Ω → E :=
    fun n ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω) with hA_def
  set B : ℕ → Ω → E →L[ℝ] E :=
    fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (X i ω) with hB_def
  set D : E →L[ℝ] E := ∫ x, H x ∂(lawOf ν p θ₀) with hD_def
  set Mb : ℕ → Ω → ℝ :=
    fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (X i ω) with hMb_def
  set T : ℕ → Ω → E := fun n ω => √(n : ℝ) • (θinit n ω - θ₀) with hT_def
  set Sn : ℕ → Ω → E :=
    fun n ω => ∑ i ∈ Finset.range n, score p (θinit n ω) (X i ω) with hSn_def
  set Tn : ℕ → Ω → E :=
    fun n ω => √(n : ℝ) • (oneStepUpdate J (θinit n ω) (Sn n ω) n - θ₀) with hTn_def
  set U : ℕ → Ω → ℝ :=
    fun n ω => ‖B n ω - D‖ + Mb n ω * ‖θinit n ω - θ₀‖ with hU_def
  set V : ℕ → Ω → ℝ := fun n ω => κ * ‖T n ω‖ * U n ω with hV_def
  set G : ℕ → Set Ω := fun n => {ω | θinit n ω ∈ Metric.ball θ₀ δ} with hG_def
  -- measurability
  have hSn_meas : ∀ n, AEMeasurable (Sn n) P := fun n => by
    have h : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, score p (θinit n ω) (X i ω)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ =>
        hscore_meas.comp_aemeasurable ((hθ_meas n).prodMk (hXm i))
    exact h
  have hTn_meas : ∀ n, AEMeasurable (Tn n) P := fun n => by
    have hKSn : AEMeasurable (fun ω => K ((n : ℝ)⁻¹ • Sn n ω)) P :=
      K.continuous.measurable.comp_aemeasurable ((hSn_meas n).const_smul _)
    have h : AEMeasurable
        (fun ω => √(n : ℝ) • (θinit n ω + K ((n : ℝ)⁻¹ • Sn n ω) - θ₀)) P :=
      ((((hθ_meas n).add hKSn).sub_const _).const_smul _)
    exact h
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n => by
    have h : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, M' (X i ω)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hM'_meas.comp_aemeasurable (hXm i)
    have h2 := h.const_mul ((n : ℝ)⁻¹)
    exact h2
  have hd_meas : ∀ n, AEMeasurable (fun ω => ‖θinit n ω - θ₀‖) P :=
    fun n => ((hθ_meas n).sub_const _).norm
  -- engines: score CLT and scalar SLLN
  have hA : TendstoInDistribution A atTop Y (fun _ => P) P' :=
    tendstoInDistribution_score hX_law hX_indep hs_meas hs_sq hs_mean hY_meas hY
  have hMb_ae : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Mb n ω) atTop
      (𝓝 (∫ x, M' x ∂(lawOf ν p θ₀))) :=
    ae_tendsto_average (μX := lawOf ν p θ₀) (X := X) hX_law hX_indep (g := M')
      hM'_meas.stronglyMeasurable hM'_int
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M' x ∂(lawOf ν p θ₀)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable) hMb_ae
  have hsqrt_top : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  -- tightness implies consistency of the starter
  have hcons : TendstoInMeasure P (fun n ω => ‖θinit n ω - θ₀‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    refine ENNReal.tendsto_nhds_zero.2 fun a ha => ?_
    obtain ⟨C, hC⟩ := htight a ha
    have hev : ∀ᶠ (n : ℕ) in atTop, C / ε + 1 ≤ √(n : ℝ) :=
      hsqrt_top.eventually (eventually_ge_atTop _)
    refine (hC.and hev).mono fun n ⟨hnC, hnn⟩ => ?_
    refine le_trans (measure_mono fun ω hω => ?_) (le_of_lt hnC)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hd : ε ≤ ‖θinit n ω - θ₀‖ := by
      simpa [sub_zero, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hω
    have hT_eq : ‖T n ω‖ = √(n : ℝ) * ‖θinit n ω - θ₀‖ := by
      rw [hT_def]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hT_eq]
    have h1 : C + ε ≤ √(n : ℝ) * ε := by
      have h2 := mul_le_mul_of_nonneg_right hnn hε.le
      rwa [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at h2
    calc C < C + ε := by linarith
      _ ≤ √(n : ℝ) * ε := h1
      _ ≤ √(n : ℝ) * ‖θinit n ω - θ₀‖ :=
          mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)
  -- the averaged Hessian and envelope terms vanish in probability
  have hBD : TendstoInMeasure P (fun n ω => ‖B n ω - D‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hHbar ⊢
    simpa using hHbar
  have hMb_dist : TendstoInDistribution Mb atTop (fun _ => ∫ x, M' x ∂(lawOf ν p θ₀))
      (fun _ => P) P :=
    hMb.tendstoInDistribution hMb_meas
  have hMb_d : TendstoInMeasure P (fun n ω => Mb n ω * ‖θinit n ω - θ₀‖) atTop 0 :=
    TendstoInDistribution.mul_tendstoInMeasure_zero hMb_dist hcons hd_meas
  have hU : TendstoInMeasure P U atTop 0 := tendstoInMeasure_add_zero hBD hMb_d
  have hV : TendstoInMeasure P V atTop 0 := tendstoInMeasure_tight_mul_zero htight hU hκ0
  -- the deterministic bound on the good events
  have hbound : ∀ n, ∀ ω ∈ G n, ‖Tn n ω - K (A n ω)‖ ≤ V n ω := by
    intro n ω hω
    simp only [hG_def, Set.mem_ofPred_eq] at hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hT0 : T 0 ω = 0 := by simp [hT_def]
      have hA0 : A 0 ω = 0 := by simp [hA_def]
      have hTn0 : Tn 0 ω = 0 := by simp [hTn_def]
      simp [hTn0, hA0, hT0, hV_def]
    · have hbridge : ‖(√(n : ℝ))⁻¹ • Sn n ω - (A n ω + B n ω (T n ω))‖ ≤
          Mb n ω * ‖θinit n ω - θ₀‖ * ‖T n ω‖ :=
        norm_resid_le hdiff hM' hD hn (fun i => X i ω) hω
      have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hrr : (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ))⁻¹ := by
        have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
        nth_rewrite 1 [← hs]
        rw [mul_inv, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
      have hsqrt_ninv : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ := by
        rw [mul_comm]; exact hrr
      have hOS : oneStepUpdate J (θinit n ω) (Sn n ω) n
          = θinit n ω + K ((n : ℝ)⁻¹ • Sn n ω) := rfl
      have hTn_eq : Tn n ω = T n ω + K ((√(n : ℝ))⁻¹ • Sn n ω) := by
        have harg : θinit n ω + K ((n : ℝ)⁻¹ • Sn n ω) - θ₀
            = (θinit n ω - θ₀) + K ((n : ℝ)⁻¹ • Sn n ω) := by abel_nf
        simp only [hTn_def, hT_def, hOS, harg, smul_add, ← map_smul, smul_smul, hsqrt_ninv]
      have hSn_eq : (√(n : ℝ))⁻¹ • Sn n ω
          = A n ω + B n ω (T n ω) +
            ((√(n : ℝ))⁻¹ • Sn n ω - (A n ω + B n ω (T n ω))) := by abel_nf
      have hJB : J + B n ω = B n ω - D := by
        rw [hDJ, sub_neg_eq_add]
        exact add_comm _ _
      have hT_eq : T n ω + K (B n ω (T n ω)) = K ((B n ω - D) (T n ω)) := by
        have hTJ : T n ω = K (J (T n ω)) := (hKJ _).symm
        nth_rewrite 1 [hTJ]
        rw [← map_add, ← add_apply, hJB]
      have eTn : Tn n ω - K (A n ω)
          = K ((B n ω - D) (T n ω)) +
            K ((√(n : ℝ))⁻¹ • Sn n ω - (A n ω + B n ω (T n ω))) := by
        rw [hTn_eq, hSn_eq, map_add, map_add, ← hT_eq]
        abel_nf
      rw [eTn]
      have hKκ : ∀ v : E, ‖K v‖ ≤ κ * ‖v‖ := fun v =>
        (K.le_opNorm v).trans (mul_le_mul_of_nonneg_right hκK (norm_nonneg v))
      have h1 : ‖K ((B n ω - D) (T n ω))‖ ≤ κ * (‖B n ω - D‖ * ‖T n ω‖) :=
        (hKκ _).trans
          (mul_le_mul_of_nonneg_left ((B n ω - D).le_opNorm _) hκ0.le)
      have h2 : ‖K ((√(n : ℝ))⁻¹ • Sn n ω - (A n ω + B n ω (T n ω)))‖ ≤
          κ * (Mb n ω * ‖θinit n ω - θ₀‖ * ‖T n ω‖) :=
        (hKκ _).trans (mul_le_mul_of_nonneg_left hbridge hκ0.le)
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add h1 h2).trans ?_
      have eV : κ * (‖B n ω - D‖ * ‖T n ω‖) +
          κ * (Mb n ω * ‖θinit n ω - θ₀‖ * ‖T n ω‖) = V n ω := by
        simp only [hV_def, hU_def]
        ring
      rw [eV]
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.1 hcons) δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le) fun n => ?_
    refine measure_mono fun ω hω => ?_
    simp only [hG_def, Set.mem_compl_iff, Set.mem_ofPred_eq] at hω
    simp only [Set.mem_ofPred_eq]
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hω
    simpa [sub_zero, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hω
  have hdiff : TendstoInMeasure P (fun n ω => ‖Tn n ω - K (A n ω)‖) atTop 0 := by
    have hbound' : ∀ n, ∀ ω ∈ G n, |‖Tn n ω - K (A n ω)‖| ≤ V n ω := by
      intro n ω hω
      rw [abs_of_nonneg (norm_nonneg _)]
      exact hbound n ω hω
    exact tendstoInMeasure_zero_of_abs_le hV hG hbound'
  have hdiff' : TendstoInMeasure P (Tn - fun n ω => K (A n ω)) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hdiff ⊢
    simpa using hdiff
  have hlim : TendstoInDistribution (fun n ω => K (A n ω)) atTop (fun ω => K (Y ω))
      (fun _ => P) P' :=
    hA.continuous_comp (g := fun v => K v) K.continuous
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hlim hdiff' hTn_meas

end MathlibExt.Probability.Statistics.OneStep
