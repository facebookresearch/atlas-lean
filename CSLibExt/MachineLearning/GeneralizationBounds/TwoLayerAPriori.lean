/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.TwoLayerReLURademacher
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import MathlibExt.Probability.UniformLaws

/-!
# A priori estimate of the population risk for two-layer networks

W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural
networks*, Commun. Math. Sci. 17 (2019), arXiv:1810.06397, Theorem 4.1 (noiseless case). Data
`x ∼ ρ_x` lie in `X = [-1, 1]^d`, the target `f*` takes values in `[0, 1]` on `X` and has a
representation `f*(x) = ∫ a(w) σ(⟨w, x⟩) dπ(w)` with `π` a probability measure on the `ℓ¹` unit
sphere `{‖w‖₁ = 1}` (their equation (3.3), with `σ` the ReLU); `γ₂(f*)` is the infimum of
`(∫ |a|² dπ)^{1/2}` over such representations (equation (3.4)). Networks
`f(x; θ) = ∑ₖ aₖ σ(⟨wₖ, x⟩)` of width `m` are truncated to `[0, 1]`, and the estimator `θ̂`
minimizes the path-norm regularized empirical risk
`J_λ(θ) = (1/n) ∑ᵢ ½ (f(xᵢ; θ) - f*(xᵢ))² + λ (‖θ‖_P + 1)` (Definition 3.1). If
`log (2d) ≥ 1` and `λ ≥ λ_n = 4 √(2 log (2d) / n)`, then for every `δ > 0`, with probability at
least `1 - δ` over the sample,

`𝔼_x |f(x; θ̂) - f*(x)|² ≲ γ₂(f*)² / m + λ γ̂₂(f*) + n^{-1/2} (γ̂₂(f*) + √(log (n / δ)))`

with `γ̂₂ = max(1, γ₂)` and an absolute constant. The estimate is a priori: it depends on the
target only through its Barron norm, and its estimation part does not depend on the width `m`.

The estimate proved here quantifies over every representation `(a, π)` with `∫ |a|² dπ ≤ γ²`
instead of naming `γ₂(f*)`; since the right-hand side is nondecreasing and continuous in `γ`,
this is equivalent to the stated form. The source's proof combines the direct approximation theorem
(Theorem 3.1) with the Rademacher bound for path-norm balls (bound (5.1)) and the Rademacher
risk bound (Theorem 5.1), through the a posteriori bound of Theorem 5.2. Measurability of `f*`
is assumed (on `X` the representation already makes `f*` continuous); every minimizer `θ̂` is
covered. As for the repository's Rademacher risk bound, the probability is that of a possibly
non-measurable event, measured by the outer measure of the product measure.

The proof of `twoLayer_a_priori_estimate` averages the objective of networks formed from i.i.d.
neurons. This bounds all minimizers' empirical losses and path norms on every sample in the
cube. A uniform deviation estimate on the resulting path-norm ball then bounds population risk.
-/

set_option autoImplicit false

namespace CSLibExt.MachineLearning.GeneralizationBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TwoLayerAPriori

private def clip (t : ℝ) : ℝ := max (min t 1) 0

private lemma clip_mem (t : ℝ) : clip t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) zero_le_one⟩

private lemma clip_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clip t = t := by
  rw [clip, min_eq_left ht.2, max_eq_left ht.1]

private lemma lipschitz_clip : LipschitzWith 1 clip :=
  (LipschitzWith.id.min_const (1 : ℝ)).max_const 0

private lemma sq_loss_le (s t : ℝ) : (clip s - clip t) ^ 2 ≤ 1 := by
  have hs := clip_mem s
  have ht := clip_mem t
  rw [← sq_abs]
  have h : |clip s - clip t| ≤ 1 :=
    abs_le.2 ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  simpa using pow_le_pow_left₀ (abs_nonneg _) h 2

private lemma lipschitz_sq_loss (t : ℝ) :
    LipschitzWith 2 (fun s => (clip s - clip t) ^ 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro s r
  have hs := clip_mem s
  have hr := clip_mem r
  have ht := clip_mem t
  have hsum : |clip s + clip r - 2 * clip t| ≤ 2 :=
    abs_le.2 ⟨by linarith [hs.1, hr.1, ht.2], by linarith [hs.2, hr.2, ht.1]⟩
  have hclip : |clip s - clip r| ≤ |s - r| := by
    simpa [Real.dist_eq] using lipschitz_clip.dist_le_mul s r
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  rw [show (clip s - clip t) ^ 2 - (clip r - clip t) ^ 2 =
    (clip s - clip r) * (clip s + clip r - 2 * clip t) by ring, abs_mul]
  calc _ ≤ |s - r| * 2 := mul_le_mul hclip hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := mul_comm _ _

private lemma abs_le_one_of_mem_cube {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)) (j : Fin d) :
    |x j| ≤ 1 := abs_le.2 (hx j (Set.mem_univ j))

private lemma abs_relu_le_l1 {d : ℕ} (w x : Fin d → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    |max (∑ j, w j * x j) 0| ≤ ∑ j, |w j| := by
  rw [abs_of_nonneg (le_max_right _ _)]
  refine (max_le (le_abs_self _) (abs_nonneg _)).trans ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hx j)

private lemma pathNorm_nonneg {d m : ℕ} (a : Fin m → ℝ) (w : Fin m → Fin d → ℝ) :
    0 ≤ pathNorm a w := by
  unfold pathNorm
  positivity

private lemma abs_twoLayerReLU_le_pathNorm {d m : ℕ}
    (a : Fin m → ℝ) (w : Fin m → Fin d → ℝ) (x : Fin d → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    |twoLayerReLU a w x| ≤ pathNorm a w := by
  unfold twoLayerReLU pathNorm
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_relu_le_l1 (w k) x hx) (abs_nonneg _)

private lemma aestronglyMeasurable_coeff {d : ℕ} {ν : Measure (Fin d → ℝ)}
    (hsphere : ∀ᵐ w ∂ν, ∑ j, |w j| = 1) (a : (Fin d → ℝ) → ℝ)
    (h : ∀ x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1),
      Integrable (fun w => a w * max (∑ j, w j * x j) 0) ν) :
    AEStronglyMeasurable a ν := by
  classical
  let e (j : Fin d) (s : ℝ) : Fin d → ℝ := fun k => if k = j then s else 0
  have he (j : Fin d) (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
      Integrable (fun w => a w * max (w j * s) 0) ν := by
    have hdot (w : Fin d → ℝ) : ∑ k, w k * e j s k = w j * s := by
      simp [e, mul_ite]
    simpa only [hdot] using h (e j s) (fun k _ => by
      by_cases hk : k = j <;> simp [e, hk, hs])
  have hj (j : Fin d) : Integrable (fun w => a w * max (w j) 0 + a w * max (-w j) 0) ν := by
    have hpos : Integrable (fun w => a w * max (w j) 0) ν := by
      simpa only [mul_one] using he j 1 (by norm_num)
    have hneg : Integrable (fun w => a w * max (-w j) 0) ν := by
      simpa only [mul_neg, mul_one] using he j (-1) (by norm_num)
    exact hpos.add hneg
  have hi : Integrable (fun w => ∑ j, (a w * max (w j) 0 + a w * max (-w j) 0)) ν :=
    integrable_finsetSum _ fun j _ => hj j
  refine hi.aestronglyMeasurable.congr ?_
  filter_upwards [hsphere] with w hw
  simp only [← mul_add, max_zero_add_max_neg_zero_eq_abs_self, ← Finset.mul_sum, hw, mul_one]

private lemma memLp_two_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (h₂ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp f 2 μ := by
  refine (memLp_two_iff_integrable_sq hf).2 ⟨(hf.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  simpa only [HasFiniteIntegral, eNorm_pow] using h₂

private lemma integral_sq_le_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) {γ : ℝ}
    (hγ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (γ ^ 2)) :
    ∫ x, f x ^ 2 ∂μ ≤ γ ^ 2 := by
  rw [← ENNReal.ofReal_le_ofReal_iff (sq_nonneg γ), ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf)
    (ae_of_all _ fun x => sq_nonneg (f x))]
  convert hγ using 1
  apply lintegral_congr
  intro x
  rw [← eNorm_pow, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]

private lemma integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ)
    {γ : ℝ} (hγ : 0 ≤ γ) (h₂ : ∫ x, f x ^ 2 ∂μ ≤ γ ^ 2) :
    ∫ x, |f x| ∂μ ≤ γ := by
  have h₁ := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := fun _ => (1 : ℝ)) (by simpa using hf)
    (memLp_const (μ := μ) (p := ENNReal.ofReal 2) (1 : ℝ))
  simp only [norm_one, mul_one, Real.norm_eq_abs, Real.rpow_two, sq_abs,
    one_pow, integral_const, probReal_univ, smul_eq_mul, Real.one_rpow] at h₁
  rw [← Real.sqrt_eq_rpow] at h₁
  exact h₁.trans ((Real.sqrt_le_sqrt h₂).trans_eq (Real.sqrt_sq hγ))

private lemma sample_mean {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun S : Fin m → α => (m : ℝ)⁻¹ * ∑ k, f (S k))
      (Measure.pi fun _ : Fin m => μ) ∧
    ∫ S : Fin m → α, (m : ℝ)⁻¹ * ∑ k, f (S k) ∂(Measure.pi fun _ : Fin m => μ) =
      ∫ x, f x ∂μ := by
  have he (k : Fin m) := measurePreserving_eval (fun _ : Fin m => μ) k
  have hi : ∀ k : Fin m, Integrable (fun S => f (S k)) (Measure.pi fun _ : Fin m => μ) :=
    fun k => (he k).integrable_comp_of_integrable hf
  have hm₀ : (m : ℝ) ≠ 0 := by positivity
  refine ⟨(integrable_finsetSum _ fun k _ => hi k).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun k _ => hi k]
  have hcomp (k : Fin m) : ∫ S, f (S k) ∂(Measure.pi fun _ : Fin m => μ) = ∫ x, f x ∂μ := by
    have hmf : AEStronglyMeasurable f ((Measure.pi fun _ : Fin m => μ).map (Function.eval k)) :=
      (he k).map_eq.symm ▸ hf.aestronglyMeasurable
    rw [← integral_map (he k).measurable.aemeasurable hmf, (he k).map_eq]
  simp only [hcomp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hm₀, one_mul]

private lemma sample_mean_sq_error {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) {f : α → ℝ} (hf : MemLp f 2 μ) :
    let P := Measure.pi fun _ : Fin m => μ
    let E := fun S : Fin m → α => ((m : ℝ)⁻¹ * ∑ k, f (S k) - ∫ x, f x ∂μ) ^ 2
    Integrable E P ∧ ∫ S, E S ∂P ≤ (m : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ := by
  dsimp only
  set P := Measure.pi fun _ : Fin m => μ
  let X (S : Fin m → α) := (m : ℝ)⁻¹ * ∑ k, f (S k)
  have hX : MemLp X 2 P := (memLp_finsetSum _ fun k _ =>
    hf.comp_measurePreserving (measurePreserving_eval _ k)).const_mul _
  have hmean : ∫ S, X S ∂P = ∫ x, f x ∂μ :=
    (sample_mean hm (hf.integrable one_le_two)).2
  change Integrable (fun S => (X S - _) ^ 2) P ∧
    ∫ S, (X S - _) ^ 2 ∂P ≤ _
  rw [← hmean, ← variance_eq_integral hX.aemeasurable]
  have hdiff : MemLp (fun S => X S - ∫ S, X S ∂P) 2 P := hX.sub (memLp_const _)
  refine ⟨(memLp_two_iff_integrable_sq hdiff.aestronglyMeasurable).1 hdiff, ?_⟩
  have hv := variance_sum_pi (μ := fun _ : Fin m => μ) (X := fun _ => f) (fun _ => hf)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hv
  have hvar : variance X P = (m : ℝ)⁻¹ * variance f μ := by
    calc variance X P = ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * variance f μ) := by
          dsimp only [X]
          rw [variance_const_mul, ← hv]
          have hsum : (fun S : Fin m → α => ∑ k, f (S k)) = ∑ k, fun S => f (S k) := by
            funext S
            simp [Finset.sum_apply]
          rw [hsum]
      _ = _ := by
        have hm₀ : (m : ℝ) ≠ 0 := by positivity
        field_simp
  rw [hvar]
  exact mul_le_mul_of_nonneg_left (variance_le_expectation_sq hf.aestronglyMeasurable)
    (by positivity)

private def squaredLoss (y t : ℝ) : ℝ := (clip t - clip y) ^ 2

private lemma measurable_squaredLoss {X : Type*} [MeasurableSpace X] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => squaredLoss (f x) (g x) :=
  ((lipschitz_clip.continuous.measurable.comp hg).sub
    (lipschitz_clip.continuous.measurable.comp hf)).pow_const 2

private noncomputable def empiricalLoss {d n m : ℕ} (f : (Fin d → ℝ) → ℝ) (S : Fin n → Fin d → ℝ)
    (b : Fin m → ℝ) (w : Fin m → Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, squaredLoss (f (S i)) (twoLayerReLU b w (S i))

/-- Integrating the comparison with i.i.d. neurons bounds the penalized empirical loss on
every sample in the cube. -/
private lemma empirical_objective_le {d n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    (hsphere : ∀ᵐ w ∂ν, ∑ j, |w j| = 1) (f a : (Fin d → ℝ) → ℝ)
    (hrep : ∀ x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1),
      Integrable (fun w => a w * max (∑ j, w j * x j) 0) ν ∧
        f x = ∫ w, a w * max (∑ j, w j * x j) 0 ∂ν)
    {γ lam : ℝ} (hγ : 0 ≤ γ) (h₂ : ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (γ ^ 2))
    (hlam : 0 ≤ lam) (S : Fin n → Fin d → ℝ)
    (hS : ∀ i, S i ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1))
    (b : Fin m → ℝ) (w : Fin m → Fin d → ℝ)
    (hmin : ∀ (b' : Fin m → ℝ) (w' : Fin m → Fin d → ℝ),
      empiricalLoss f S b w / 2 + lam * pathNorm b w ≤
        empiricalLoss f S b' w' / 2 + lam * pathNorm b' w') :
    empiricalLoss f S b w / 2 + lam * pathNorm b w ≤ γ ^ 2 / m / 2 + lam * γ := by
  set P := Measure.pi fun _ : Fin m => ν
  let c (W : Fin m → Fin d → ℝ) (k : Fin m) := (m : ℝ)⁻¹ * a (W k)
  have ha := memLp_two_of_lintegral
    (aestronglyMeasurable_coeff hsphere a fun x hx => (hrep x hx).1)
    (h₂.trans_lt ENNReal.ofReal_lt_top)
  have hsP : ∀ᵐ W ∂P, ∀ k, ∑ j, |W k j| = 1 := by
    rw [ae_all_iff]
    intro k
    have he := measurePreserving_eval (fun _ : Fin m => ν) k
    exact ae_of_ae_map he.measurable.aemeasurable (he.map_eq.symm ▸ hsphere)
  have hpath : (fun W => pathNorm (c W) W) =ᵐ[P]
      fun W => (m : ℝ)⁻¹ * ∑ k, |a (W k)| := by
    filter_upwards [hsP] with W hW
    simp only [pathNorm, c, hW, mul_one, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹),
      Finset.mul_sum]
  have haabs : Integrable (fun w => |a w|) ν := (ha.integrable one_le_two).abs
  obtain ⟨hiN, hEN⟩ := sample_mean hm haabs
  have hEN' : ∫ W, pathNorm (c W) W ∂P ≤ γ := by
    rw [integral_congr_ae hpath, hEN]
    exact integral_abs_le ha hγ (integral_sq_le_of_lintegral ha h₂)
  let E (i : Fin n) (W : Fin m → Fin d → ℝ) :=
    squaredLoss (f (S i)) (twoLayerReLU (c W) W (S i))
  have hE (i : Fin n) : Integrable (E i) P ∧ ∫ W, E i W ∂P ≤ γ ^ 2 / m := by
    let φ (w : Fin d → ℝ) := a w * max (∑ j, w j * S i j) 0
    obtain ⟨hφ, hmean⟩ := hrep (S i) (hS i)
    have hφ₂ : ∫⁻ w, ‖φ w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (γ ^ 2) := by
      refine (lintegral_mono_ae ?_).trans h₂
      filter_upwards [hsphere] with w hw
      have hneuron := abs_relu_le_l1 w (S i) (abs_le_one_of_mem_cube (hS i))
      rw [hw] at hneuron
      have hle : |φ w| ≤ |a w| := by
        dsimp only [φ]
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hneuron
      simp only [Real.eNorm_eq_ofReal_abs]
      gcongr
    have hp := memLp_two_of_lintegral hφ.aestronglyMeasurable (hφ₂.trans_lt ENNReal.ofReal_lt_top)
    let X (W : Fin m → Fin d → ℝ) := (m : ℝ)⁻¹ * ∑ k, φ (W k)
    have hX (W : Fin m → Fin d → ℝ) : twoLayerReLU (c W) W (S i) = X W := by
      simp only [twoLayerReLU, c, X, φ, Finset.mul_sum, mul_assoc]
    have hmX := (sample_mean hm hφ).1.aemeasurable
    have hi : Integrable (E i) P := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun W => ?_)
      · simp only [E, hX, squaredLoss]
        exact ((lipschitz_clip.continuous.measurable.comp_aemeasurable hmX).sub_const _
          |>.pow_const 2).aestronglyMeasurable
      · dsimp only [E, squaredLoss]
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact sq_loss_le _ _
    obtain ⟨hV, hEV⟩ := sample_mean_sq_error hm hp
    refine ⟨hi, (integral_mono hi hV fun W => ?_).trans (hEV.trans ?_)⟩
    · simp only [E, hX, squaredLoss, ← hmean]
      have h := lipschitz_clip.dist_le_mul (X W) (f (S i))
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    · rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (integral_sq_le_of_lintegral hp hφ₂) (by positivity)
  have hiEmp : Integrable (fun W => empiricalLoss f S (c W) W) P :=
    (integrable_finsetSum _ fun i _ => (hE i).1).const_mul _
  have hEE : ∫ W, empiricalLoss f S (c W) W ∂P ≤ γ ^ 2 / m := by
    change ∫ W, (n : ℝ)⁻¹ * ∑ i, E i W ∂P ≤ _
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hE i).1]
    calc _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, γ ^ 2 / m := by
            gcongr with i
            exact (hE i).2
      _ = _ := by
        have hn₀ : (n : ℝ) ≠ 0 := by positivity
        simp [← mul_assoc, inv_mul_cancel₀ hn₀]
  calc _ = ∫ _W : Fin m → Fin d → ℝ, empiricalLoss f S b w / 2 + lam * pathNorm b w ∂P := by simp
    _ ≤ ∫ W, empiricalLoss f S (c W) W / 2 + lam * pathNorm (c W) W ∂P :=
      integral_mono (integrable_const _) ((hiEmp.div_const _).add
        ((hiN.congr hpath.symm).const_mul _)) fun W => hmin (c W) W
    _ ≤ _ := by
      rw [integral_add (hiEmp.div_const _) ((hiN.congr hpath.symm).const_mul _),
        integral_div, integral_const_mul]
      gcongr

open Cslib.MachineLearning.Rademacher
open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype
  (rademacherSign average_rademacher_norm_le)

/-- The absolute correlations of the clipped losses are controlled by the two one-sided
correlations and the correlation of the loss at the zero network. -/
private lemma sample_loss_complexity_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {S : Fin n → Fin d → ℝ} (hS : ∀ i j, |S i j| ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q)
    (y : Fin n → ℝ) {ι : Type*} (v : ι → Fin n → ℝ)
    (hv : ∀ t, v t ∈ pathNormBallValues S Q) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ ε : Fin n → Bool,
        ⨆ t, |(1 / (n : ℝ)) * ∑ i, (if ε i then (1 : ℝ) else -1) *
          squaredLoss (y i) (v t i)| ≤
      8 * Q * √(2 * Real.log (2 * d) / n) + (√(n : ℝ))⁻¹ := by
  let A := pathNormBallValues S Q
  let B := coordMap (fun i => squaredLoss (y i)) '' A
  let b₀ : Fin n → ℝ := fun i => squaredLoss (y i) 0
  have hA : Bornology.IsBounded A := by
    refine isBounded_iff_forall_norm_le.2 ⟨Q, ?_⟩
    rintro _ ⟨m, a, w, hp, rfl⟩
    refine (pi_norm_le_iff_of_nonneg hQ).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact (abs_twoLayerReLU_le_pathNorm a w (S i) (hS i)).trans hp
  have hb₀ : b₀ ∈ B := ⟨0, ⟨0, Fin.elim0, Fin.elim0, by simp [pathNorm, hQ],
    by ext i; simp [twoLayerReLU]⟩, rfl⟩
  have hB : Bornology.IsBounded B :=
    isBounded_coordMap_image hA (show (0 : ℝ) ≤ 2 by norm_num) fun i s t => by
      simpa [Real.dist_eq, squaredLoss] using (lipschitz_sq_loss (y i)).dist_le_mul s t
  have hc := (rademacherComplexity_coordMap_le hA _ fun i => lipschitz_sq_loss (y i)).trans
    (mul_le_mul_of_nonneg_left (rademacherComplexity_pathNormBallValues_le hd hS hQ)
      (show (0 : ℝ) ≤ (2 : NNReal) by positivity))
  have hle (ε : Fin n → Bool) (b : Fin n → ℝ) (hb : b ∈ B) :
      signCorr ε b ≤ supCorr B ε :=
    le_csSup (bddAbove_signCorr_image hB ε) ⟨b, hb, rfl⟩
  have hn₀ : (0 : ℝ) < n := by positivity
  have hpoint (ε : Fin n → Bool) :
      (⨆ t, |(1 / (n : ℝ)) * ∑ i, (if ε i then (1 : ℝ) else -1) *
          squaredLoss (y i) (v t i)|) ≤
        (n : ℝ)⁻¹ * (supCorr B ε + supCorr B (flipSigns ε) + |signCorr ε b₀|) := by
    have hpos := hle ε b₀ hb₀
    have hneg := hle (flipSigns ε) b₀ hb₀
    rw [signCorr_flipSigns] at hneg
    have hbound : 0 ≤ supCorr B ε + supCorr B (flipSigns ε) + |signCorr ε b₀| :=
      by linarith [abs_nonneg (signCorr ε b₀)]
    refine Real.iSup_le ?_ (mul_nonneg (inv_nonneg.2 hn₀.le) hbound)
    intro t
    let b := coordMap (fun i => squaredLoss (y i)) (v t)
    have hb : b ∈ B := ⟨v t, hv t, rfl⟩
    have hp := hle ε b hb
    have hm := hle (flipSigns ε) b hb
    rw [signCorr_flipSigns] at hm
    change |(1 / (n : ℝ)) * signCorr ε b| ≤ _
    rw [one_div, abs_mul, abs_of_nonneg (inv_nonneg.2 hn₀.le)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hn₀.le)
    exact abs_le.2 ⟨by linarith [neg_abs_le (signCorr ε b₀)],
      by linarith [le_abs_self (signCorr ε b₀)]⟩
  have hbase : ((2 : ℝ) ^ n)⁻¹ * ∑ ε, |signCorr ε b₀| ≤ √(n : ℝ) := by
    have h := average_rademacher_norm_le (𝕜 := ℝ) n b₀
    simp only [signCorr, smul_eq_mul, Real.norm_eq_abs, sq_abs] at h ⊢
    refine h.trans (Real.sqrt_le_sqrt ?_)
    calc ∑ i, b₀ i ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hbi : b₀ i ≤ 1 := sq_loss_le _ _
            exact (pow_le_pow_left₀ (sq_nonneg _) hbi 2).trans_eq (by norm_num)
      _ = n := by simp
  have hsqrt : (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ))⁻¹ := by
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn₀
    field_simp
    exact Real.sq_sqrt hn₀.le
  calc _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ ε : Fin n → Bool,
        (n : ℝ)⁻¹ * (supCorr B ε + supCorr B (flipSigns ε) + |signCorr ε b₀|) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε _ => hpoint ε) (by positivity)
    _ = 2 * rademacherComplexity B +
        (n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ ε, |signCorr ε b₀|) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_flipSigns, rademacherComplexity]
      ring
    _ ≤ _ := by
      rw [← hsqrt]
      have hc' : rademacherComplexity B ≤ (2 : ℝ) * (2 * Q * √(2 * Real.log (2 * d) / n)) := hc
      linarith [mul_le_mul_of_nonneg_left hbase (inv_nonneg.2 hn₀.le)]

open TopologicalSpace
open MathlibExt.Probability.UniformLawsWanted (uniformDeviation
  uniformDeviation_le_two_mul_rademacherComplexity_add)

/-- Uniform control on a fixed path-norm ball. A countable dense subset suffices because
both the empirical and population loss are continuous in the network parameters. -/
private lemma uniform_loss {d n m : ℕ} (hd : 0 < d) (hn : 0 < n)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ x ∂ρ, x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) {Q δ : ℝ}
    (hQ : 0 ≤ Q) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => ρ)
      {S | (∀ i, S i ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)) ∧
        ∀ (b : Fin m → ℝ) (w : Fin m → Fin d → ℝ), pathNorm b w ≤ Q →
          (∫ x, squaredLoss (f x) (twoLayerReLU b w x) ∂ρ) ≤ empiricalLoss f S b w +
            (16 * Q * √(2 * Real.log (2 * d) / n) + 2 * (√(n : ℝ))⁻¹ +
              √(2 * Real.log (1 / δ) / n))} := by
  let P := Measure.pi fun _ : Fin n => ρ
  let Θ := {p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) // pathNorm p.1 p.2 ≤ Q}
  let F (p : Θ) (x : Fin d → ℝ) := squaredLoss (f x) (twoLayerReLU p.1.1 p.1.2 x)
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense Θ
  let _ : Countable D := hDc.to_subtype
  let G (p : D) := F p.1
  have hF (p : Θ) : Measurable (F p) := by
    have hnet : Continuous (twoLayerReLU p.1.1 p.1.2) := by
      unfold twoLayerReLU
      fun_prop
    exact measurable_squaredLoss hf hnet.measurable
  have hFc (x : Fin d → ℝ) : Continuous fun p => F p x := by
    have hnet : Continuous (fun p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) =>
        twoLayerReLU p.1 p.2 x) := by
      unfold twoLayerReLU
      fun_prop
    exact (((lipschitz_clip.continuous.comp (hnet.comp continuous_subtype_val)).sub
      continuous_const).pow 2)
  have hFbd (p : Θ) (x : Fin d → ℝ) : |F p x| ≤ 1 := by
    dsimp only [F, squaredLoss]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_loss_le _ _
  have hPop : Continuous fun p => ∫ x, F p x ∂ρ :=
    continuous_of_dominated (fun p => (hF p).aestronglyMeasurable)
      (fun p => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFbd p x)
      (integrable_const _) (ae_of_all _ hFc)
  have hPS : ∀ᵐ S ∂P, ∀ i, S i ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1) := by
    rw [ae_all_iff]
    intro i
    have he := measurePreserving_eval (fun _ : Fin n => ρ) i
    exact ae_of_ae_map he.measurable.aemeasurable (he.map_eq.symm ▸ hρ)
  let r := √(2 * Real.log (2 * d) / n)
  let K := 8 * Q * r + (√(n : ℝ))⁻¹
  let u := √(2 * Real.log (1 / δ) / n)
  let R := MathlibExt.Probability.UniformLawsWanted.rademacherComplexity ρ G hn
  have hR : R ≤ K := by
    rw [show K = ∫ _S, K ∂P by simp]
    dsimp only [R, MathlibExt.Probability.UniformLawsWanted.rademacherComplexity]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ fun S => by
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun ε _ => Real.iSup_nonneg fun _ => abs_nonneg _)
    · exact integrable_const _
    · filter_upwards [hPS] with S hS
      let v (p : D) (i : Fin n) := twoLayerReLU p.1.1.1 p.1.1.2 (S i)
      have hv (p : D) : v p ∈ pathNormBallValues S Q := ⟨m, _, _, p.1.2, rfl⟩
      exact sample_loss_complexity_le hd hn (fun i => abs_le_one_of_mem_cube (hS i)) hQ
        (fun i => f (S i)) v hv
  have hExp : Real.exp (-(n : ℝ) * u ^ 2 / (2 * (1 : ℝ) ^ 2)) = δ := by
    have hn₀ : (0 : ℝ) < n := by positivity
    have harg : (1 : ℝ) ≤ 1 / δ := by simpa only [le_div_iff₀ hδ, one_mul] using hδ₁.le
    rw [show u ^ 2 = 2 * Real.log (1 / δ) / n from
      Real.sq_sqrt (by positivity [Real.log_nonneg harg])]
    have hexp : -(n : ℝ) * (2 * Real.log (1 / δ) / n) / (2 * (1 : ℝ) ^ 2) =
        Real.log δ := by
      rw [one_pow, mul_one, Real.log_div (by norm_num) hδ.ne', Real.log_one]
      field_simp
      ring
    rw [hexp, Real.exp_log hδ]
  have hprob := uniformDeviation_le_two_mul_rademacherComplexity_add ρ G
    (fun p => hF p.1) (b := 1) zero_lt_one (fun p => hFbd p.1) hn
    (show 0 ≤ u from Real.sqrt_nonneg _)
  rw [hExp] at hprob
  let good := {S | uniformDeviation ρ G hn S ≤ 2 * R + u}
  have hgood : 1 - ENNReal.ofReal δ ≤ P good := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hδ.le, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hprob
  calc _ ≤ P good := hgood
    _ = P {S | S ∈ good ∧ ∀ i, S i ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)} := by
      apply measure_congr
      filter_upwards [hPS] with S hS
      exact (and_iff_left hS).symm
    _ ≤ _ := by
      apply measure_mono
      rintro S ⟨hgoodS, hS⟩
      refine ⟨hS, ?_⟩
      let A (p : Θ) := (n : ℝ)⁻¹ * ∑ i, F p (S i)
      let H (p : Θ) := |A p - ∫ x, F p x ∂ρ|
      have hAc : Continuous A := continuous_const.mul
        (continuous_finsetSum _ fun i _ => hFc (S i))
      have hHc : Continuous H := (hAc.sub hPop).abs
      have hAbd (p : Θ) : |A p| ≤ 1 := by
        have hn₀ : (n : ℝ) ≠ 0 := by positivity
        dsimp only [A]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
        calc _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) :=
              mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun i _ => hFbd p (S i))) (by positivity)
          _ = 1 := by simp [inv_mul_cancel₀ hn₀]
      have hHbd : BddAbove (Set.range H) := by
        refine ⟨2, ?_⟩
        rintro _ ⟨p, rfl⟩
        have hPbd : |∫ x, F p x ∂ρ| ≤ 1 := by
          rw [← Real.norm_eq_abs]
          simpa using norm_integral_le_of_norm_le_const (μ := ρ) (f := F p) (C := 1)
            (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFbd p x)
        exact (abs_sub _ _).trans (by linarith [hAbd p, hPbd])
      have hsup : (⨆ p : D, H p.1) = ⨆ p : Θ, H p := hD.ciSup hHc hHbd
      intro b w hp
      let p : Θ := ⟨(b, w), hp⟩
      have hdev : H p ≤ 2 * R + u := by
        refine (le_ciSup hHbd p).trans ?_
        rw [← hsup]
        simpa only [good, Set.mem_ofPred_eq, uniformDeviation, one_div] using hgoodS
      change ∫ x, F p x ∂ρ ≤ A p + _
      have hdiff := (abs_le.1 hdev).1
      change -(2 * R + u) ≤ A p - ∫ x, F p x ∂ρ at hdiff
      dsimp only [K, r, u] at hR
      linarith

end TwoLayerAPriori

open TwoLayerAPriori

@[expose] public section

/-- **A priori estimate of the population risk for two-layer ReLU networks** (W. E, C. Ma and
L. Wu, *A priori estimates of the population risk for two-layer neural networks*, Commun. Math.
Sci. 17 (2019), Theorem 4.1, noiseless case). There is an absolute constant `C` such that the
following holds. Let `log (2d) ≥ 1`, `n ≥ 1`, `m ≥ 1`, let `ρ_x` be a probability measure
carried by `[-1, 1]^d`, and let `f*` be measurable with values in `[0, 1]` on `[-1, 1]^d` and
`f*(x) = ∫ a(w) max(⟨w, x⟩, 0) dπ(w)` there, for a probability measure `π` carried by the `ℓ¹`
unit sphere and `∫ |a|² dπ ≤ γ²`, `γ ≥ 0`. Let `λ ≥ 4 √(2 log (2d) / n)` and `δ > 0`. Then with
probability at least `1 - δ` over an i.i.d. sample `x₁, …, xₙ ∼ ρ_x`, every minimizer `θ̂` over
width-`m` networks of `J_λ(θ) = (1/n) ∑ᵢ ½ (T f(xᵢ; θ) - f*(xᵢ))² + λ (‖θ‖_P + 1)`, where
`T t = max (min t 1) 0` truncates to `[0, 1]`, satisfies
`𝔼_x |T f(x; θ̂) - f*(x)|² ≤ C (γ² / m + λ max(1, γ) + (max(1, γ) + √(log (n / δ))) / √n)`. -/
theorem twoLayer_a_priori_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n m : ℕ), 1 ≤ Real.log (2 * d) → 0 < n → 0 < m →
      ∀ (ρx : Measure (Fin d → ℝ)), IsProbabilityMeasure ρx →
      ρx (Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1)ᶜ = 0 →
      ∀ (fstar : (Fin d → ℝ) → ℝ), Measurable fstar →
      (∀ x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1), fstar x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (ν : Measure (Fin d → ℝ)), IsProbabilityMeasure ν → (∀ᵐ w ∂ν, ∑ j, |w j| = 1) →
      ∀ (a : (Fin d → ℝ) → ℝ),
      (∀ x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1),
        Integrable (fun w => a w * max (∑ j, w j * x j) 0) ν ∧
          fstar x = ∫ w, a w * max (∑ j, w j * x j) 0 ∂ν) →
      ∀ γ : ℝ, 0 ≤ γ → ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (γ ^ 2) →
      ∀ (lam δ : ℝ), 4 * √(2 * Real.log (2 * d) / n) ≤ lam → 0 < δ →
      1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => ρx)
        {S | ∀ (â : Fin m → ℝ) (ŵ : Fin m → Fin d → ℝ),
          (∀ (a' : Fin m → ℝ) (w' : Fin m → Fin d → ℝ),
            (n : ℝ)⁻¹ * ∑ i, (max (min (twoLayerReLU â ŵ (S i)) 1) 0 - fstar (S i)) ^ 2 / 2 +
                lam * (pathNorm â ŵ + 1) ≤
              (n : ℝ)⁻¹ * ∑ i, (max (min (twoLayerReLU a' w' (S i)) 1) 0 - fstar (S i)) ^ 2 / 2 +
                lam * (pathNorm a' w' + 1)) →
          ∫⁻ x, ENNReal.ofReal ((max (min (twoLayerReLU â ŵ x) 1) 0 - fstar x) ^ 2) ∂ρx ≤
            ENNReal.ofReal (C * (γ ^ 2 / m + lam * max 1 γ +
              (max 1 γ + √(Real.log (n / δ))) / √(n : ℝ)))} := by
  refine ⟨10, by norm_num, ?_⟩
  intro d n m hd hn hm ρx hρx hcube fstar hfstar htarget ν hν hsphere a hrep γ hγ h₂ lam δ hlam hδ
  by_cases hlarge : 1 ≤ δ
  · rw [tsub_eq_zero_of_le (ENNReal.one_le_ofReal.2 hlarge)]
    exact zero_le
  have hδ₁ := lt_of_not_ge hlarge
  let _ : IsProbabilityMeasure ρx := hρx
  let _ : IsProbabilityMeasure ν := hν
  have hd₀ : 0 < d := by
    by_contra! h
    have he : d = 0 := Nat.eq_zero_of_le_zero h
    norm_num [he] at hd
  have hn₀ : (0 : ℝ) < n := by positivity
  have hr : 0 < √(2 * Real.log (2 * d) / n) :=
    Real.sqrt_pos.2 (div_pos (mul_pos (by norm_num) (by linarith)) hn₀)
  have hlam₀ : 0 < lam := by linarith
  let B : ℝ := γ ^ 2 / m / 2 + lam * γ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let Q := B / lam
  have hQ : 0 ≤ Q := div_nonneg hB hlam₀.le
  have hBQ : Q * lam = B := div_mul_cancel₀ _ hlam₀.ne'
  have hρ := ae_iff.2 hcube
  refine (uniform_loss (m := m) hd₀ hn ρx hρ fstar hfstar hQ hδ hδ₁).trans (measure_mono ?_)
  rintro S ⟨hS, hdev⟩ b w hmin
  have hobj := empirical_objective_le hn hm hsphere fstar a hrep hγ h₂ hlam₀.le S hS b w
    (fun b' w' => by
      have h (c : Fin m → ℝ) (v : Fin m → Fin d → ℝ) :
          empiricalLoss fstar S c v / 2 =
            (n : ℝ)⁻¹ * ∑ i, (clip (twoLayerReLU c v (S i)) - fstar (S i)) ^ 2 / 2 := by
        simp only [empiricalLoss, squaredLoss, clip_eq (htarget _ (hS _)),
          Finset.sum_div, mul_div_assoc]
      have hi := hmin b' w'
      change _ + lam * (pathNorm b w + 1) ≤ _ + lam * (pathNorm b' w' + 1) at hi
      rw [h, h]
      unfold clip
      linarith)
  change _ ≤ B at hobj
  have hEmp : 0 ≤ empiricalLoss fstar S b w := by
    unfold empiricalLoss squaredLoss
    positivity
  have hp : pathNorm b w ≤ Q := by
    apply (le_div_iff₀ hlam₀).2
    linarith
  have hEmpB : empiricalLoss fstar S b w ≤ 2 * B := by
    linarith [mul_nonneg hlam₀.le (pathNorm_nonneg b w)]
  have hrad : 16 * Q * √(2 * Real.log (2 * d) / n) ≤ 4 * B := by
    calc _ = (4 * Q) * (4 * √(2 * Real.log (2 * d) / n)) := by ring
      _ ≤ (4 * Q) * lam := mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = 4 * B := by rw [mul_assoc, hBQ]
  have hlog : Real.log (1 / δ) ≤ Real.log (n / δ) :=
    Real.log_le_log (by positivity) (by gcongr; exact_mod_cast (show 1 ≤ n from hn))
  have hlog₀ : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by simpa only [le_div_iff₀ hδ, one_mul] using hδ₁.le)
  have hconf : √(2 * Real.log (1 / δ) / n) ≤ 2 * √(Real.log (n / δ)) / √(n : ℝ) := by
    rw [Real.sqrt_div' _ hn₀.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
    · exact Real.sqrt_le_left (by norm_num) |>.2 (by norm_num)
  have hstat : 2 * (√(n : ℝ))⁻¹ + √(2 * Real.log (1 / δ) / n) ≤
      2 * ((max 1 γ + √(Real.log (n / δ))) / √(n : ℝ)) := by
    calc _ ≤ 2 * (√(n : ℝ))⁻¹ + 2 * √(Real.log (n / δ)) / √(n : ℝ) :=
          add_le_add le_rfl hconf
      _ = 2 * ((1 + √(Real.log (n / δ))) / √(n : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hB' : B ≤ γ ^ 2 / m + lam * max 1 γ := by
    dsimp only [B]
    apply add_le_add
    · linarith [show 0 ≤ γ ^ 2 / (m : ℝ) by positivity]
    · exact mul_le_mul_of_nonneg_left (le_max_right 1 γ) hlam₀.le
  have hL : (∫ x, squaredLoss (fstar x) (twoLayerReLU b w x) ∂ρx) ≤
      10 * (γ ^ 2 / m + lam * max 1 γ + (max 1 γ + √(Real.log (n / δ))) / √(n : ℝ)) := by
    linarith [hdev b w hp, show 0 ≤ γ ^ 2 / (m : ℝ) by positivity,
      mul_nonneg hlam₀.le ((zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_left 1 γ)),
      show 0 ≤ (max 1 γ + √(Real.log (n / δ))) / √(n : ℝ) by positivity]
  have hmeas : Measurable (fun x => squaredLoss (fstar x) (twoLayerReLU b w x)) := by
    have hnet : Continuous (twoLayerReLU b w) := by unfold twoLayerReLU; fun_prop
    exact measurable_squaredLoss hfstar hnet.measurable
  have hi := Integrable.mono' (integrable_const (1 : ℝ))
    (μ := ρx) hmeas.aestronglyMeasurable (ae_of_all _ fun x => by
      change ‖(clip (twoLayerReLU b w x) - clip (fstar x)) ^ 2‖ ≤ 1
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_loss_le _ _)
  calc
    ∫⁻ x, ENNReal.ofReal ((max (min (twoLayerReLU b w x) 1) 0 - fstar x) ^ 2) ∂ρx =
        ∫⁻ x, ENNReal.ofReal (squaredLoss (fstar x) (twoLayerReLU b w x)) ∂ρx := by
      refine lintegral_congr_ae ?_
      filter_upwards [hρ] with x hx
      simp only [squaredLoss, clip_eq (htarget x hx)]
      rfl
    _ = ENNReal.ofReal (∫ x, squaredLoss (fstar x) (twoLayerReLU b w x) ∂ρx) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hL

end

end CSLibExt.MachineLearning.GeneralizationBounds
