/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import MathlibExt.Probability.Concentration.McDiarmidPi
public import MathlibExt.Probability.KernelMeanEmbedding

/-!
# Concentration of the biased empirical MMD

The kernel two-sample test of Gretton, Borgwardt, Rasch, Schölkopf and Smola compares two
samples through the biased empirical maximum mean discrepancy `MMD_b` (the distance between
the empirical kernel mean embeddings, `KernelMeanEmbedding.mmdBiased_eq`). For a kernel with
values in `[0, K]`, `MMD_b` concentrates around the population `MMD` at rate
`O(√(1/m) + √(1/n))`, uniformly over the distributions: this is what makes the test
distribution-free and consistent against every fixed alternative. The paper combines McDiarmid's
bounded-difference inequality with a symmetrization (Rademacher-average) bound for the unit
ball of the RKHS. Here we bound the expected embedding errors by their second moments and
apply McDiarmid's inequality to each centered error.

Reference: A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, "A kernel
two-sample test", *J. Mach. Learn. Res.* **13** (2012), 723–773, Theorem 7 (proved in
Appendix A.2).
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.KernelMeanEmbedding

namespace MathlibExt.Probability.KernelTwoSampleTestWanted

open ProbabilityTheory
open scoped InnerProductSpace NNReal

section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- In the second moment of a sum of centered observations, the off-diagonal terms vanish. -/
private lemma integral_norm_sum_le {f : X → H} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) (μ : Measure X) [IsProbabilityMeasure μ]
    (hzero : ∫ x, f x ∂μ = 0) (m : ℕ) :
    ∫ z, ‖∑ i : Fin m, f (z i)‖ ∂(Measure.pi fun _ : Fin m => μ) ≤ √(m * C ^ 2) := by
  classical
  borelize H
  let P := Measure.pi fun _ : Fin m => μ
  let W (i : Fin m) (z : Fin m → X) := f (z i)
  have hm (i) : StronglyMeasurable (W i) := hf.comp_measurable (measurable_pi_apply i)
  have hL (i) : MemLp (W i) 2 P :=
    .of_bound (hm i).aestronglyMeasurable C (.of_forall fun z => hb (z i))
  have hmean (i) : ∫ z, W i z ∂P = 0 := by
    change ∫ z, f (Function.eval i z) ∂P = 0
    rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply i) hf,
      (measurePreserving_eval (fun _ : Fin m => μ) i).map_eq, hzero]
  have hind : iIndepFun W P :=
    iIndepFun_pi (μ := fun _ : Fin m => μ) (X := fun _ => f) fun _ => hf.measurable.aemeasurable
  have hint (i j) : Integrable (fun z => ⟪W i z, W j z⟫_ℝ) P := by
    refine .of_bound ((hm i).inner (hm j)).aestronglyMeasurable (C * C) (.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hb (z i)) (hb (z j)) (norm_nonneg _) hC)
  have hterm (i j) : ∫ z, ⟪W i z, W j z⟫_ℝ ∂P ≤ if i = j then C ^ 2 else 0 := by
    split_ifs with hij
    · simpa [pow_two] using (integral_mono (hint i j) (integrable_const (C * C)) fun z =>
        (real_inner_le_norm _ _).trans
          (mul_le_mul (hb (z i)) (hb (z j)) (norm_nonneg _) hC))
    · have h := (hind.indepFun hij).integral_bilin ((hL i).integrable (by norm_num))
          ((hL j).integrable (by norm_num)) (innerSL ℝ)
      change (∫ z, ⟪W i z, W j z⟫_ℝ ∂P) = ⟪∫ z, W i z ∂P, ∫ z, W j z ∂P⟫_ℝ at h
      simp [h, hmean]
  let S (z : Fin m → X) := ∑ i, W i z
  have hsq : ∫ z, ‖S z‖ ^ 2 ∂P ≤ m * C ^ 2 := by
    simp only [S, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint j i]
    simp_rw [integral_finsetSum _ fun j _ => hint j _]
    calc
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, (if j = i then C ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm j i
      _ = _ := by simp
  have hS : MemLp (fun z => ‖S z‖) 2 P := (memLp_finsetSum _ fun i _ => hL i).norm
  have hv := variance_nonneg (fun z => ‖S z‖) P
  rw [variance_eq_sub hS] at hv
  exact Real.le_sqrt_of_sq_le ((sub_nonneg.mp hv).trans hsq)

variable [RKHS ℝ H X ℝ]

variable (H) in
private noncomputable def embeddingError (μ : Measure X)
    {m : ℕ} [NeZero m] (z : Fin m → X) : ℝ :=
  ‖empiricalEmbedding H z - meanEmbedding H μ‖

private lemma measurable_embeddingError (hφ : StronglyMeasurable (featureMap H))
    (μ : Measure X) {m : ℕ} [NeZero m] :
    Measurable (embeddingError H μ (m := m)) := by
  have hs := Finset.stronglyMeasurable_fun_sum (Finset.univ : Finset (Fin m))
    fun i _ => hφ.comp_measurable (measurable_pi_apply i)
  exact ((hs.const_smul (m : ℝ)⁻¹).sub stronglyMeasurable_const).norm.measurable

private lemma integral_embeddingError_le (hφ : StronglyMeasurable (featureMap H))
    (b : ℝ≥0) (hb : ∀ x, ‖featureMap H x‖ ≤ b) (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) [NeZero m] :
    ∫ z, embeddingError H μ z ∂(Measure.pi fun _ : Fin m => μ) ≤ 2 * b / √m := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hint : Integrable (featureMap H) μ := .of_bound hφ.aestronglyMeasurable b (.of_forall hb)
  have hmean : ‖meanEmbedding H μ‖ ≤ b := by
    simpa [meanEmbedding] using norm_integral_le_of_norm_le_const (μ := μ) (.of_forall hb)
  let f (x : X) := featureMap H x - meanEmbedding H μ
  have hzero : ∫ x, f x ∂μ = 0 := by simp [f, integral_sub hint (integrable_const _), meanEmbedding]
  have hbound (x) : ‖f x‖ ≤ 2 * b := by
    exact (norm_sub_le _ _).trans (by linarith [hb x])
  have hsum := integral_norm_sum_le (hφ.sub stronglyMeasurable_const) (by positivity)
    hbound μ hzero m
  have heq (z : Fin m → X) : embeddingError H μ z = (m : ℝ)⁻¹ * ‖∑ i, f (z i)‖ := by
    rw [embeddingError, empiricalEmbedding, ← Real.norm_of_nonneg (inv_nonneg.mpr hm.le),
      ← norm_smul]
    congr 1
    simp [f, Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hm.ne']
  simp_rw [heq, integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hm.le)).trans_eq ?_
  rw [Real.sqrt_mul hm.le, Real.sqrt_sq (by positivity : 0 ≤ 2 * (b : ℝ))]
  have hs := Real.sq_sqrt hm.le
  have hp := Real.sqrt_pos.2 hm
  field_simp
  nlinarith only [congrArg (fun t : ℝ => t * b) hs]

private lemma embeddingError_update_le (b : ℝ≥0) (hb : ∀ x, ‖featureMap H x‖ ≤ b)
    (μ : Measure X) {m : ℕ} [NeZero m] (z : Fin m → X) (i : Fin m) (y : X) :
    |embeddingError H μ (Function.update z i y) - embeddingError H μ z| ≤ 2 * b / m := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  unfold embeddingError
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [sub_sub_sub_cancel_right, empiricalEmbedding, empiricalEmbedding, ← smul_sub,
    ← Finset.sum_sub_distrib]
  have hsum : (∑ j, (featureMap H (Function.update z i y j) - featureMap H (z j))) =
      featureMap H y - featureMap H (z i) := by
    rw [Finset.sum_eq_single i]
    · rw [Function.update_self]
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp
  rw [hsum, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm.le), div_eq_inv_mul]
  gcongr
  exact (norm_sub_le _ _).trans (by linarith [hb y, hb (z i)])

private lemma embeddingError_subgaussian (hφ : StronglyMeasurable (featureMap H))
    (b : ℝ≥0) (hb : ∀ x, ‖featureMap H x‖ ≤ b) (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) [NeZero m] :
    HasSubgaussianMGF
      (fun z => embeddingError H μ z - ∫ w, embeddingError H μ w ∂(Measure.pi fun _ : Fin m => μ))
      (b ^ 2 / m) (Measure.pi fun _ : Fin m => μ) := by
  have h := hasSubgaussianMGF_sub_integral_of_bounded_differences
    (μ := fun _ : Fin m => μ) (c := fun _ => 2 * b / m) (measurable_embeddingError hφ μ)
    (fun z i y => by exact_mod_cast embeddingError_update_le b hb μ z i y)
  convert h using 1
  ext
  push_cast
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  field_simp
  ring

end

/-- **Large-deviation bound for the biased empirical MMD** (Gretton, Borgwardt, Rasch,
Schölkopf and Smola, *A kernel two-sample test*, JMLR 13 (2012), Theorem 7). Let `H` be a real
RKHS on a measurable space `X` whose feature map is strongly measurable and whose kernel
satisfies `0 ≤ k(x, y) ≤ K`. Let `m, n ≥ 1`, let `X = (x₁, …, x_m)` be i.i.d. with law `P` and
`Y = (y₁, …, y_n)` i.i.d. with law `Q`, independent of `X`. Then for every `ε > 0`,
`Pr{|MMD_b[X, Y] - MMD[P, Q]| > 2 (√(K/m) + √(K/n)) + ε} ≤ 2 exp(-ε² m n / (2K(m + n)))`. -/
theorem measureReal_abs_mmdBiased_sub_mmd_gt_le {X : Type*} [MeasurableSpace X]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H X ℝ] (hφ : StronglyMeasurable (featureMap H)) {K : ℝ}
    (hk : ∀ x y, 0 ≤ kernelValue H x y ∧ kernelValue H x y ≤ K)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m n : ℕ} [NeZero m] [NeZero n] {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)).real
        {z | 2 * (√(K / m) + √(K / n)) + ε < |mmdBiased H z.1 z.2 - mmd H μ ν|} ≤
      2 * Real.exp (-(ε ^ 2 * m * n / (2 * K * (m + n)))) := by
  obtain ⟨x₀⟩ := μ.nonempty_of_neZero
  have hK : 0 ≤ K := (hk x₀ x₀).1.trans (hk x₀ x₀).2
  let b : ℝ≥0 := ⟨√K, Real.sqrt_nonneg _⟩
  have hb (x : X) : ‖featureMap H x‖ ≤ b := by
    rw [norm_featureMap]
    exact Real.sqrt_le_sqrt (hk x x).2
  have hInt (ρ : Measure X) [IsProbabilityMeasure ρ] : Integrable (featureMap H) ρ :=
    .of_bound hφ.aestronglyMeasurable b (.of_forall hb)
  let P := Measure.pi fun _ : Fin m => μ
  let Q := Measure.pi fun _ : Fin n => ν
  let F (z : Fin m → X) := embeddingError H μ z - ∫ x, embeddingError H μ x ∂P
  let G (z : Fin n → X) := embeddingError H ν z - ∫ y, embeddingError H ν y ∂Q
  have hF : HasSubgaussianMGF (F ∘ Prod.fst) (b ^ 2 / m) (P.prod Q) := by
    apply HasSubgaussianMGF.of_map measurable_fst.aemeasurable
    simpa [F, P] using embeddingError_subgaussian hφ b hb μ m
  have hG : HasSubgaussianMGF (G ∘ Prod.snd) (b ^ 2 / n) (P.prod Q) := by
    apply HasSubgaussianMGF.of_map measurable_snd.aemeasurable
    simpa [G, Q] using embeddingError_subgaussian hφ b hb ν n
  have hi := indepFun_prod (μ := P) (ν := Q)
    ((measurable_embeddingError (m := m) hφ μ).sub_const (∫ x, embeddingError H μ x ∂P))
    ((measurable_embeddingError (m := n) hφ ν).sub_const (∫ y, embeddingError H ν y ∂Q))
  have htail := (hF.add_of_indepFun hG hi).measure_ge_le hε.le
  calc
    _ ≤ (P.prod Q).real {z | ε ≤ F z.1 + G z.2} := by
      refine measureReal_mono ?_
      intro z hz
      have hdev : |mmdBiased H z.1 z.2 - mmd H μ ν| ≤
          embeddingError H μ z.1 + embeddingError H ν z.2 := by
        rw [mmdBiased_eq, mmd_eq_norm_sub (hInt μ) (hInt ν)]
        refine (abs_norm_sub_norm_le _ _).trans ?_
        rw [sub_sub_sub_comm]
        exact norm_sub_le _ _
      have hm := integral_embeddingError_le hφ b hb μ m
      have hn := integral_embeddingError_le hφ b hb ν n
      change 2 * (√(K / m) + √(K / n)) + ε < _ at hz
      simp only [Real.sqrt_div hK] at hz
      change ε ≤ (_ - _) + (_ - _)
      have hbias : (∫ x, embeddingError H μ x ∂P) + (∫ y, embeddingError H ν y ∂Q) ≤
          2 * (√K / √m + √K / √n) := by
        rw [mul_add, ← mul_div_assoc, ← mul_div_assoc]
        exact add_le_add hm hn
      linarith only [hz, hdev, hbias]
    _ ≤ _ := htail
    _ ≤ _ := by
      push_cast
      change Real.exp (-(ε ^ 2) / (2 * ((√K) ^ 2 / m + (√K) ^ 2 / n))) ≤ _
      rw [Real.sq_sqrt hK]
      have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
      have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      have heq : -(ε ^ 2) / (2 * (K / m + K / n)) =
          -(ε ^ 2 * m * n / (2 * K * (m + n))) := by
        rw [div_add_div _ _ hm hn, ← mul_div_assoc, div_div_eq_mul_div]
        ring_nf
      rw [heq]
      linarith [Real.exp_pos (-(ε ^ 2 * m * n / (2 * K * (m + n))))]

end MathlibExt.Probability.KernelTwoSampleTestWanted
