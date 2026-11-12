/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Posterior consistency in a finite model

`weightLaw g` is the law `∑ x, ENNReal.ofReal (g x) • δ_x` on a finite space, and
`postWeight π f X n ω θ` is the posterior probability of `θ` after the first `n` observations in
the finite model with prior weights `π` and likelihoods `f θ x`.

`ae_tendsto_postWeight_one`: with finite parameter and observation spaces, positive prior mass at
the truth `θ₀`, strictly positive normalized likelihoods, positive Kullback–Leibler separation of
`f θ₀` from every other `f θ`, and pairwise independent observations with law `f θ₀`, the
posterior probability of `θ₀` tends to `1` almost surely (strong law of large numbers applied to
the log-likelihood ratios).

No link to a kernel posterior, no Bernstein–von Mises statement, and no misspecified model is
covered.

## References

* J. L. Doob (1949); D. A. Freedman, Ann. Math. Statist. 34 (1963).
* S. Ghosal and A. van der Vaart, *Fundamentals of Nonparametric Bayesian Inference*, Cambridge
  University Press, 2017, Chapter 6.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Bayesian

open MeasureTheory ProbabilityTheory Filter Topology

/-- The law on a finite space `𝓧` with real point masses `g x`:
`∑ x, ENNReal.ofReal (g x) • δ_x`. For `g ≥ 0` with `∑ x, g x = 1` it is a probability measure
(`isProbabilityMeasure_weightLaw`). -/
noncomputable def weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧] (g : 𝓧 → ℝ) :
    Measure 𝓧 :=
  ∑ x, ENNReal.ofReal (g x) • Measure.dirac x

/-- Posterior probability of `θ` after the first `n` observations `X 0 ω, …, X (n - 1) ω` in the
finite model with prior weights `π` and likelihoods `f θ x`:
`π θ * ∏_{i<n} f θ (X i ω) / ∑_{θ'} π θ' * ∏_{i<n} f θ' (X i ω)`. -/
noncomputable def postWeight {Θ 𝓧 Ω : Type*} [Fintype Θ] (π : Θ → ℝ) (f : Θ → 𝓧 → ℝ)
    (X : ℕ → Ω → 𝓧) (n : ℕ) (ω : Ω) (θ : Θ) : ℝ :=
  (π θ * ∏ i ∈ Finset.range n, f θ (X i ω)) /
    ∑ θ', π θ' * ∏ i ∈ Finset.range n, f θ' (X i ω)

private lemma integral_weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] (g : 𝓧 → ℝ) (hg : ∀ x, 0 ≤ g x) (φ : 𝓧 → ℝ) :
    ∫ x, φ x ∂(weightLaw g) = ∑ x, g x * φ x := by
  rw [weightLaw, integral_finsetSum_measure fun x _ =>
    (Integrable.of_finite (μ := Measure.dirac x)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hg x), smul_eq_mul]

/-- Strong law for the log-likelihood ratio: likelihood-ratio products against a
KL-separated truth `g₀` tend to `0` almost surely. -/
private lemma ae_tendsto_prod_ratio_zero {𝓧 Ω : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    [DiscreteMeasurableSpace 𝓧] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (g g₀ : 𝓧 → ℝ) [IsFiniteMeasure (weightLaw g₀)] (hg : ∀ x, 0 < g x) (hg₀ : ∀ x, 0 < g₀ x)
    (hKL : 0 < ∑ x, g₀ x * Real.log (g₀ x / g x))
    (X : ℕ → Ω → 𝓧) (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = weightLaw g₀)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => ∏ i ∈ Finset.range n, (g (X i ω) / g₀ (X i ω))) atTop (𝓝 0) := by
  let φ : 𝓧 → ℝ := fun x => Real.log (g x / g₀ x)
  have hφ : Measurable φ := Measurable.of_discrete
  let Y : ℕ → Ω → ℝ := fun i => φ ∘ X i
  have hint : Integrable (Y 0) μ := by
    have : Integrable φ (μ.map (X 0)) := by rw [hlaw 0]; exact Integrable.of_finite
    exact this.comp_measurable (hX 0)
  have hindepY : Pairwise fun i j => IndepFun (Y i) (Y j) μ := fun i j hij =>
    (hindep hij).comp hφ hφ
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i =>
    (IdentDistrib.mk (hX i).aemeasurable (hX 0).aemeasurable ((hlaw i).trans (hlaw 0).symm)).comp
      hφ
  have hmean : ∫ ω, Y 0 ω ∂μ = -∑ x, g₀ x * Real.log (g₀ x / g x) := by
    change ∫ ω, φ (X 0 ω) ∂μ = _
    rw [← integral_map (hX 0).aemeasurable hφ.aestronglyMeasurable, hlaw 0,
      integral_weightLaw g₀ fun x => (hg₀ x).le, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_neg, ← Real.log_inv, inv_div]
  filter_upwards [strong_law_ae_real Y hint hindepY hident] with ω hω
  rw [hmean] at hω
  have hS : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, Y i ω) atTop atBot := by
    refine (hω.neg_mul_atTop (neg_neg_of_pos hKL) tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)
  refine (Real.tendsto_exp_atBot.comp hS).congr fun n => ?_
  rw [Function.comp_apply, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => Real.exp_log (div_pos (hg _) (hg₀ _))

/-- Deterministic part: if every likelihood-ratio product against `θ₀` tends to `0`, the
posterior weight of `θ₀` tends to `1`. -/
private lemma tendsto_postWeight_one_of_ratio {Θ 𝓧 Ω : Type*} [Fintype Θ] (π : Θ → ℝ)
    (hπ_nonneg : ∀ θ, 0 ≤ π θ) (θ₀ : Θ) (hπ₀ : 0 < π θ₀) (f : Θ → 𝓧 → ℝ)
    (hf_pos : ∀ θ x, 0 < f θ x) (X : ℕ → Ω → 𝓧) (ω : Ω)
    (hR : ∀ θ, θ ≠ θ₀ →
      Tendsto (fun n => ∏ i ∈ Finset.range n, (f θ (X i ω) / f θ₀ (X i ω))) atTop (𝓝 0)) :
    Tendsto (fun n => postWeight π f X n ω θ₀) atTop (𝓝 1) := by
  classical
  have hP_pos : ∀ θ n, 0 < ∏ i ∈ Finset.range n, f θ (X i ω) := fun θ n =>
    Finset.prod_pos fun i _ => hf_pos θ (X i ω)
  have hA_pos : ∀ n, 0 < π θ₀ * ∏ i ∈ Finset.range n, f θ₀ (X i ω) := fun n =>
    mul_pos hπ₀ (hP_pos θ₀ n)
  have hA_le : ∀ n, π θ₀ * ∏ i ∈ Finset.range n, f θ₀ (X i ω) ≤
      ∑ θ', π θ' * ∏ i ∈ Finset.range n, f θ' (X i ω) := fun n =>
    Finset.single_le_sum (f := fun θ' => π θ' * ∏ i ∈ Finset.range n, f θ' (X i ω))
      (fun θ' _ => mul_nonneg (hπ_nonneg θ') (hP_pos θ' n).le) (Finset.mem_univ θ₀)
  have hD_pos : ∀ n, 0 < ∑ θ', π θ' * ∏ i ∈ Finset.range n, f θ' (X i ω) := fun n =>
    (hA_pos n).trans_le (hA_le n)
  have hother : ∀ θ ∈ Finset.univ.erase θ₀,
      Tendsto (fun n => postWeight π f X n ω θ) atTop (𝓝 0) := by
    intro θ hθ
    have hlim := (hR θ (Finset.ne_of_mem_erase hθ)).const_mul (π θ / π θ₀)
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => ?_)
      (fun n => ?_)
    · exact div_nonneg (mul_nonneg (hπ_nonneg θ) (hP_pos θ n).le) (hD_pos n).le
    · dsimp only
      rw [postWeight, Finset.prod_div_distrib, div_mul_div_comm]
      exact div_le_div_of_nonneg_left (mul_nonneg (hπ_nonneg θ) (hP_pos θ n).le) (hA_pos n)
        (hA_le n)
  have hsum : ∀ n, 1 - ∑ θ ∈ Finset.univ.erase θ₀, postWeight π f X n ω θ =
      postWeight π f X n ω θ₀ := by
    intro n
    have h1 : ∑ θ, postWeight π f X n ω θ = 1 := by
      unfold postWeight
      rw [← Finset.sum_div]
      exact div_self (hD_pos n).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ θ₀)] at h1
    linarith
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (tendsto_finsetSum _ hother)
  rw [Finset.sum_const_zero, sub_zero] at hlim
  exact hlim.congr hsum

/-- Nonnegative point masses summing to one give a probability measure. -/
theorem isProbabilityMeasure_weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] (g : 𝓧 → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_sum : ∑ x, g x = 1) :
    IsProbabilityMeasure (weightLaw g) := by
  constructor
  rw [weightLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hg_nonneg x), hg_sum, ENNReal.ofReal_one]

/-- **Posterior consistency in a finite model.** Finite parameter and observation spaces, a prior
with positive mass at the truth `θ₀`, strictly positive normalized likelihoods, positive
Kullback–Leibler separation of `f θ₀` from every other `f θ`, and pairwise independent
observations with common law `f θ₀`: the posterior probability of `θ₀` tends to `1` almost surely.

Source: J. L. Doob (1949); D. A. Freedman, Ann. Math. Statist. 34 (1963); S. Ghosal and
A. van der Vaart, *Fundamentals of Nonparametric Bayesian Inference* (2017), Chapter 6. -/
theorem ae_tendsto_postWeight_one {Θ 𝓧 Ω : Type*} [Fintype Θ] [Fintype 𝓧]
    [MeasurableSpace 𝓧] [DiscreteMeasurableSpace 𝓧] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (π : Θ → ℝ) (hπ_nonneg : ∀ θ, 0 ≤ π θ) (θ₀ : Θ) (hπ₀ : 0 < π θ₀)
    (f : Θ → 𝓧 → ℝ) (hf_pos : ∀ θ x, 0 < f θ x) (hf_sum : ∀ θ, ∑ x, f θ x = 1)
    (hKL : ∀ θ, θ ≠ θ₀ → 0 < ∑ x, f θ₀ x * Real.log (f θ₀ x / f θ x))
    (X : ℕ → Ω → 𝓧) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = weightLaw (f θ₀))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => postWeight π f X n ω θ₀) atTop (𝓝 1) := by
  have := isProbabilityMeasure_weightLaw (f θ₀) (fun x => (hf_pos θ₀ x).le) (hf_sum θ₀)
  have hR : ∀ᵐ ω ∂μ, ∀ θ, θ ≠ θ₀ →
      Tendsto (fun n => ∏ i ∈ Finset.range n, (f θ (X i ω) / f θ₀ (X i ω))) atTop (𝓝 0) := by
    refine ae_all_iff.2 fun θ => ?_
    by_cases hθ : θ = θ₀
    · exact Eventually.of_forall fun ω h => absurd hθ h
    · filter_upwards [ae_tendsto_prod_ratio_zero (f θ) (f θ₀) (hf_pos θ) (hf_pos θ₀) (hKL θ hθ)
        X hX hlaw hindep] with ω hω _ using hω
  filter_upwards [hR] with ω hω
  exact tendsto_postWeight_one_of_ratio π hπ_nonneg θ₀ hπ₀ f hf_pos X ω hω

end MathlibExt.Probability.Statistics.Bayesian





namespace MathlibExt.Probability.Statistics.Bayesian

open MeasureTheory ProbabilityTheory Filter Topology

/-- Bernoulli mass function on `Fin 2`: `1 - p` at `0`, `p` at `1`. -/
noncomputable def bernPMF (p : ℝ) : Fin 2 → ℝ :=
  fun x => if x = 0 then 1 - p else p

/-- Binary KL positivity for distinct biases in `(0, 1)`. -/
private theorem binary_KL_pos {p₀ p₁ : ℝ} (h₀ : 0 < p₀) (h₀' : p₀ < 1)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1) (hne : p₀ ≠ p₁) :
    0 < ∑ x, bernPMF p₀ x * Real.log (bernPMF p₀ x / bernPMF p₁ x) := by
  have hg₀ : ∀ x, 0 < bernPMF p₀ x := fun x => by
    unfold bernPMF
    by_cases hx : x = 0 <;> simp [hx] <;> linarith
  have hg₁ : ∀ x, 0 < bernPMF p₁ x := fun x => by
    unfold bernPMF
    by_cases hx : x = 0 <;> simp [hx] <;> linarith
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hv : ∀ p : ℝ, bernPMF p 1 = p := fun p => by simp [bernPMF, h10]
  have hle : ∀ x, bernPMF p₀ x * Real.log (bernPMF p₁ x / bernPMF p₀ x)
      ≤ bernPMF p₁ x - bernPMF p₀ x := fun x => by
    have hpos : 0 < bernPMF p₁ x / bernPMF p₀ x := div_pos (hg₁ x) (hg₀ x)
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hg₀ne : bernPMF p₀ x ≠ 0 := ne_of_gt (hg₀ x)
    calc bernPMF p₀ x * Real.log (bernPMF p₁ x / bernPMF p₀ x)
        ≤ bernPMF p₀ x * (bernPMF p₁ x / bernPMF p₀ x - 1) :=
          mul_le_mul_of_nonneg_left hlog (hg₀ x).le
      _ = bernPMF p₁ x - bernPMF p₀ x := by field_simp
  have hlt1 : bernPMF p₀ 1 * Real.log (bernPMF p₁ 1 / bernPMF p₀ 1)
      < bernPMF p₁ 1 - bernPMF p₀ 1 := by
    have hpos : 0 < bernPMF p₁ 1 / bernPMF p₀ 1 := div_pos (hg₁ 1) (hg₀ 1)
    have hratio : bernPMF p₁ 1 / bernPMF p₀ 1 ≠ 1 := by
      rw [hv, hv]
      intro h
      apply hne
      exact ((div_eq_one_iff_eq (ne_of_gt h₀)).mp h).symm
    have hlog := Real.log_lt_sub_one_of_pos hpos hratio
    have hg₀ne : bernPMF p₀ 1 ≠ 0 := ne_of_gt (hg₀ 1)
    calc bernPMF p₀ 1 * Real.log (bernPMF p₁ 1 / bernPMF p₀ 1)
        < bernPMF p₀ 1 * (bernPMF p₁ 1 / bernPMF p₀ 1 - 1) := by
          apply mul_lt_mul_of_pos_left hlog (hg₀ 1)
      _ = bernPMF p₁ 1 - bernPMF p₀ 1 := by field_simp
  have hsum₀ : ∑ x : Fin 2, bernPMF p₀ x = 1 := by
    rw [Fin.sum_univ_two]
    simp only [bernPMF]
    simp [h10]
  have hsum₁ : ∑ x : Fin 2, bernPMF p₁ x = 1 := by
    rw [Fin.sum_univ_two]
    simp only [bernPMF]
    simp [h10]
  have hS : ∑ x : Fin 2, bernPMF p₀ x * Real.log (bernPMF p₁ x / bernPMF p₀ x) < 0 := by
    rw [Fin.sum_univ_two]
    have h0 := hle 0
    have hsum_eq : (bernPMF p₁ 0 - bernPMF p₀ 0) + (bernPMF p₁ 1 - bernPMF p₀ 1) = 0 := by
      have h : ∑ x : Fin 2, (bernPMF p₁ x - bernPMF p₀ x) = 0 := by
        rw [Finset.sum_sub_distrib, hsum₁, hsum₀, sub_self]
      rw [Fin.sum_univ_two] at h
      exact h
    have hlt := add_lt_add_of_le_of_lt h0 hlt1
    rw [hsum_eq] at hlt
    exact hlt
  have hneg : ∑ x : Fin 2, bernPMF p₀ x * Real.log (bernPMF p₁ x / bernPMF p₀ x)
      = -(∑ x : Fin 2, bernPMF p₀ x * Real.log (bernPMF p₀ x / bernPMF p₁ x)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_neg, ← Real.log_inv, inv_div]
  linarith

/-- **Two-parameter Bernoulli posterior consistency.** With truth `p₀` and alternative `p₁`
distinct biases in `(0, 1)`, unit prior weights, and pairwise independent Bernoulli(`p₀`)
observations, the posterior weight of the truth tends to `1` almost surely. -/
theorem twoPoint_postWeight_tendsto_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p₀ p₁ : ℝ}
    (h₀ : 0 < p₀) (h₀' : p₀ < 1) (h₁ : 0 < p₁) (h₁' : p₁ < 1) (hne : p₀ ≠ p₁)
    (X : ℕ → Ω → Fin 2) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = weightLaw (bernPMF p₀))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => postWeight (fun _ : Fin 2 => (1 : ℝ))
        (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) X n ω (0 : Fin 2))
      atTop (𝓝 1) := by
  have hpos₀ : ∀ x : Fin 2, 0 < bernPMF p₀ x := fun x => by
    unfold bernPMF
    by_cases hx : x = 0 <;> simp [hx] <;> linarith
  have hpos₁ : ∀ x : Fin 2, 0 < bernPMF p₁ x := fun x => by
    unfold bernPMF
    by_cases hx : x = 0 <;> simp [hx] <;> linarith
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hsum₀ : ∑ x : Fin 2, bernPMF p₀ x = 1 := by
    rw [Fin.sum_univ_two]
    simp only [bernPMF]
    simp [h10]
  have hsum₁ : ∑ x : Fin 2, bernPMF p₁ x = 1 := by
    rw [Fin.sum_univ_two]
    simp only [bernPMF]
    simp [h10]
  have h00 : (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) (0 : Fin 2)
      = bernPMF p₀ := rfl
  have hf_pos : ∀ θ x,
      0 < (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) θ x := fun θ x => by
    by_cases hθ : θ = 0
    · subst hθ
      change 0 < bernPMF p₀ x
      exact hpos₀ x
    · change 0 < bernPMF (if θ = 0 then p₀ else p₁) x
      simp only [hθ, ite_false]
      exact hpos₁ x
  have hf_sum : ∀ θ,
      ∑ x, (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) θ x = 1 := fun θ => by
    by_cases hθ : θ = 0
    · subst hθ
      change ∑ x : Fin 2, bernPMF p₀ x = 1
      exact hsum₀
    · change ∑ x : Fin 2, bernPMF (if θ = 0 then p₀ else p₁) x = 1
      simp only [hθ, ite_false]
      exact hsum₁
  have hKL : ∀ θ, θ ≠ (0 : Fin 2) →
      0 < ∑ x, (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) 0 x *
        Real.log ((fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) 0 x /
          (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) θ x) := fun θ hθ => by
    have hθ1 : θ = 1 := (by decide : ∀ θ : Fin 2, θ ≠ 0 → θ = 1) θ hθ
    rw [hθ1]
    have h11 : (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) 1
        = bernPMF p₁ := by
      change bernPMF (if (1 : Fin 2) = 0 then p₀ else p₁) = bernPMF p₁
      simp [h10]
    rw [h00, h11]
    exact binary_KL_pos h₀ h₀' h₁ h₁' hne
  have hlaw' : ∀ i, μ.map (X i) =
      weightLaw ((fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁)) 0) := by
    change ∀ i, μ.map (X i) = weightLaw (bernPMF p₀)
    exact hlaw
  exact ae_tendsto_postWeight_one (fun _ : Fin 2 => (1 : ℝ)) (fun _ => zero_le_one)
    (0 : Fin 2) zero_lt_one
    (fun θ : Fin 2 => bernPMF (if θ = 0 then p₀ else p₁))
    hf_pos hf_sum hKL X hX hlaw' hindep

end MathlibExt.Probability.Statistics.Bayesian
