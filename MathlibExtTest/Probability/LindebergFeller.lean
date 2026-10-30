/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LindebergFeller
public import Mathlib.Probability.ProductMeasure

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Finset Set
open scoped Topology BoundedContinuousFunction NNReal ENNReal

namespace MathlibExtTest.LindebergFeller

/-- The fair coin measure on `Bool`: mass `1/2` on `true` and on `false`. -/
noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _)]
  rw [← two_mul, mul_one, one_div]
  exact ENNReal.mul_inv_cancel (by positivity) (by simp)

/-- Integration against the fair coin is the average of the two values. -/
lemma integral_fairCoin (f : Bool → ℝ) :
    ∫ b, f b ∂fairCoin = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  have htrue : fairCoin.real {true} = 1 / 2 := by simp [fairCoin, Measure.real]
  have hfalse : fairCoin.real {false} = 1 / 2 := by simp [fairCoin, Measure.real]
  rw [hfalse, htrue]
  simp only [smul_eq_mul]
  ring

/-- The Rademacher variable on the `k`-th coordinate of the coin-flip space:
`+1` on heads, `-1` on tails. -/
noncomputable def rademacher (k : ℕ) (ω : ℕ → Bool) : ℝ := if ω k then 1 else -1

/-- The scaled triangular array: the `k`-th Rademacher variable divided by `√n`. -/
noncomputable def scaledRademacher (n k : ℕ) (ω : ℕ → Bool) : ℝ :=
  rademacher k ω / Real.sqrt n

/-- The Rademacher variable has square `1` everywhere. -/
lemma rademacher_sq (k : ℕ) (ω : ℕ → Bool) : (rademacher k ω) ^ 2 = 1 := by
  unfold rademacher
  split_ifs <;> norm_num

/-- Each scaled Rademacher variable is measurable. -/
lemma measurable_scaledRademacher (n k : ℕ) :
    Measurable (scaledRademacher n k) := by
  unfold scaledRademacher rademacher
  refine Measurable.div_const ?_ _
  exact Measurable.ite
    (MeasurableSet.preimage (measurableSet_singleton true) (measurable_pi_apply k))
    measurable_const measurable_const

/-- The Rademacher variable on a single coordinate has mean zero. -/
lemma integral_rademacher (k : ℕ) :
    ∫ ω, rademacher k ω ∂(Measure.infinitePi (fun _ : ℕ => fairCoin)) = 0 := by
  have hfun : (fun ω : ℕ → Bool => rademacher k ω) =
      (fun ω => (fun b : Bool => if b then (1 : ℝ) else -1) (ω k)) := by
    funext ω
    rfl
  have h2 : (∫ ω, (fun b : Bool => if b then (1 : ℝ) else -1) (ω k)
      ∂Measure.infinitePi (fun _ : ℕ => fairCoin)) =
      ∫ b, (fun b : Bool => if b then (1 : ℝ) else -1) b ∂fairCoin := by
    have h : (∫ b, (fun b : Bool => if b then (1 : ℝ) else -1) b
        ∂Measure.map (fun ω : ℕ → Bool => ω k)
          (Measure.infinitePi (fun _ : ℕ => fairCoin))) =
        ∫ ω, (fun b : Bool => if b then (1 : ℝ) else -1) (ω k)
          ∂Measure.infinitePi (fun _ : ℕ => fairCoin) :=
      integral_map (measurable_pi_apply k).aemeasurable
        (measurable_of_finite _).aestronglyMeasurable
    rw [Measure.infinitePi_map_eval] at h
    exact h.symm
  rw [hfun, h2, integral_fairCoin]
  simp

/-- The Bernoulli coordinates of the infinite coin-flip space are independent.
Proved from `iIndepFun_iff_measure_inter_preimage_eq_mul`: a finite intersection
of coordinate preimages is a cylinder, whose `Measure.pi` measure is the
product of the coordinate measures (`Measure.pi_pi_finset`). -/
lemma iIndepFun_rademacher :
    iIndepFun rademacher (Measure.infinitePi (fun _ : ℕ => fairCoin)) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hInter : ⋂ i ∈ S, rademacher i ⁻¹' sets i =
      (S : Set ℕ).pi (fun i =>
        (fun b : Bool => if b then (1 : ℝ) else -1) ⁻¹' sets i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_pi]
    constructor
    · intro h i hi
      exact h i hi
    · intro h i hi
      exact h i hi
  have hmt : ∀ i ∈ S, MeasurableSet
      ((fun b : Bool => if b then (1 : ℝ) else -1) ⁻¹' sets i) :=
    fun i hi => MeasurableSet.preimage (hsets i hi) (measurable_of_finite _)
  rw [hInter, Measure.infinitePi_pi (fun _ : ℕ => fairCoin) hmt]
  apply Finset.prod_congr rfl
  intro i hi
  have hY : Measurable (fun b : Bool => if b then (1 : ℝ) else -1) :=
    measurable_of_finite _
  have hpre : MeasurableSet
      ((fun b : Bool => if b then (1 : ℝ) else -1) ⁻¹' sets i) := hY (hsets i hi)
  have hpre2 : rademacher i ⁻¹' sets i =
      (fun ω : ℕ → Bool => ω i) ⁻¹'
        ((fun b : Bool => if b then (1 : ℝ) else -1) ⁻¹' sets i) := rfl
  rw [hpre2, ← Measure.map_apply (measurable_pi_apply i) hpre,
    Measure.infinitePi_map_eval]

/-- The rows of the scaled array are independent. -/
lemma iIndepFun_scaledRademacher (n : ℕ) :
    iIndepFun (scaledRademacher n) (Measure.infinitePi (fun _ : ℕ => fairCoin)) := by
  have hcomp := iIndepFun_rademacher.comp (fun _ (y : ℝ) => y / Real.sqrt n)
    (fun _ => Measurable.div_const measurable_id _)
  apply hcomp.congr
  intro k
  filter_upwards with ω
  simp [scaledRademacher]

/-- Each scaled Rademacher variable has mean zero. -/
lemma integral_scaledRademacher (n k : ℕ) :
    ∫ ω, scaledRademacher n k ω ∂(Measure.infinitePi (fun _ : ℕ => fairCoin)) = 0 := by
  unfold scaledRademacher
  rw [integral_div, integral_rademacher]
  simp

/-- Each scaled Rademacher variable is square-integrable. -/
lemma integrable_sq_scaledRademacher (n k : ℕ) :
    Integrable (fun ω => (scaledRademacher n k ω) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => fairCoin)) := by
  have h2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [show (fun ω => (scaledRademacher n k ω) ^ 2) = (fun _ => (1 : ℝ) / n) from
    funext fun ω => by
      rw [scaledRademacher, div_pow, rademacher_sq, h2]]
  exact integrable_const _

/-- Each scaled Rademacher variable has second moment `1 / n`. -/
lemma integral_sq_scaledRademacher (n k : ℕ) :
    ∫ ω, (scaledRademacher n k ω) ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => fairCoin))
      = 1 / n := by
  have h2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have h : ∀ ω : ℕ → Bool, (scaledRademacher n k ω) ^ 2 = 1 / n := by
    intro ω
    rw [scaledRademacher, div_pow, rademacher_sq, h2]
  simp_rw [h]
  rw [integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- The scaled Rademacher array satisfies the Lindeberg condition. -/
lemma lindeberg_scaledRademacher :
    LindebergConditionTriangular scaledRademacher
      (Measure.infinitePi (fun _ : ℕ => fairCoin)) := by
  intro ε hε
  -- For `n` large, `|X n k| = 1 / √n ≤ ε`, so every truncation set is empty.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
  have hNpos : 0 < N := by
    exact_mod_cast lt_trans (show (0 : ℝ) < 1 / ε ^ 2 by positivity) hN
  refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
  intro n hn
  have hn0 : 0 < n := lt_of_lt_of_le hNpos hn
  have hsqrt : (1 : ℝ) / ε ≤ Real.sqrt n := by
    have h1 : (1 : ℝ) / ε ^ 2 ≤ (n : ℝ) := by
      have hN' : (1 : ℝ) / ε ^ 2 < (N : ℝ) := hN
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h2 : (1 : ℝ) / ε = Real.sqrt (1 / ε ^ 2) := by
      rw [show (1 : ℝ) / ε ^ 2 = (1 / ε) ^ 2 by rw [div_pow, one_pow],
        Real.sqrt_sq (by positivity)]
    rw [h2]
    exact Real.sqrt_le_sqrt h1
  apply Finset.sum_eq_zero
  intro k _
  have hset : {ω : ℕ → Bool | ε < |scaledRademacher n k ω|} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    have hω' : ε < |scaledRademacher n k ω| := hω
    have habs : |scaledRademacher n k ω| = 1 / Real.sqrt n := by
      rw [scaledRademacher, abs_div,
        abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hn0 : (0 : ℝ) < (n : ℝ)))]
      have h1 : |rademacher k ω| = 1 := by
        unfold rademacher
        split_ifs <;> norm_num
      rw [h1]
    rw [habs] at hω'
    have hle : (1 : ℝ) / Real.sqrt n ≤ ε :=
      calc (1 : ℝ) / Real.sqrt n ≤ 1 / (1 / ε) :=
            one_div_le_one_div_of_le (by positivity) hsqrt
        _ = ε := one_div_one_div ε
    exact not_lt_of_ge hle hω'
  rw [hset]
  simp

/-- The row variances of the scaled Rademacher array converge to `1`. -/
lemma tendsto_sum_sq_scaledRademacher :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      ∫ ω, (scaledRademacher n k ω) ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => fairCoin)))
      atTop (𝓝 (1 ^ 2)) := by
  refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
  intro n hn
  rw [Finset.sum_congr rfl (fun k _ => integral_sq_scaledRademacher n k)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mul_one_div, div_self hn', one_pow]

/-- **End-to-end test**: the Lindeberg–Feller theorem applied to the scaled
Rademacher array. The row sums converge in distribution to the standard normal. -/
example : ∀ f : ℝ →ᵇ ℝ,
    Tendsto (fun n => ∫ x, f x ∂(Measure.map
      (fun ω => ∑ k ∈ Finset.range n, scaledRademacher n k ω)
      (Measure.infinitePi (fun _ : ℕ => fairCoin))))
      atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 ⟨1 ^ 2, sq_nonneg 1⟩))) := by
  apply lindeberg_feller_clt_triangular scaledRademacher
    (fun n => (iIndepFun_scaledRademacher n).restrict (Finset.range n))
    (fun n k _ => measurable_scaledRademacher n k)
    (fun n k _ => integral_scaledRademacher n k)
    (fun n k _ => integrable_sq_scaledRademacher n k) 1 zero_lt_one
    tendsto_sum_sq_scaledRademacher lindeberg_scaledRademacher

/-- The quadratic Taylor bound for `exp` on `‖x‖ ≤ 1`, at a concrete point. -/
example : ‖Complex.exp (↑(1 / 2 : ℝ) * Complex.I) - 1 - ↑(1 / 2 : ℝ) * Complex.I‖
    ≤ (1 / 2 : ℝ) ^ 2 :=
  norm_exp_ofReal_mul_I_sub_one_sub_le (by norm_num)

/-- The Lindeberg condition holds trivially for the zero array. -/
example : LindebergConditionTriangular (fun _ _ _ => (0 : ℝ))
    (Measure.infinitePi (fun _ : ℕ => fairCoin)) := by
  intro ε _
  simp

end MathlibExtTest.LindebergFeller
