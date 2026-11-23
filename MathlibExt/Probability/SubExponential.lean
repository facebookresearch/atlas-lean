/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sub-exponential random variables and Bernstein's inequality

Following Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge
University Press, 2019), §2.1.3, a real random variable `X` is **sub-exponential with parameters
`(ν, α)`** when its moment generating function satisfies `E[exp (t X)] ≤ exp (ν² t² / 2)` for every
`|t| < 1 / α`. Unlike a sub-Gaussian variable, the bound is only required on a
neighbourhood of zero, which allows exponential rather than Gaussian tails. As in Mathlib's
`ProbabilityTheory.HasSubgaussianMGF`, the definition concerns `X` itself: apply it to
`X - E[X]` for the centred notion of the source. The interval of admissible `t` is written
`α |t| < 1`, so `α = 0` gives all `t`, the sub-Gaussian case.

## Main results

* `HasSubexponentialMGF`: the definition; `HasSubgaussianMGF.hasSubexponentialMGF`: a
  sub-Gaussian variable with variance proxy `c` is sub-exponential with parameters `(√c, α)` for
  every `α`.
* `HasSubexponentialMGF.measureReal_ge_le_of_le` and
  `HasSubexponentialMGF.measureReal_ge_le_of_ge`: the **sub-exponential tail bound** (Wainwright
  2019, §2.1.3; Rinaldo 2017, Theorem 3.2): `P(X ≥ t) ≤ exp (-t² / (2 ν²))` for
  `0 ≤ t ≤ ν² / α`, and `P(X ≥ t) ≤ exp (-t / (2 α))` for `t ≥ ν² / α`.
* `HasSubexponentialMGF.sum_of_iIndepFun`: a finite sum of independent sub-exponential variables
  with parameters `(νᵢ, α)` is sub-exponential with parameters `(√(∑ νᵢ²), α)` (Wainwright 2019,
  §2.1.3, with a common `α`; Rinaldo 2017, Lemma 3.6).
* `mgf_le_of_abs_le`: **Bernstein's moment generating function bound** for a bounded variable
  (Wainwright 2019, §2.1.3, and Rinaldo 2017, Theorem 3.4, in the case `|X| ≤ b`, which satisfies
  the Bernstein
  condition with parameter `b`): if `|X| ≤ b`, `E[X] = 0` and `E[X²] ≤ σ²`, then
  `E[exp (t X)] ≤ exp (t² σ² / (2 (1 - b |t|)))` for `b |t| < 1`.
* `measureReal_ge_le_bernstein` and `measureReal_abs_ge_le_bernstein`: **Bernstein's inequality**
  for such a variable (Wainwright 2019, §2.1.3; Rinaldo 2017, Theorem 3.5):
  `P(X ≥ t) ≤ exp (-t² / (2 (σ² + b t)))` and `P(|X| ≥ t) ≤ 2 exp (-t² / (2 (σ² + b t)))` for
  `t ≥ 0`.

An open account of the same statements, with the same constants, is A. Rinaldo, *36-755 Advanced
Statistics Theory I*, Lecture 3 (Carnegie Mellon, 2017), Definition 3.1 and Theorems 3.2, 3.4,
3.5 and Lemma 3.6.
-/

open MeasureTheory Real Filter Topology
open scoped NNReal

namespace ProbabilityTheory

@[expose] public section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {ν α : ℝ≥0}

/-- A real random variable `X` is **sub-exponential with parameters `(ν, α)`** under `μ` if for
every `t` with `α |t| < 1` the function `exp (t X)` is integrable and
`E[exp (t X)] ≤ exp (ν² t² / 2)` (Wainwright, *High-Dimensional Statistics*, 2019, §2.1.3;
Rinaldo 2017, Definition 3.1; for the variable `X` itself, apply it to `X - E[X]` for the centred
notion).
For `α = 0` the condition holds for all `t`, which is the sub-Gaussian condition with variance
proxy `ν²`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (ν α : ℝ≥0) (μ : Measure Ω) : Prop where
  integrable_exp_mul : ∀ t : ℝ, α * |t| < 1 → Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, α * |t| < 1 → mgf X μ t ≤ exp (ν ^ 2 * t ^ 2 / 2)

/-- A sub-Gaussian variable with variance proxy `c` is sub-exponential with parameters
`(√c, α)` for every `α` (Wainwright, *High-Dimensional Statistics*, 2019, §2.1.3; Rinaldo 2017,
remark after Definition 3.1: sub-Gaussian variables are sub-exponential). -/
lemma HasSubgaussianMGF.hasSubexponentialMGF {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    (α : ℝ≥0) : HasSubexponentialMGF X (NNReal.sqrt c) α μ where
  integrable_exp_mul t _ := h.integrable_exp_mul t
  mgf_le t _ := by
    have hc : ((NNReal.sqrt c : ℝ≥0) : ℝ) ^ 2 = c := by
      rw [Real.coe_sqrt, Real.sq_sqrt (NNReal.coe_nonneg c)]
    rw [hc]
    exact h.mgf_le t

namespace HasSubexponentialMGF

/-- The Chernoff step for a sub-exponential variable: for every `0 ≤ s` with `α s ≤ 1`,
`P(X ≥ t) ≤ exp (-s t + ν² s² / 2)`. The endpoint `s = 1 / α` is reached by continuity. -/
lemma measureReal_ge_le_exp [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X ν α μ)
    (t : ℝ) {s : ℝ} (hs : 0 ≤ s) (hαs : α * s ≤ 1) :
    μ.real {ω | t ≤ X ω} ≤ exp (-s * t + ν ^ 2 * s ^ 2 / 2) := by
  -- The interior case `α s < 1`.
  have hint : ∀ s : ℝ, 0 ≤ s → α * s < 1 →
      μ.real {ω | t ≤ X ω} ≤ exp (-s * t + ν ^ 2 * s ^ 2 / 2) := by
    intro s hs hαs
    have habs : α * |s| < 1 := by rwa [abs_of_nonneg hs]
    calc μ.real {ω | t ≤ X ω} ≤ exp (-s * t) * mgf X μ s :=
          measure_ge_le_exp_mul_mgf t hs (h.integrable_exp_mul s habs)
      _ ≤ exp (-s * t) * exp (ν ^ 2 * s ^ 2 / 2) := by
          gcongr; exact h.mgf_le s habs
      _ = exp (-s * t + ν ^ 2 * s ^ 2 / 2) := by rw [← exp_add]
  rcases hαs.lt_or_eq with hlt | heq
  · exact hint s hs hlt
  -- The endpoint `s = 1 / α`, with `α > 0`, as a limit from the left.
  have hα : (0 : ℝ) < α := by
    rcases (NNReal.coe_nonneg α).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at heq; exact absurd heq zero_ne_one
  have hs0 : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at heq; exact absurd heq zero_ne_one
  have hcont : Tendsto (fun u : ℝ ↦ exp (-u * t + ν ^ 2 * u ^ 2 / 2)) (𝓝[<] s)
      (𝓝 (exp (-s * t + ν ^ 2 * s ^ 2 / 2))) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((by fun_prop : Continuous fun u : ℝ ↦
      exp (-u * t + ν ^ 2 * u ^ 2 / 2)).tendsto s)
  refine ge_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsLT hs0] with u hu
  refine hint u hu.1.le ?_
  calc (α : ℝ) * u < α * s := mul_lt_mul_of_pos_left hu.2 hα
    _ = 1 := heq

/-- **Sub-exponential tail bound, Gaussian regime** (Wainwright, *High-Dimensional Statistics*,
2019, §2.1.3; Rinaldo 2017, Theorem 3.2): if `X` is sub-exponential with parameters `(ν, α)` and
`0 ≤ t ≤ ν² / α` (with `t` arbitrary nonnegative when `α = 0`), then
`P(X ≥ t) ≤ exp (-t² / (2 ν²))`. -/
lemma measureReal_ge_le_of_le [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X ν α μ)
    {t : ℝ} (ht : 0 ≤ t) (htα : α * t ≤ ν ^ 2) :
    μ.real {ω | t ≤ X ω} ≤ exp (-t ^ 2 / (2 * ν ^ 2)) := by
  rcases (sq_nonneg (ν : ℝ)).lt_or_eq with hν | hν
  · have hb := h.measureReal_ge_le_exp t (s := t / ν ^ 2) (by positivity) (by
      rw [mul_div_assoc', div_le_one hν]; exact htα)
    convert hb using 2
    field_simp
    ring
  · rw [← hν, mul_zero, div_zero, exp_zero]
    exact measureReal_le_one

/-- **Sub-exponential tail bound, exponential regime** (Wainwright, *High-Dimensional
Statistics*, 2019, §2.1.3; Rinaldo 2017, Theorem 3.2): if `X` is sub-exponential with parameters
`(ν, α)`, `α > 0`
and `t ≥ ν² / α`, then `P(X ≥ t) ≤ exp (-t / (2 α))`. -/
lemma measureReal_ge_le_of_ge [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X ν α μ)
    (hα : 0 < α) {t : ℝ} (htα : ν ^ 2 ≤ α * t) :
    μ.real {ω | t ≤ X ω} ≤ exp (-t / (2 * α)) := by
  have hα' : (0 : ℝ) < α := hα
  have hb := h.measureReal_ge_le_exp t (s := 1 / α) (by positivity) (by field_simp; rfl)
  refine hb.trans (exp_le_exp.mpr ?_)
  rw [div_pow, one_pow]
  have : (ν : ℝ) ^ 2 * (1 / (α : ℝ) ^ 2) / 2 ≤ t / (2 * α) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (ν : ℝ) ^ 2 * (1 / α ^ 2) * (2 * α) = 2 * (ν ^ 2 / α) := by field_simp
    rw [this]
    have : (ν : ℝ) ^ 2 / α ≤ t := by rw [div_le_iff₀ hα']; linarith
    nlinarith
  have h2 : -(1 / (α : ℝ)) * t = -t / α := by ring
  rw [h2]
  have h3 : -t / (α : ℝ) + t / (2 * α) = -t / (2 * α) := by field_simp; ring
  linarith

/-- **Sums of independent sub-exponential variables** (Wainwright, *High-Dimensional
Statistics*, 2019, §2.1.3, with a common `α`; Rinaldo 2017, Lemma 3.6): if the `X i` are
independent and each is sub-exponential with parameters `(ν i, α)`, then `∑ i ∈ s, X i` is
sub-exponential with parameters `(√(∑ i ∈ s, ν i²), α)`. -/
lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) {ν : ι → ℝ≥0} {s : Finset ι}
    (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (ν i) α μ) :
    HasSubexponentialMGF (∑ i ∈ s, X i) (NNReal.sqrt (∑ i ∈ s, ν i ^ 2)) α μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · exact h_indep.integrable_exp_mul_sum h_meas fun i hi ↦ (h i hi).integrable_exp_mul t ht
  · rw [h_indep.mgf_sum h_meas]
    have hsq : ((NNReal.sqrt (∑ i ∈ s, ν i ^ 2) : ℝ≥0) : ℝ) ^ 2 = ∑ i ∈ s, (ν i : ℝ) ^ 2 := by
      rw [Real.coe_sqrt, Real.sq_sqrt (NNReal.coe_nonneg _)]
      push_cast; rfl
    rw [hsq, Finset.sum_mul, Finset.sum_div, exp_sum]
    exact Finset.prod_le_prod₀ (fun i _ ↦ mgf_nonneg) fun i hi ↦ (h i hi).mgf_le t ht

end HasSubexponentialMGF

/-! ### Bernstein's inequality for bounded variables -/

/-- The exponential series bound behind Bernstein's inequality: for `|y| < 1`,
`exp y ≤ 1 + y + y² / (2 (1 - |y|))`, from `exp y = ∑ yⁿ / n!` and `n! ≥ 2` for `n ≥ 2`. -/
lemma exp_le_one_add_add_sq_div_of_abs_lt_one {y : ℝ} (hy : |y| < 1) :
    exp y ≤ 1 + y + y ^ 2 / (2 * (1 - |y|)) := by
  have hs := Real.summable_pow_div_factorial y
  have hexp : exp y = ∑' n : ℕ, y ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsplit := hs.sum_add_tsum_nat_add 2
  rw [hexp, ← hsplit]
  have hrange : ∑ i ∈ Finset.range 2, y ^ i / (i.factorial : ℝ) = 1 + y := by
    simp [Finset.sum_range_succ]
  rw [hrange]
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hgeom : Summable fun n : ℕ ↦ |y| ^ 2 / 2 * |y| ^ n :=
    (summable_geometric_of_lt_one hy0 hy).mul_left _
  have htail : Summable fun n : ℕ ↦ y ^ (n + 2) / ((n + 2).factorial : ℝ) :=
    (summable_nat_add_iff 2).mpr hs
  have hle : ∑' n : ℕ, y ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
      ∑' n : ℕ, |y| ^ 2 / 2 * |y| ^ n := by
    refine htail.tsum_le_tsum (fun n ↦ ?_) hgeom
    have hfac : (2 : ℝ) ≤ ((n + 2).factorial : ℝ) := by
      have : (2 : ℕ).factorial ≤ (n + 2).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    calc y ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ |y ^ (n + 2) / ((n + 2).factorial : ℝ)| :=
          le_abs_self _
      _ = |y| ^ (n + 2) / ((n + 2).factorial : ℝ) := by
          rw [abs_div, abs_pow, Nat.abs_cast]
      _ ≤ |y| ^ (n + 2) / 2 := by
          gcongr
      _ = |y| ^ 2 / 2 * |y| ^ n := by ring
  rw [tsum_mul_left, tsum_geometric_of_lt_one hy0 hy] at hle
  have : |y| ^ 2 / 2 * (1 - |y|)⁻¹ = y ^ 2 / (2 * (1 - |y|)) := by
    rw [sq_abs]; field_simp
  linarith

variable [IsProbabilityMeasure μ]

/-- **Bernstein's bound on the moment generating function of a bounded variable** (Wainwright,
*High-Dimensional Statistics*, 2019, §2.1.3; Rinaldo 2017, Theorem 3.4; in the case `|X| ≤ b`, for
which the Bernstein condition holds with parameter `b`): if `|X| ≤ b` almost surely, `E[X] = 0` and
`E[X²] ≤ σ²`, then for every `t` with `b |t| < 1`,
`E[exp (t X)] ≤ exp (t² σ² / (2 (1 - b |t|)))`. -/
theorem mgf_le_of_abs_le (hX : AEMeasurable X μ) {b σ t : ℝ}
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) (hmean : μ[X] = 0) (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ σ ^ 2)
    (ht : b * |t| < 1) :
    mgf X μ t ≤ exp (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|))) := by
  have hden : 0 < 1 - b * |t| := by linarith
  have hXint : Integrable X μ :=
    Integrable.of_bound hX.aestronglyMeasurable b (by simpa [Real.norm_eq_abs] using hb)
  have hX2int : Integrable (fun ω ↦ X ω ^ 2) μ :=
    Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (b ^ 2) (by
      filter_upwards [hb] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
  -- Pointwise: `exp (t X) ≤ 1 + t X + t² X² / (2 (1 - b |t|))`.
  have hpt : ∀ᵐ ω ∂μ, exp (t * X ω) ≤
      1 + t * X ω + t ^ 2 / (2 * (1 - b * |t|)) * X ω ^ 2 := by
    filter_upwards [hb] with ω hω
    have hy : |t * X ω| ≤ b * |t| := by
      rw [abs_mul, mul_comm b]; exact mul_le_mul_of_nonneg_left hω (abs_nonneg t)
    have h1 := exp_le_one_add_add_sq_div_of_abs_lt_one (hy.trans_lt ht)
    refine h1.trans ?_
    have hden' : 0 < 1 - |t * X ω| := by linarith
    have : (t * X ω) ^ 2 / (2 * (1 - |t * X ω|)) ≤ (t * X ω) ^ 2 / (2 * (1 - b * |t|)) := by
      gcongr
    calc 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - |t * X ω|))
        ≤ 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - b * |t|)) := by linarith
      _ = _ := by ring
  have hrhs : Integrable (fun ω ↦ 1 + t * X ω + t ^ 2 / (2 * (1 - b * |t|)) * X ω ^ 2) μ :=
    ((integrable_const 1).add (hXint.const_mul t)).add (hX2int.const_mul _)
  have hexpint : Integrable (fun ω ↦ exp (t * X ω)) μ :=
    Integrable.of_bound (by fun_prop) (exp (b * |t|)) (by
      filter_upwards [hb] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      refine exp_le_exp.mpr ?_
      calc t * X ω ≤ |t * X ω| := le_abs_self _
        _ = |t| * |X ω| := abs_mul _ _
        _ ≤ |t| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
        _ = b * |t| := mul_comm _ _)
  calc mgf X μ t = ∫ ω, exp (t * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + t * X ω + t ^ 2 / (2 * (1 - b * |t|)) * X ω ^ 2) ∂μ :=
        integral_mono_ae hexpint hrhs hpt
    _ = 1 + t * μ[X] + t ^ 2 / (2 * (1 - b * |t|)) * ∫ ω, X ω ^ 2 ∂μ := by
        have hA : Integrable (fun ω ↦ 1 + t * X ω) μ := (integrable_const 1).add (hXint.const_mul t)
        have hB : Integrable (fun ω ↦ t ^ 2 / (2 * (1 - b * |t|)) * X ω ^ 2) μ :=
          hX2int.const_mul _
        have hC : Integrable (fun ω ↦ t * X ω) μ := hXint.const_mul t
        rw [integral_add hA hB, integral_add (integrable_const 1) hC, integral_const_mul,
          integral_const_mul]
        simp
    _ ≤ 1 + t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|)) := by
        rw [hmean, mul_zero, add_zero]
        have : t ^ 2 / (2 * (1 - b * |t|)) * ∫ ω, X ω ^ 2 ∂μ ≤
            t ^ 2 / (2 * (1 - b * |t|)) * σ ^ 2 :=
          mul_le_mul_of_nonneg_left hvar (by positivity)
        linarith [show t ^ 2 / (2 * (1 - b * |t|)) * σ ^ 2 =
          t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|)) by ring]
    _ ≤ exp (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|))) := by
        linarith [add_one_le_exp (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|)))]

/-- **Bernstein's inequality** for a bounded variable, upper tail (Wainwright, *High-Dimensional
Statistics*, 2019, §2.1.3; Rinaldo 2017, Theorem 3.5; in the case `|X| ≤ b`): if `|X| ≤ b` almost
surely with `b ≥ 0`, `E[X] = 0` and `E[X²] ≤ σ²`, then for every `t ≥ 0`,
`P(X ≥ t) ≤ exp (-t² / (2 (σ² + b t)))`. -/
theorem measureReal_ge_le_bernstein (hX : AEMeasurable X μ) {b σ t : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) (hmean : μ[X] = 0) (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ σ ^ 2)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ exp (-t ^ 2 / (2 * (σ ^ 2 + b * t))) := by
  -- The bound for every variance proxy `v > 0` with `E[X²] ≤ v`.
  have key : ∀ v : ℝ, 0 < v → ∫ ω, X ω ^ 2 ∂μ ≤ v →
      μ.real {ω | t ≤ X ω} ≤ exp (-t ^ 2 / (2 * (v + b * t))) := by
    intro v hv hvv
    have hD : 0 < v + b * t := by positivity
    set s := t / (v + b * t) with hs_def
    have hs0 : 0 ≤ s := by positivity
    have hbs : b * |s| < 1 := by
      rw [abs_of_nonneg hs0, hs_def, mul_div_assoc', div_lt_one hD]; linarith
    have hden : 1 - b * |s| = v / (v + b * t) := by
      rw [abs_of_nonneg hs0, hs_def]; field_simp; ring
    have hXint : Integrable (fun ω ↦ exp (s * X ω)) μ :=
      Integrable.of_bound (by fun_prop) (exp (b * |s|)) (by
        filter_upwards [hb] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        refine exp_le_exp.mpr ?_
        calc s * X ω ≤ |s * X ω| := le_abs_self _
          _ = |s| * |X ω| := abs_mul _ _
          _ ≤ |s| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg s)
          _ = b * |s| := mul_comm _ _)
    have hv' : ∫ ω, X ω ^ 2 ∂μ ≤ (Real.sqrt v) ^ 2 := by rwa [Real.sq_sqrt hv.le]
    have hm := mgf_le_of_abs_le hX hb hmean hv' hbs
    rw [Real.sq_sqrt hv.le, hden] at hm
    calc μ.real {ω | t ≤ X ω} ≤ exp (-s * t) * mgf X μ s :=
          measure_ge_le_exp_mul_mgf t hs0 hXint
      _ ≤ exp (-s * t) * exp (s ^ 2 * v / (2 * (v / (v + b * t)))) := by gcongr
      _ = exp (-t ^ 2 / (2 * (v + b * t))) := by
          rw [← exp_add]; congr 1; rw [hs_def]; field_simp; ring
  rcases (sq_nonneg σ).lt_or_eq with hσ | hσ
  · exact key _ hσ hvar
  -- Degenerate case `σ = 0`: let the variance proxy `v` decrease to `0`.
  rw [← hσ, zero_add]
  rcases (mul_nonneg hb0 ht).lt_or_eq with hbt | hbt
  · have hcont : Tendsto (fun v : ℝ ↦ exp (-t ^ 2 / (2 * (v + b * t)))) (𝓝[>] 0)
        (𝓝 (exp (-t ^ 2 / (2 * (0 + b * t))))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
      exact ((continuousAt_const.div (continuousAt_const.mul
        (continuousAt_id.add continuousAt_const))
        (ne_of_gt (by simpa using mul_pos two_pos hbt))).rexp)
    rw [zero_add] at hcont
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with v (hv : 0 < v)
    exact key v hv (by rw [← hσ] at hvar; linarith)
  · rw [← hbt, mul_zero, div_zero, exp_zero]
    exact measureReal_le_one

/-- **Bernstein's inequality** for a bounded variable, two-sided (Wainwright, *High-Dimensional
Statistics*, 2019, §2.1.3; Rinaldo 2017, Theorem 3.5; in the case `|X| ≤ b`): if `|X| ≤ b` almost
surely with `b ≥ 0`, `E[X] = 0` and `E[X²] ≤ σ²`, then for every `t ≥ 0`,
`P(|X| ≥ t) ≤ 2 exp (-t² / (2 (σ² + b t)))`. -/
theorem measureReal_abs_ge_le_bernstein (hX : AEMeasurable X μ) {b σ t : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) (hmean : μ[X] = 0) (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ σ ^ 2)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-t ^ 2 / (2 * (σ ^ 2 + b * t))) := by
  have hpos := measureReal_ge_le_bernstein hX hb0 hb hmean hvar ht
  have hneg := measureReal_ge_le_bernstein (X := -X) hX.neg hb0
    (by filter_upwards [hb] with ω hω; simpa using hω)
    (by simp [Pi.neg_apply, integral_neg, hmean])
    (by simpa using hvar) ht
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; exact h
  calc μ.real {ω | t ≤ |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end

end ProbabilityTheory
