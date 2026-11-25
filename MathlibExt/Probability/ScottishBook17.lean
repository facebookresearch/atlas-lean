/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Scottish Book Problem 17: the converse of Poisson's urn theorem

For this converse, convergence in measure of the centered averages suffices. Given a subsequence
of deterministic means outside a neighborhood of the proposed limit, pass to an almost surely
convergent further subsequence of the centered averages. This preserves the pointwise implication
in the statement, without assuming almost-sure convergence of the whole sample sequence.
-/

@[expose] public section

namespace MathlibExt.Probability.ScottishBook17Wanted

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem integral_bernoulli {X : Ω → ℝ} (hX : Measurable X)
    (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) {p : ℝ} (hp : 0 ≤ p)
    (hprob : μ {ω | X ω = 1} = ENNReal.ofReal p) : ∫ ω, X ω ∂μ = p := by
  have hm : MeasurableSet {ω | X ω = 1} := hX (measurableSet_singleton 1)
  calc
    ∫ ω, X ω ∂μ = ∫ ω, ({ω | X ω = 1} : Set Ω).indicator (1 : Ω → ℝ) ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [h01] with ω hω
      rcases hω with hω | hω <;> simp [hω]
    _ = p := by rw [integral_indicator_one hm, measureReal_def, hprob, ENNReal.toReal_ofReal hp]

private theorem ae_imp_of_centered_tendsto {A : ℕ → Ω → ℝ} {P : ℕ → ℝ} {L : ℝ}
    (h : TendstoInMeasure μ (fun n ω => A n ω - P n) atTop (fun _ => (0 : ℝ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 L) → Tendsto P atTop (𝓝 L) := by
  by_cases hP : Tendsto P atTop (𝓝 L)
  · exact Eventually.of_forall fun _ _ => hP
  obtain ⟨U, hU, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.mp hP
  obtain ⟨i, hi, hiU⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨j, hj, hjA⟩ := (h.comp hi.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hjA] with ω hω hA
  have hsub := (hA.comp (hi.tendsto_atTop.comp hj.tendsto_atTop)).sub hω
  have ht : Tendsto (fun n => P (i (j n))) atTop (𝓝 L) := by
    convert hsub using 1
    · funext n
      change P (i (j n)) = A (i (j n)) ω - (A (i (j n)) ω - P (i (j n)))
      ring
    · rw [sub_zero]
  obtain ⟨n, hn⟩ := (ht.eventually_mem hU).exists
  exact (hiU (j n) hn).elim

variable [IsProbabilityMeasure μ]

private theorem centered_tendsto (P : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hP : ∀ n, 0 ≤ P n)
    (h01 : ∀ n, ∀ᵐ ω ∂μ, X n ω = 0 ∨ X n ω = 1)
    (hprob : ∀ n, μ {ω | X n ω = 1} = ENNReal.ofReal (P n))
    (hind : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ) :
    TendstoInMeasure μ (fun n ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ) -
      (∑ i ∈ Finset.range n, P i) / (n : ℝ)) atTop (fun _ => (0 : ℝ)) := by
  let S (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, X i ω
  let A (n : ℕ) (ω : Ω) : ℝ := (n : ℝ)⁻¹ * S n ω
  have hb (i : ℕ) : ∀ᵐ ω ∂μ, X i ω ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [h01 i] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hLp (i : ℕ) : MemLp (X i) 2 μ :=
    memLp_of_bounded (hb i) (hX i).aestronglyMeasurable 2
  have hInt (i : ℕ) : Integrable (X i) μ :=
    (memLp_of_bounded (hb i) (hX i).aestronglyMeasurable 1).integrable le_rfl
  have hA (n : ℕ) : MemLp (A n) 2 μ :=
    (memLp_finsetSum (Finset.range n) (fun i _ => hLp i)).const_mul _
  have hmean (n : ℕ) : (∫ ω, A n ω ∂μ) = (∑ i ∈ Finset.range n, P i) / (n : ℝ) := by
    change (∫ ω, (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) ∂μ) = _
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hInt i), div_eq_mul_inv, mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_bernoulli (hX i) (h01 i) (hP i) (hprob i)
  have hvarS (n : ℕ) : variance (S n) μ ≤ (n : ℝ) := by
    have hs : S n = ∑ i ∈ Finset.range n, X i := by
      funext ω
      simp [S, Finset.sum_apply]
    rw [hs, IndepFun.variance_sum (fun i _ => hLp i) (fun i _ j _ hij => hind i j hij)]
    calc
      _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (variance_le_sq_of_bounded (hb i) (hX i).aemeasurable).trans (by norm_num)
      _ = n := by simp
  have hvarA (n : ℕ) : variance (A n) μ ≤ (n : ℝ)⁻¹ := by
    change variance (fun ω => (n : ℝ)⁻¹ * S n ω) μ ≤ _
    rw [variance_const_mul]
    calc
      _ ≤ ((n : ℝ)⁻¹) ^ 2 * n := mul_le_mul_of_nonneg_left (hvarS n) (sq_nonneg _)
      _ = (n : ℝ)⁻¹ := by
        by_cases hn : n = 0
        · simp [hn]
        · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          field_simp
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ)⁻¹ / ε ^ 2)) atTop (𝓝 0) := by
    change Tendsto (ENNReal.ofReal ∘ fun n : ℕ => (n : ℝ)⁻¹ / ε ^ 2) atTop (𝓝 0)
    simpa only [zero_div, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 / ε ^ 2)).comp (hinv.div_const (ε ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) ?_
  intro n
  simpa only [sub_zero, Real.norm_eq_abs, hmean n, A, S, div_eq_mul_inv, mul_comm] using
    (meas_ge_le_variance_div_sq (hA n) hε).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hvarA n) (sq_nonneg ε)))

end

/--
**Converse of Poisson's theorem for urns.** Let $(\Omega, \mu)$ be a probability space, let
$(p_n)_{n \ge 0}$ be real numbers in $[0, 1]$, and let $(X_n)_{n \ge 0}$ be pairwise independent
measurable real random variables on $\Omega$ such that each $X_n$ almost surely takes only the
values $0$ and $1$, and $\mu(X_n = 1) = p_n$. Then for every real number $L$ and almost every
$\omega \in \Omega$: if $\frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega) \to L$ as $n \to \infty$, then
$\frac{1}{n} \sum_{i=0}^{n-1} p_i \to L$ as $n \to \infty$.

Here $X_n$ records one draw from the $n$-th of a sequence of urns of unknown composition, a white
ball as $1$ and a black ball as $0$, and $p_n$ is the probability of drawing a white ball from the
$n$-th urn. Only pairwise independence is assumed: for uncorrelated variables with uniformly
bounded variances the strong law of large numbers still holds.

Source: S. Ulam, Problem 17 of the Scottish Book. Rajchman's strong law for pairwise
uncorrelated variables with uniformly bounded variances gives almost-sure convergence of the
centered averages. The proof here uses only convergence in measure, by variance additivity and
Chebyshev's inequality, and an almost-sure subsequence to rule out nonconvergent deterministic
averages whenever a sample average converges to the proposed limit.
-/
theorem urnConversePoisson :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (prob : ℕ → ℝ) (X : ℕ → Ω → ℝ) (L : ℝ),
      (∀ n, 0 ≤ prob n ∧ prob n ≤ 1) →
      (∀ n, Measurable (X n)) →
      (∀ n, ∀ᵐ ω ∂μ, X n ω = 0 ∨ X n ω = 1) →
      (∀ n, μ {ω | X n ω = 1} = ENNReal.ofReal (prob n)) →
      (∀ i j, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ) →
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
          Filter.atTop (nhds L) →
        Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, prob i) / (n : ℝ))
          Filter.atTop (nhds L) := by
  intro Ω _ μ _ prob X L hP hX h01 hprob hind
  exact ae_imp_of_centered_tendsto (centered_tendsto prob X hX (fun i => (hP i).1) h01 hprob hind)

end MathlibExt.Probability.ScottishBook17Wanted
