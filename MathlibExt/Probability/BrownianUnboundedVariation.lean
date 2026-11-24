/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import MathlibExt.Probability.BrownianQuadraticVariation

/-!
# Brownian paths have unbounded variation

On every interval `[0, t]` with `t > 0`, almost every Brownian path has unbounded (infinite)
variation. This is the reason why the stochastic integral `∫ H dB` cannot be defined pathwise as
a Lebesgue–Stieltjes integral, and it follows from the quadratic variation of Brownian motion:
along the uniform partitions of `[0, t]`,

`∑_k (B t_{k+1} - B t_k)² ≤ (max_k |B t_{k+1} - B t_k|) · ∑_k |B t_{k+1} - B t_k|`.

On a continuous path of bounded variation `V`, the right side is at most `V · max_k |Δ_k|`,
which tends to `0` by uniform continuity on `[0, t]`, while the left side tends to `t > 0` in
probability (`ProbabilityTheory.IsPreBrownianReal.tendstoInMeasure_sum_sq`), hence almost surely
along a subsequence.

## Main results

* `ProbabilityTheory.tendsto_sum_sq_increments_of_boundedVariationOn`: along the uniform
  partitions of `[0, t]`, the quadratic sums of a continuous function of bounded variation on
  `[0, t]` tend to `0`.
* `ProbabilityTheory.IsBrownianReal.ae_not_boundedVariationOn`: **Brownian paths have unbounded
  variation** on `[0, t]` for every `t > 0`, almost surely.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2 (quadratic variation of Brownian paths) and
  Chapter 4 (finite variation processes).
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 1.5.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- **Quadratic sums of a continuous function of bounded variation vanish.** If `f : ℝ≥0 → ℝ` is
continuous and has bounded variation on `[0, t]`, then along the uniform partitions of `[0, t]`,
`∑_{k < n} (f (t (k + 1) / n) - f (t k / n))² → 0` (Le Gall, *Brownian Motion, Martingales, and
Stochastic Calculus*, Chapter 4: a continuous finite variation function has zero quadratic
variation). -/
theorem tendsto_sum_sq_increments_of_boundedVariationOn {f : ℝ≥0 → ℝ} (hf : Continuous f)
    (t : ℝ≥0) (hbv : BoundedVariationOn f (Set.Icc 0 t)) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, (f (t * (k + 1) / n) - f (t * k / n)) ^ 2)
      atTop (𝓝 0) := by
  set V : ℝ := (eVariationOn f (Set.Icc 0 t)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  -- the partition points
  set u : ℕ → ℕ → ℝ≥0 := fun n i ↦ t * i / n with hu
  have hu_mono : ∀ n, Monotone (u n) := fun n i j hij ↦ by
    simp only [hu]
    gcongr
  -- sum of absolute increments is at most the variation
  have hsum_abs : ∀ n : ℕ, 0 < n →
      ∑ k ∈ Finset.range n, |f (t * (k + 1) / n) - f (t * k / n)| ≤ V := by
    intro n hn
    have hmem : ∀ i ∈ Set.Icc 0 n, u n i ∈ Set.Icc (0 : ℝ≥0) t := by
      intro i hi
      refine ⟨zero_le, ?_⟩
      simp only [hu]
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      gcongr
      exact_mod_cast hi.2
    have hle := eVariationOn.sum_le_of_monotoneOn_Icc (f := f) (s := Set.Icc 0 t) (m := 0)
      (n := n) (u := u n) ((hu_mono n).monotoneOn _) hmem
    rw [Nat.Ico_zero_eq_range] at hle
    have hfin : eVariationOn f (Set.Icc 0 t) ≠ ∞ := hbv
    have : ∑ k ∈ Finset.range n, ENNReal.ofReal |f (t * (k + 1) / n) - f (t * k / n)| ≤
        eVariationOn f (Set.Icc 0 t) := by
      refine le_trans (le_of_eq ?_) hle
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [edist_dist, Real.dist_eq]
      simp only [hu]
      push_cast
      rfl
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 this
  -- uniform continuity on `[0, t]`
  have huc : UniformContinuousOn f (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := huc (ε / (V + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / δ)
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hstep : (t : ℝ) / n < δ := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
    nlinarith
  have hinc : ∀ k ∈ Finset.range n,
      |f (t * (k + 1) / n) - f (t * k / n)| < ε / (V + 1) := by
    intro k hk
    have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
    have hmem1 : t * (k + 1) / n ∈ Set.Icc (0 : ℝ≥0) t := by
      refine ⟨zero_le, ?_⟩
      rw [div_le_iff₀ (by exact_mod_cast hn0)]
      gcongr
      exact_mod_cast hk'
    have hmem0 : t * k / n ∈ Set.Icc (0 : ℝ≥0) t := by
      refine ⟨zero_le, ?_⟩
      rw [div_le_iff₀ (by exact_mod_cast hn0)]
      gcongr
      exact_mod_cast (show k ≤ n by omega)
    have hd : dist (t * (k + 1) / n) (t * k / n) < δ := by
      rw [NNReal.dist_eq]
      push_cast
      rw [show (t : ℝ) * (k + 1) / n - t * k / n = t / n by field_simp; ring]
      rw [abs_of_nonneg (by positivity)]
      exact hstep
    have := hδf _ hmem1 _ hmem0 hd
    rwa [Real.dist_eq] at this
  have hsq : ∑ k ∈ Finset.range n, (f (t * (k + 1) / n) - f (t * k / n)) ^ 2 ≤
      ε / (V + 1) * V := by
    calc ∑ k ∈ Finset.range n, (f (t * (k + 1) / n) - f (t * k / n)) ^ 2
        ≤ ∑ k ∈ Finset.range n, ε / (V + 1) * |f (t * (k + 1) / n) - f (t * k / n)| := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [← sq_abs]
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hinc k hk).le (abs_nonneg _)
      _ = ε / (V + 1) * ∑ k ∈ Finset.range n, |f (t * (k + 1) / n) - f (t * k / n)| := by
          rw [Finset.mul_sum]
      _ ≤ ε / (V + 1) * V := by
          gcongr
          exact hsum_abs n hn0
  have hlt : ε / (V + 1) * V < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  exact lt_of_le_of_lt hsq hlt

/-- **Brownian paths have unbounded variation.** If `B` is a Brownian motion (`IsBrownianReal`)
and `t > 0`, then almost surely the path `s ↦ B s ω` does not have bounded variation on `[0, t]`.
The proof compares the quadratic variation `∑_k (ΔB_k)² → t` (in probability, hence almost surely
along a subsequence) with the vanishing quadratic sums of continuous functions of bounded
variation (Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Chapter 2 and
Chapter 4). -/
theorem IsBrownianReal.ae_not_boundedVariationOn {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ¬ BoundedVariationOn (fun s ↦ B s ω) (Set.Icc 0 t) := by
  obtain ⟨ns, hns, hae⟩ :=
    (hB.toIsPreBrownianReal.tendstoInMeasure_sum_sq t).exists_seq_tendsto_ae
  filter_upwards [hB.cont, hae] with ω hcont hlim hbv
  have h0 := (tendsto_sum_sq_increments_of_boundedVariationOn hcont t hbv).comp
    hns.tendsto_atTop
  have := tendsto_nhds_unique hlim h0
  exact (ne_of_gt (show (0 : ℝ) < t by exact_mod_cast ht)) this

end ProbabilityTheory
