/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The alternating harmonic series

The alternating harmonic series `∑ (-1) ^ n / (n + 1)` is the canonical
example of a conditionally convergent series: its partial sums converge,
but the series of absolute values (the harmonic series) diverges.

## Main results

* `Real.tendsto_sum_alternating_harmonic`: the partial sums converge to
  `Real.log 2`.
* `Real.not_summable_abs_alternating_harmonic`: the series is not
  absolutely summable, in Mathlib's unconditional `Summable` sense.

The sum is evaluated with Abel's limit theorem
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`), following the pattern of
Mathlib's proof of Leibniz's series for `π / 4`
(`Real.tendsto_sum_pi_div_four`): the power series `∑ (-1) ^ n x ^ n / (n + 1)`
is `Real.log (1 + x) / x` for `|x| < 1`, and Abel's theorem identifies its
limit as `x → 1⁻` with the sum of the coefficient series.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem (Alternating Series
test), "Series section": "`∑ (-1) ^ n / n` does not absolutely converge.
However, `∑ (-1) ^ n / n` converges." The v1 formalization
`Real_Analysis.Series.alternating_harmonic_converges` in
`v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean` proves only that the
partial sums converge to *some* limit, via the alternating series test. Here
the limit is identified as `Real.log 2`, and non-absolute-summability is
stated in Mathlib's `Summable` form. The `n + 1` shift follows the v1
formalization (the book's series starts at `n = 1`); it avoids dividing by
zero at `n = 0` in Lean's `ℕ`-indexed sum.
-/

@[expose] public section

open scoped Topology

namespace Real

/-- **The alternating harmonic series sums to `log 2`.** The partial sums
`∑ i ∈ range k, (-1) ^ i / (i + 1)` converge to `Real.log 2`. -/
theorem tendsto_sum_alternating_harmonic :
    Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i / (↑i + 1)) Filter.atTop
      (𝓝 (Real.log 2)) := by
  -- Convergence to some limit `l`, via the alternating series test.
  obtain ⟨l, h⟩ : ∃ l, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1))
      Filter.atTop (𝓝 l) := by
    obtain ⟨l, htest⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
      (f := fun n : ℕ => (1 : ℝ) / (↑n + 1))
      (by
        intro a b hab
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        exact_mod_cast Nat.add_le_add_right hab 1)
      (by
        have h1 : Filter.Tendsto (fun n : ℕ => ((↑n + 1 : ℝ))⁻¹) Filter.atTop (𝓝 0) := by
          apply tendsto_inv_atTop_zero.comp
          exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        simpa only [div_eq_mul_inv, one_mul] using h1)
    refine ⟨l, ?_⟩
    have heq : (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) =
        (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (1 / (↑i + 1))) := by
      ext n
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_one_div]
    rw [heq]
    exact htest
  -- Abel's limit theorem: the power series tends to `l` as `x → 1⁻`.
  have abel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt h
  -- The power series is `log (1 + x) / x`, which tends to `log 2` as `x → 1⁻`.
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] 1)
      (𝓝 (Real.log 2)) := by
    have h1 : Filter.Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝[<] 1)
        (𝓝 (Real.log 2)) := by
      have hc : ContinuousAt Real.log 2 := Real.continuousAt_log (by norm_num)
      have hx : Filter.Tendsto (fun x : ℝ => 1 + x) (𝓝[<] 1) (𝓝 2) := by
        have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] 1) (𝓝 1) :=
          tendsto_const_nhds
        have hid : Filter.Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
          Filter.tendsto_id.mono_left nhdsWithin_le_nhds
        have h := hconst.add hid
        rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
        exact h
      exact hc.tendsto.comp hx
    have hx : Filter.Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    have hdiv := h1.div hx (by norm_num)
    rw [div_one] at hdiv
    exact hdiv
  have hident : Filter.Tendsto
      (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n / (↑n + 1)) * x ^ n) (𝓝[<] 1)
      (𝓝 (Real.log 2)) := by
    apply hlog.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨1 / 2, by norm_num, fun y hy1 hy2 => ?_⟩
    rw [Real.dist_eq] at hy1
    rw [Set.mem_Iio] at hy2
    have hy_lo : (1 : ℝ) / 2 < y := by
      have := abs_sub_lt_iff.mp hy1
      linarith
    have hy_hi : y < 1 := hy2
    have hy_pos : (0 : ℝ) < y := by linarith
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hy_abs : |y| < 1 := by
      rw [abs_of_pos hy_pos]; exact hy_hi
    -- The log power series at `-y`, with its terms rewritten.
    have hseries := Real.hasSum_pow_div_log_of_abs_lt_one (x := -y) (by rwa [abs_neg])
    rw [show (1 : ℝ) - -y = 1 + y by ring] at hseries
    have hterm : (fun n : ℕ => (-y) ^ (n + 1) / (↑n + 1)) =
        (fun n : ℕ => -(((-1 : ℝ) ^ n / (↑n + 1)) * y ^ n * y)) := by
      ext n
      rw [neg_pow]
      ring
    rw [hterm] at hseries
    have hsum : HasSum (fun n : ℕ => ((-1 : ℝ) ^ n / (↑n + 1)) * y ^ n * y)
        (Real.log (1 + y)) := by
      have := hseries.neg
      simpa using this
    have htsum : (∑' n : ℕ, ((-1 : ℝ) ^ n / (↑n + 1)) * y ^ n) * y = Real.log (1 + y) := by
      rw [← tsum_mul_right]
      exact hsum.tsum_eq
    exact (eq_div_of_mul_eq hy_ne htsum).symm
  -- Uniqueness of limits identifies `l` with `Real.log 2`.
  have hl : l = Real.log 2 := tendsto_nhds_unique abel hident
  rw [hl] at h
  exact h

/-- **The alternating harmonic series is not absolutely summable.** The
series of absolute values is (up to the `n + 1` shift) the harmonic series,
which diverges. In particular the convergence of
`Real.tendsto_sum_alternating_harmonic` is only conditional. -/
theorem not_summable_abs_alternating_harmonic :
    ¬ Summable (fun n : ℕ => |(-1 : ℝ) ^ n / (↑n + 1)|) := by
  have habs : ∀ n : ℕ, |(-1 : ℝ) ^ n / (↑n + 1)| = (1 : ℝ) / (↑n + 1) := by
    intro n
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ↑n + 1)]
  simp only [habs]
  intro hsum
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / ↑n) := by
    apply (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ↑n) 1).mp
    have heq : (fun n : ℕ => (1 : ℝ) / (↑(n + 1))) = (fun n : ℕ => (1 : ℝ) / (↑n + 1)) := by
      ext n
      push_cast
      ring_nf
    rw [heq]
    exact hsum
  have h1' : Summable (fun n : ℕ => (1 : ℝ) / ↑n ^ (1 : ℝ)) := by
    simpa only [Real.rpow_one] using h1
  have h2 := (Real.summable_one_div_nat_rpow (p := 1)).mp h1'
  exact lt_irrefl (1 : ℝ) h2

end Real
