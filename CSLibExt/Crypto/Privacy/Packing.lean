/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.Basic

/-!
# Packing lower bound for pure differential privacy

Let an `ε`-differentially private mechanism `M` send each of `N` databases into its own region of
the output space with probability at least `1 / 2`, where each database is joined to a database
`d₀` by a chain of exactly `k` neighbouring steps (for a reflexive relation, a database at distance
at most `k` from `d₀`). Group privacy moves each of these probabilities to `M d₀` at the cost of a
factor `e^{ε k}`, and the regions, being disjoint, share the mass `1` of `M d₀`. Hence
`N ≤ 2 e^{ε k}`.

* `DifferentiallyPrivate.packing`: `N ≤ 2 e^{ε k}` and, for `ε > 0`, `k ≥ log (N / 2) / ε`
  (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Lemma 8.4, there
  for `2 ^ s` histograms at pairwise `ℓ₁` distance at most `Δ`).

`CSLibExt.Privacy.DifferentialPrivacy.packing_lower_bound_pure`, in
`CSLibExt/Privacy/PackingLowerBound.lean`, is a form for mechanisms with values in probability mass
functions, with a threshold `p` in place of `1 / 2` and its logarithmic corollary stated
separately; it does not apply to measures on a general measurable space.
-/

public section

open Function MeasureTheory
open scoped ENNReal

namespace Cslib.Crypto.Privacy

variable {X Ω : Type*} [MeasurableSpace Ω] {Adj : X → X → Prop} {M : X → Measure Ω} {ε : ℝ}

/-- **Packing lower bound for pure differential privacy.** Let `M` be `ε`-differentially private
for `Adj` with `M d₀` a probability measure, and let `d i`, for `i : Fin N`, be databases each
joined to `d₀` by a chain `d i = z 0, z 1, …, z k = d₀` of exactly `k` steps, with
`Adj (z j) (z (j + 1))` for `j < k` (for a reflexive relation such as `hammingAdj` or
`histogramAdj`, these are the databases at distance at most `k` from `d₀`). If the `S i` are
pairwise disjoint measurable sets of outputs with `M (d i) (S i) ≥ 1 / 2`, then
`N ≤ 2 e^{ε k}`, and consequently `k ≥ log (N / 2) / ε` when `ε > 0`. Dwork and Roth (*The
Algorithmic Foundations of Differential Privacy*, 2014, Lemma 8.4) state the bound for `2 ^ s`
histograms at pairwise `ℓ₁` distance at most `Δ` as `ε ≥ ln 2 · (s - 1) / Δ`; the argument
through a fixed `d₀` is that of Hardt and Talwar (*On the geometry of differential privacy*,
STOC 2010; arXiv:0907.3754v3, proof of Theorem 3.3). -/
theorem DifferentiallyPrivate.packing (h : DifferentiallyPrivate Adj M ε 0) {d₀ : X}
    [IsProbabilityMeasure (M d₀)] {k N : ℕ} {d : Fin N → X}
    (hd : ∀ i, ∃ z : ℕ → X, z 0 = d i ∧ z k = d₀ ∧ ∀ j < k, Adj (z j) (z (j + 1)))
    {S : Fin N → Set Ω} (hS : ∀ i, MeasurableSet (S i)) (hdisj : Pairwise (Disjoint on S))
    (hprob : ∀ i, 2⁻¹ ≤ M (d i) (S i)) :
    (N : ℝ) ≤ 2 * Real.exp (ε * k) ∧ (0 < ε → Real.log (N / 2) / ε ≤ k) := by
  have key : (N : ℝ≥0∞) * 2⁻¹ ≤ ENNReal.ofReal (Real.exp (k * ε)) :=
    calc (N : ℝ≥0∞) * 2⁻¹ = ∑ _i : Fin N, (2⁻¹ : ℝ≥0∞) := by simp
      _ ≤ ∑ i, ENNReal.ofReal (Real.exp (k * ε)) * M d₀ (S i) := by
          gcongr with i
          obtain ⟨z, hz0, hzk, hz⟩ := hd i
          have hgroup := h.group hz (hS i)
          rw [hz0, hzk] at hgroup
          exact (hprob i).trans hgroup
      _ = ENNReal.ofReal (Real.exp (k * ε)) * M d₀ (⋃ i, S i) := by
          rw [← Finset.mul_sum, measure_iUnion hdisj hS, tsum_fintype]
      _ ≤ ENNReal.ofReal (Real.exp (k * ε)) := mul_le_of_le_one_right' prob_le_one
  have hN : (N : ℝ) / 2 ≤ Real.exp (ε * k) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, mul_comm (k : ℝ)] at this
    simpa [div_eq_mul_inv] using this
  refine ⟨by linarith, fun hε ↦ ?_⟩
  rw [div_le_iff₀ hε]
  rcases N.eq_zero_or_pos with rfl | hN0
  · simp [mul_nonneg (Nat.cast_nonneg k) hε.le]
  · calc Real.log (N / 2) ≤ Real.log (Real.exp (ε * k)) :=
          Real.log_le_log (by positivity) hN
      _ = k * ε := by rw [Real.log_exp, mul_comm]

end Cslib.Crypto.Privacy
