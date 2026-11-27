/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SplitConformalExactCoverage

/-!
# Conformalized quantile regression

Conformalized quantile regression (CQR; Y. Romano, E. Patterson and E. J. Candès,
*Conformalized quantile regression*, NeurIPS 2019, arXiv:1905.03222) turns two fitted
conditional quantile functions `q̂_lo`, `q̂_hi` into a prediction interval with a finite-sample,
distribution-free coverage guarantee. On a calibration set of `n` points it computes the
conformity scores

`E_i = max (q̂_lo(X_i) - Y_i, Y_i - q̂_hi(X_i))`,

takes `Q`, the `(1 - α)(1 + 1/n)`-th empirical quantile of the `E_i`, which is the `k`-th smallest
score with `k = ⌈(1 - α)(n + 1)⌉`, and outputs `C(x) = [q̂_lo(x) - Q, q̂_hi(x) + Q]`.

Here the `n + 1` data points (calibration points first, the test point last) form a random vector
`Z : Fin (n + 1) → 𝒳 × ℝ` whose law `μ` is invariant under coordinate permutations, i.e.
exchangeable. The fitted functions `q̂_lo`, `q̂_hi` are fixed measurable maps: this is the
statement conditional on the proper training set, as in the proof of Theorem 1 of Romano et al.
When `k = n + 1` (that is, `α < 1 / (n + 1)`) the quantile level exceeds `1` and the band is all
of `ℝ`; this convention (`Q = +∞`) is the one of `splitConformalThreshold`.

## Main definitions

* `cqrScore q_lo q_hi (x, y)`: the CQR conformity score `max (q_lo x - y) (y - q_hi x)`.
* `cqrThreshold q_lo q_hi k Z`: the `k`-th smallest calibration score, or `⊤` if `k > n`.
* `cqrBand q_lo q_hi Q x`: the band `[q_lo x - Q, q_hi x + Q]`, all of `ℝ` when `Q = ⊤`.

## Main results

* `cqrBand_coe`: for finite `Q`, the band is the interval `Set.Icc (q_lo x - Q) (q_hi x + Q)`.
* `mem_cqrBand_iff`: `y ∈ C(x)` iff the score of `(x, y)` is at most `Q`.
* `ofReal_one_sub_le_measure_mem_cqrBand`: coverage at least `1 - α` (Theorem 1, lower bound).
* `measure_mem_cqrBand_le`: if the scores are almost surely distinct, coverage at most
  `1 - α + 1 / (n + 1)` (Theorem 1, upper bound, with `|I₂| = n`).
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.Statistics.SplitConformal
open MathlibExt.Probability.Statistics.SplitConformalExactCoverage

namespace MathlibExt.Probability.Statistics.ConformalizedQuantileRegression

variable {𝒳 : Type*} {n : ℕ}

/-- **CQR conformity score.** For fitted lower and upper conditional quantile functions `q_lo`,
`q_hi`, the score of a data point `(x, y)` is `max (q_lo x - y) (y - q_hi x)`: negative when `y`
lies strictly inside `[q_lo x, q_hi x]`, and the signed distance to the nearer endpoint otherwise.

Source: Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*,
NeurIPS 2019, arXiv:1905.03222, Algorithm 1 (the scores `E_i`). -/
def cqrScore (q_lo q_hi : 𝒳 → ℝ) (z : 𝒳 × ℝ) : ℝ :=
  max (q_lo z.1 - z.2) (z.2 - q_hi z.1)

/-- **CQR threshold.** The `k`-th smallest CQR score of the calibration points `Z i.castSucc`
(counted with multiplicity), and `⊤` when `k > n`. With `k = ⌈(1 - α)(n + 1)⌉` this is the
`(1 - α)(1 + 1/n)`-th empirical quantile `Q_{1-α}(E, I₂)` of Romano, Patterson and Candès
(NeurIPS 2019, arXiv:1905.03222, Algorithm 1), with `Q = +∞` when that level exceeds `1`. -/
noncomputable def cqrThreshold (q_lo q_hi : 𝒳 → ℝ) (k : ℕ) (Z : Fin (n + 1) → 𝒳 × ℝ) :
    WithTop ℝ :=
  splitConformalThreshold k fun i => cqrScore q_lo q_hi (Z i)

/-- **CQR prediction band.** For a threshold `Q ∈ ℝ ∪ {+∞}`, the band at `x` is
`[q_lo x - Q, q_hi x + Q]`, written as the set of `y` with `q_lo x - y ≤ Q` and `y - q_hi x ≤ Q`;
it is all of `ℝ` when `Q = ⊤`.

Source: Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*,
NeurIPS 2019, arXiv:1905.03222, Algorithm 1 (output). -/
def cqrBand (q_lo q_hi : 𝒳 → ℝ) (Q : WithTop ℝ) (x : 𝒳) : Set ℝ :=
  {y | ((q_lo x - y : ℝ) : WithTop ℝ) ≤ Q ∧ ((y - q_hi x : ℝ) : WithTop ℝ) ≤ Q}

/-- **The CQR band for a finite threshold is an interval.** For `Q ∈ ℝ`,
`cqrBand q_lo q_hi Q x = [q_lo x - Q, q_hi x + Q]`. -/
theorem cqrBand_coe (q_lo q_hi : 𝒳 → ℝ) (Q : ℝ) (x : 𝒳) :
    cqrBand q_lo q_hi (Q : WithTop ℝ) x = Set.Icc (q_lo x - Q) (q_hi x + Q) := by
  ext y
  simp only [cqrBand, Set.mem_ofPred_eq, WithTop.coe_le_coe, Set.mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Membership in the CQR band through the score.** `y` lies in the band at `x` with threshold
`Q` iff the CQR score of `(x, y)` is at most `Q`. -/
theorem mem_cqrBand_iff (q_lo q_hi : 𝒳 → ℝ) (Q : WithTop ℝ) (x : 𝒳) (y : ℝ) :
    y ∈ cqrBand q_lo q_hi Q x ↔ (cqrScore q_lo q_hi (x, y) : WithTop ℝ) ≤ Q := by
  induction Q with
  | top => simp [cqrBand]
  | coe Q =>
    simp only [cqrBand, cqrScore, Set.mem_ofPred_eq, WithTop.coe_le_coe, max_le_iff]

variable [MeasurableSpace 𝒳]

private theorem measurable_scoreVector {q_lo q_hi : 𝒳 → ℝ} (hlo : Measurable q_lo)
    (hhi : Measurable q_hi) :
    Measurable fun Z : Fin (n + 1) → 𝒳 × ℝ => fun i => cqrScore q_lo q_hi (Z i) := by
  refine Measurable.of_eval fun i => ?_
  have h1 : Measurable fun Z : Fin (n + 1) → 𝒳 × ℝ => (Z i).1 :=
    measurable_fst.comp (measurable_pi_apply i)
  have h2 : Measurable fun Z : Fin (n + 1) → 𝒳 × ℝ => (Z i).2 :=
    measurable_snd.comp (measurable_pi_apply i)
  exact ((hlo.comp h1).sub h2).max (h2.sub (hhi.comp h1))

/-- The law of the score vector, and the coverage event as a preimage. -/
private theorem measure_mem_cqrBand_eq_map (μ : Measure (Fin (n + 1) → 𝒳 × ℝ))
    {q_lo q_hi : 𝒳 → ℝ} (hlo : Measurable q_lo) (hhi : Measurable q_hi) {k : ℕ} (hk : 1 ≤ k) :
    μ {Z | (Z (Fin.last n)).2 ∈ cqrBand q_lo q_hi (cqrThreshold q_lo q_hi k Z) (Z (Fin.last n)).1}
      = (μ.map fun Z : Fin (n + 1) → 𝒳 × ℝ => fun i => cqrScore q_lo q_hi (Z i))
          {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω} := by
  have hC : MeasurableSet
      {ω : Fin (n + 1) → ℝ | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω} := by
    have : {ω : Fin (n + 1) → ℝ | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω}
        = strictLowerCount ⁻¹' Set.Iio k := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
      exact coe_le_splitConformalThreshold_iff hk ω
    rw [this]
    exact measurable_strictLowerCount MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_scoreVector hlo hhi) hC]
  congr 1
  ext Z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, cqrThreshold]
  rw [mem_cqrBand_iff]

private theorem map_scoreVector_perm (μ : Measure (Fin (n + 1) → 𝒳 × ℝ))
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun Z => Z ∘ σ) = μ)
    {q_lo q_hi : 𝒳 → ℝ} (hlo : Measurable q_lo) (hhi : Measurable q_hi)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (μ.map fun Z : Fin (n + 1) → 𝒳 × ℝ => fun i => cqrScore q_lo q_hi (Z i)).map
        (fun ω => ω ∘ σ) =
      μ.map fun Z : Fin (n + 1) → 𝒳 × ℝ => fun i => cqrScore q_lo q_hi (Z i) := by
  have hσℝ : Measurable fun ω : Fin (n + 1) → ℝ => ω ∘ σ :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  have hσZ : Measurable fun Z : Fin (n + 1) → 𝒳 × ℝ => Z ∘ σ :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  rw [Measure.map_map hσℝ (measurable_scoreVector hlo hhi)]
  conv_rhs => rw [← hμ σ]
  rw [Measure.map_map (measurable_scoreVector hlo hhi) hσZ]
  rfl

/-- **CQR coverage (lower bound).** Let the law `μ` of the data `Z : Fin (n + 1) → 𝒳 × ℝ`
(`n` calibration points, then the test point) be a probability measure invariant under every
coordinate permutation, and let `q_lo`, `q_hi` be measurable. For `0 ≤ α < 1`, with
`k = ⌈(1 - α)(n + 1)⌉`, the test response lies in the CQR band at the test covariate with
probability at least `1 - α`.

Source: Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*,
NeurIPS 2019, arXiv:1905.03222, Theorem 1 (first inequality), stated conditionally on the proper
training set (fixed `q_lo`, `q_hi`), as in its proof. The source takes `α ∈ (0, 1)`; the Lean
statement also admits the trivial endpoint `α = 0`. -/
theorem ofReal_one_sub_le_measure_mem_cqrBand (μ : Measure (Fin (n + 1) → 𝒳 × ℝ))
    [IsProbabilityMeasure μ] (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun Z => Z ∘ σ) = μ)
    {q_lo q_hi : 𝒳 → ℝ} (hlo : Measurable q_lo) (hhi : Measurable q_hi) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      μ {Z | (Z (Fin.last n)).2 ∈
        cqrBand q_lo q_hi (cqrThreshold q_lo q_hi ⌈(1 - α) * (n + 1)⌉₊ Z) (Z (Fin.last n)).1} := by
  have hk : 1 ≤ ⌈(1 - α) * (n + 1)⌉₊ :=
    Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα1) (by positivity))
  rw [measure_mem_cqrBand_eq_map μ hlo hhi hk]
  exact ofReal_one_sub_le_measure_coe_le_splitConformalThreshold _
    (map_scoreVector_perm μ hμ hlo hhi) hα0 hα1

/-- **CQR coverage (upper bound without ties).** Under the hypotheses of
`ofReal_one_sub_le_measure_mem_cqrBand`, if moreover the `n + 1` CQR scores are almost surely
distinct, the test response lies in the CQR band with probability at most `1 - α + 1 / (n + 1)`.

Source: Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*,
NeurIPS 2019, arXiv:1905.03222, Theorem 1 (second inequality, `|I₂| = n` calibration points),
conditionally on the proper training set. The source takes `α ∈ (0, 1)`; the Lean statement also
admits the trivial endpoint `α = 0`. -/
theorem measure_mem_cqrBand_le (μ : Measure (Fin (n + 1) → 𝒳 × ℝ))
    [IsProbabilityMeasure μ] (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun Z => Z ∘ σ) = μ)
    {q_lo q_hi : 𝒳 → ℝ} (hlo : Measurable q_lo) (hhi : Measurable q_hi)
    (hdistinct : ∀ᵐ Z ∂μ, Function.Injective fun i => cqrScore q_lo q_hi (Z i)) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    μ {Z | (Z (Fin.last n)).2 ∈
        cqrBand q_lo q_hi (cqrThreshold q_lo q_hi ⌈(1 - α) * (n + 1)⌉₊ Z) (Z (Fin.last n)).1} ≤
      ENNReal.ofReal (1 - α + 1 / (n + 1)) := by
  have hk : 1 ≤ ⌈(1 - α) * (n + 1)⌉₊ :=
    Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα1) (by positivity))
  rw [measure_mem_cqrBand_eq_map μ hlo hhi hk]
  refine measure_coe_le_splitConformalThreshold_le _ (map_scoreVector_perm μ hμ hlo hhi) ?_ hα0
    hα1
  exact (ae_map_iff (measurable_scoreVector hlo hhi).aemeasurable
    measurableSet_setOf_injective).2 hdistinct

end MathlibExt.Probability.Statistics.ConformalizedQuantileRegression
