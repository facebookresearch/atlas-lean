/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl
public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Genomic control with an estimated inflation factor `λ̂`

T38 (`RareVariantInference.GenomicControl`) shows that dividing a 1-df statistic `S_j = Z_j²`
by the **true** common inflation factor `λ` is exactly `χ²₁`-calibrated when every null score is
`𝒩(0, λ)`. In practice (Devlin and Roeder 1999) `λ` is unknown and is estimated from the
statistics of all `m` genes in the same scan. This file studies the **mean estimate**
`λ̂ = (1 / m) ∑ₖ Sₖ` (`lambdaHat`) and the corrected statistics `T_j = S_j / λ̂` (`gcStat`,
`gcStatRV`). Because gene `j` is one of the genes that define `λ̂`, the `T_j` are coupled to each
other and to `λ̂`.

## Coupling (deterministic, any scores)

* `gcStat_eq`: `T_j = m S_j / ∑ₖ Sₖ`.
* `gcStat_le_card`: `T_j ≤ m`; `sum_gcStat`: `∑ⱼ T_j = m` when some score is nonzero;
  `gcStat_two_add`: `T₀ + T₁ = 2` for two genes.
* `gcStat_update_lt`: raising another gene's statistic strictly lowers `T_j`, so non-null
  signal at gene `k` inflates `λ̂` and makes every other test more conservative.

## Calibration of `S / λ̂` is an assumption, not a consequence of true-`λ` calibration

* `not_forall_measure_lt_gcStatRV_eq`, `calibrated_true_and_not_calibrated_estimated`: for
  every law of the scores, `P(T_j > c) = 0 < P(χ²₁ > c)` at every `c ≥ m`, so `T_j` is never
  exactly `χ²₁`, while in T38's `CommonInflationModel` dividing by `λ` is exact at every `c`.
* `isTailCalibratedFamily_gcStatRV_iff`: the assumption that must be made is
  `P(T_i ≥ s) ≤ P(χ²₁ > s)` for the null genes, i.e. that the `λ̂` family is a
  `RareVariantInference.MultipleTesting.IsTailCalibratedFamily` with reference tail `χ²₁`
  (`chiSqOneTailReal`). Under it, `measure_exists_le_gcStatRV_le` gives Bonferroni control
  `P(∃ i ∈ H0, T_i ≥ s) ≤ |H0| P(χ²₁ > s)` with no assumption on the dependence.
* `not_isTailCalibratedFamily_gcStatRV_two`: the assumption can fail in T38's model. With two
  genes whose null scores are independent `𝒩(0, λ)`, `P(T₀ ≥ 1) ≥ 1/2`
  (`half_le_measure_one_le_gcStatRV_two`, by exchangeability) while
  `P(χ²₁ > 1) < 1/2` (`chiSqOneTail_one_lt_half`), so the `λ̂` test is anti-conservative at
  threshold `1` (`chiSqOneTail_lt_measure_one_le_gcStatRV_two`).

## When calibration holds or fails, for a general random `λ̂`

For any random estimate `L` (mean, median, leave-one-out, ...) and one null score with law
`𝒩(0, λ)`, with no assumption on the joint law of the score and `L`:

* `measure_lt_div_le_chiSqOneTail_add`, `chiSqOneTail_le_measure_lt_div_add`: if
  `κ₁ λ ≤ L ≤ κ₂ λ` on an event `E`, then
  `P(χ²₁ > c κ₂) - P(Eᶜ) ≤ P(Z² / L > c) ≤ P(χ²₁ > c κ₁) + P(Eᶜ)`. Calibration holds
  approximately when `L` concentrates around `λ` (`κ₁, κ₂ → 1`, `P(Eᶜ) → 0`).
* `chiSqOneTail_lt_measure_lt_div_of_le_mul`: an estimate that is always below `κ λ`, `κ < 1`,
  is strictly anti-conservative at every `c > 0`; `measure_lt_div_lt_chiSqOneTail_of_mul_le`:
  one always above `κ λ`, `κ > 1`, is strictly conservative.

## Dependence: the PRDS argument does not go through

* `sum_sum_covariance_gcStatRV`, `exists_covariance_gcStatRV_neg`: since `∑ⱼ T_j = m`, the
  covariances sum to `0`, so some pair of genes has strictly negative covariance as soon as one
  `T_j` is nondegenerate. `covariance_gcStatRV_eq_of_forall_eq`: with equal variances `v` and
  equal pairwise covariances `γ`, `γ = -v / (m - 1)`.
* `not_isPRDSOn_of_separated`: a general criterion refuting `IsPRDSOn` from a separation of
  the p-values of two genes, via `IsPRDSOn.measure_inter_mul_le`.
* `not_isPRDSOn_tailPValue_gcStatRV_two`: for two genes the `χ²₁` p-values of the `T_j` are
  never PRDS when `{T₀ ≥ 1}` and `{T₀ < 1}` both have positive probability;
  `not_isPRDSOn_tailPValue_gcStatRV_two_of_indep` discharges this in T38's model with
  independent scores, and `covariance_gcStatRV_two_neg` gives `Cov(T₀, T₁) < 0` there.

So the Benjamini–Yekutieli PRDS route used by `RareVariantInference.MultipleTesting` for BH
does not apply to the estimated-`λ̂` statistics as such.

## Gap (not proved here)

* **BH under the `λ̂` coupling for `m ≥ 3`.** Whether the `T_j` p-values are PRDS for `m ≥ 3`
  independent null scores is not settled here. The negative-covariance theorem rules out
  pairwise nonnegative covariance, but that implication from PRDS is not formalized, and FDR
  control of BH under this specific negative coupling (which shrinks like `1 / m`) is not
  proved. Without PRDS, only dependence-free procedures (Bonferroni above; the
  Benjamini–Yekutieli `∑ 1/i` correction) are justified by the assumption.
* **Anti-conservativeness for general `m`.** The failure of the calibration assumption is proved
  for `m = 2` only. For independent `𝒩(0, λ)` scores, `T_j / m` has a
  `Beta(1/2, (m - 1)/2)` law and `T_j` converges in law to `χ²₁` as `m → ∞`; neither the
  Beta law nor this limit is formalized.
* **Concentration of `λ̂`.** The sandwich bounds take `P(Eᶜ)` as given; a law of large numbers
  or variance bound for `λ̂` with independent or weakly dependent scores is not proved, and the
  median-based estimator `median(S) / 0.456` is not treated.

## Reuse and sources (API-00 receipt)

Reused, not redefined: `GenomicControl.chiSqOneTail`, `chiSqOneTail_eq_gaussianReal`,
`chiSqOneTail_lt_of_lt`, `measure_reject_eq_chiSqOneTail`, `CommonInflationModel` (T38);
`RareVariantInference.MultipleTesting.IsTailCalibratedFamily`, `tailPValue` (T39);
`MultipleTesting.IsPRDSOn`, `IsPRDSOn.measure_inter_mul_le`; from Mathlib, `gaussianReal`,
`gaussianReal_apply`, `gaussianReal_absolutelyContinuous`, `HasLaw`,
`indepFun_iff_map_prod_eq_prod_map_map`, `Measure.prod_swap`, `variance_fun_sum`,
`covariance_self`, `ae_eq_integral_of_variance_eq_zero`, `Real.pi_lt_d2`. A search of
`MathlibExt` for an estimated genomic-control factor or for coupled statistics with a shared
estimated scale found no existing development.

## References

* B. Devlin and K. Roeder, *Genomic control for association studies*, Biometrics 55 (1999),
  997–1004.
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
  MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl
  MathlibExt.Probability.Statistics.MultipleTesting
open scoped NNReal ENNReal

namespace MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControlEstimated

open MathlibExt.Biology.StatisticalGenetics.RareVariantInference

variable {m : ℕ}

/-! ### The estimator and the corrected statistics -/

/-- The mean-based genomic-control estimate `λ̂ = (1 / m) ∑ₖ zₖ²` computed from the scores
`z : Fin m → ℝ` of all `m` genes (the 1-df statistics are `zₖ²`). -/
noncomputable def lambdaHat (z : Fin m → ℝ) : ℝ :=
  (∑ k, z k ^ 2) / m

/-- The genomic-control statistic of gene `j` with the estimated factor: `S_j / λ̂ = z_j² / λ̂`.
When all scores vanish, `λ̂ = 0` and Lean's convention `x / 0 = 0` makes the statistic `0`. -/
noncomputable def gcStat (z : Fin m → ℝ) (j : Fin m) : ℝ :=
  z j ^ 2 / lambdaHat z

/-- The estimate `λ̂` is nonnegative. -/
theorem lambdaHat_nonneg (z : Fin m → ℝ) : 0 ≤ lambdaHat z := by
  unfold lambdaHat
  positivity

/-- The corrected statistic is nonnegative. -/
theorem gcStat_nonneg (z : Fin m → ℝ) (j : Fin m) : 0 ≤ gcStat z j := by
  unfold gcStat
  have := lambdaHat_nonneg z
  positivity

/-- `S_j / λ̂ = m z_j² / ∑ₖ zₖ²`: gene `j` enters its own denominator. -/
theorem gcStat_eq (z : Fin m → ℝ) (j : Fin m) :
    gcStat z j = m * z j ^ 2 / ∑ k, z k ^ 2 := by
  rw [gcStat, lambdaHat, div_div_eq_mul_div, mul_comm]

/-! ### Deterministic coupling -/

/-- **Self-coupling bound.** Because `z_j²` is one of the summands of `m λ̂`, the corrected
statistic never exceeds the number of genes: `S_j / λ̂ ≤ m`, for every score vector. -/
theorem gcStat_le_card (z : Fin m → ℝ) (j : Fin m) : gcStat z j ≤ m := by
  rw [gcStat_eq]
  rcases (Finset.sum_nonneg fun k _ => sq_nonneg (z k) :
      0 ≤ ∑ k, z k ^ 2).eq_or_lt with h | h
  · rw [← h, div_zero]
    positivity
  · rw [div_le_iff₀ h]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j)) (Nat.cast_nonneg m)

/-- **Constant sum.** Whenever some score is nonzero, the corrected statistics of all genes sum
to exactly `m`: `∑ⱼ S_j / λ̂ = m`. The family lives on a simplex, so a large corrected statistic
for one gene forces small ones elsewhere. -/
theorem sum_gcStat (z : Fin m → ℝ) (h : ∑ k, z k ^ 2 ≠ 0) : ∑ j, gcStat z j = m := by
  simp_rw [gcStat_eq]
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, div_self h, mul_one]

/-- **Cross-coupling.** Raising the statistic of a different gene `k ≠ j` strictly lowers the
corrected statistic of gene `j` (when `z_j ≠ 0`): a strong non-null signal at `k` inflates `λ̂`
and makes every other gene more conservative. -/
theorem gcStat_update_lt (z : Fin m → ℝ) {j k : Fin m} (hjk : k ≠ j) (hj : z j ≠ 0) {t : ℝ}
    (ht : z k ^ 2 < t ^ 2) : gcStat (Function.update z k t) j < gcStat z j := by
  rw [gcStat_eq, gcStat_eq, Function.update_of_ne hjk.symm]
  have hpos : 0 < ∑ i, z i ^ 2 :=
    lt_of_lt_of_le (pow_pos (abs_pos.mpr hj) 2 |>.trans_eq (sq_abs _))
      (Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ j))
  have hlt : ∑ i, z i ^ 2 < ∑ i, Function.update z k t i ^ 2 := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨k, Finset.mem_univ k, by simpa using ht⟩
    by_cases hik : i = k
    · subst hik
      simpa using ht.le
    · rw [Function.update_of_ne hik]
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Fin.pos j)
  exact div_lt_div_of_pos_left (by positivity) hpos hlt


/-! ### The `χ²₁` reference tail as a real-valued function -/

/-- The `χ²₁` tail is finite. -/
theorem chiSqOneTail_ne_top (c : ℝ) : chiSqOneTail c ≠ ⊤ := by
  rw [chiSqOneTail_eq_gaussianReal]
  exact measure_ne_top _ _

/-- The `χ²₁` tail is antitone on all of `ℝ`. -/
theorem antitone_chiSqOneTail : Antitone chiSqOneTail := fun a b hab => by
  rw [chiSqOneTail_eq_gaussianReal, chiSqOneTail_eq_gaussianReal]
  exact measure_mono fun x hx => lt_of_le_of_lt hab hx

/-- The `χ²₁` tail is positive at every nonnegative threshold. -/
theorem chiSqOneTail_pos {c : ℝ} (hc : 0 ≤ c) : 0 < chiSqOneTail c :=
  lt_of_le_of_lt (zero_le) (chiSqOneTail_lt_of_lt hc (lt_add_one c))

/-- The `χ²₁` tail as a real number, the reference upper tail `G` of the multiple-testing
interface `RareVariantInference.MultipleTesting.IsTailCalibratedFamily`. -/
noncomputable def chiSqOneTailReal (c : ℝ) : ℝ :=
  (chiSqOneTail c).toReal

/-- The real `χ²₁` tail is antitone. -/
theorem antitone_chiSqOneTailReal : Antitone chiSqOneTailReal := fun _ _ hab =>
  ENNReal.toReal_mono (chiSqOneTail_ne_top _) (antitone_chiSqOneTail hab)

/-- The real `χ²₁` tail is strictly decreasing on `[0, ∞)`. -/
theorem chiSqOneTailReal_lt_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    chiSqOneTailReal b < chiSqOneTailReal a :=
  ENNReal.toReal_strict_mono (chiSqOneTail_ne_top _) (chiSqOneTail_lt_of_lt ha hab)

/-- Converting the real tail back to `ℝ≥0∞` recovers `chiSqOneTail`. -/
theorem ofReal_chiSqOneTailReal (c : ℝ) : ENNReal.ofReal (chiSqOneTailReal c) = chiSqOneTail c :=
  ENNReal.ofReal_toReal (chiSqOneTail_ne_top c)

/-! ### Random scores: exact calibration with `λ̂` is impossible -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The corrected statistics `S_j / λ̂` of a family of random scores `Z : Fin m → Ω → ℝ`,
with `λ̂` computed on the same sample point from all genes. -/
noncomputable def gcStatRV (Z : Fin m → Ω → ℝ) : Fin m → Ω → ℝ :=
  fun j ω => gcStat (fun k => Z k ω) j

/-- The corrected statistics of measurable scores are measurable. -/
theorem measurable_gcStatRV {Z : Fin m → Ω → ℝ} (hZ : ∀ k, Measurable (Z k)) (j : Fin m) :
    Measurable (gcStatRV Z j) := by
  change Measurable fun ω => Z j ω ^ 2 / ((∑ k, Z k ω ^ 2) / m)
  exact ((hZ j).pow_const 2).div
    ((Finset.measurable_fun_sum _ fun k _ => (hZ k).pow_const 2).div_const _)

/-- At every threshold `c ≥ m` the corrected test never rejects, whatever the law of the scores:
`P(S_j / λ̂ > c) = 0`. -/
theorem measure_lt_gcStatRV_eq_zero (Z : Fin m → Ω → ℝ) (j : Fin m) {c : ℝ} (hc : (m : ℝ) ≤ c) :
    P {ω | c < gcStatRV Z j ω} = 0 := by
  have : {ω | c < gcStatRV Z j ω} = ∅ := by
    ext ω
    simpa [gcStatRV] using (gcStat_le_card (fun k => Z k ω) j).trans hc
  rw [this, measure_empty]

/-- Hence `S_j / λ̂` is strictly conservative against `χ²₁` at every threshold `c ≥ m`. -/
theorem measure_lt_gcStatRV_lt_chiSqOneTail (Z : Fin m → Ω → ℝ) (j : Fin m) {c : ℝ}
    (hc : (m : ℝ) ≤ c) : P {ω | c < gcStatRV Z j ω} < chiSqOneTail c := by
  rw [measure_lt_gcStatRV_eq_zero Z j hc]
  exact chiSqOneTail_pos ((Nat.cast_nonneg m).trans hc)

/-- **True-`λ` calibration does not transfer to `λ̂`.** In T38's exact model
(`CommonInflationModel`: every null score is `𝒩(0, λ)`), dividing by the true `λ` is calibrated
at every threshold, while dividing by the mean estimate `λ̂` of the same scores is not
calibrated at any threshold `c ≥ m`. No independence or other dependence assumption is needed
for either half. -/
theorem calibrated_true_and_not_calibrated_estimated (G : CommonInflationModel P (Fin m))
    (j : Fin m) :
    (∀ c, P {ω | c < G.score j ω ^ 2 / G.lam} = chiSqOneTail c) ∧
      ∀ c, (m : ℝ) ≤ c → P {ω | c < gcStatRV G.score j ω} < chiSqOneTail c :=
  ⟨G.measure_reject_eq j, fun _ hc => measure_lt_gcStatRV_lt_chiSqOneTail _ j hc⟩

/-- Exact `χ²₁` calibration of `S_j / λ̂` at every threshold is false for every law of the scores,
in particular in T38's model. -/
theorem not_forall_measure_lt_gcStatRV_eq (Z : Fin m → Ω → ℝ) (j : Fin m) :
    ¬ ∀ c, P {ω | c < gcStatRV Z j ω} = chiSqOneTail c := fun h =>
  (measure_lt_gcStatRV_lt_chiSqOneTail (P := P) Z j le_rfl).ne (h m)

/-! ### Calibration of `S / λ̂` as an assumption -/

/-- **Calibration of `S / λ̂` is an assumption on `S / λ̂` itself.** The estimated-`λ̂` family is a
tail-calibrated family in the sense of `RareVariantInference.MultipleTesting` (reference tail
`χ²₁`) exactly when every null corrected statistic is conservative against `χ²₁`:
`P(S_i / λ̂ ≥ s) ≤ P(χ²₁ > s)` for all `s`. By
`calibrated_true_and_not_calibrated_estimated` this is not implied by T38's true-`λ` model. -/
theorem isTailCalibratedFamily_gcStatRV_iff {Z : Fin m → Ω → ℝ} (hZ : ∀ k, Measurable (Z k))
    (H0 : Finset (Fin m)) :
    MultipleTesting.IsTailCalibratedFamily P (gcStatRV Z) (fun _ => chiSqOneTailReal) H0 ↔
      ∀ i ∈ H0, ∀ s, P {ω | s ≤ gcStatRV Z i ω} ≤ chiSqOneTail s := by
  constructor
  · intro h i hi s
    simpa [ofReal_chiSqOneTailReal] using h.null_tail_le i hi s
  · intro h
    exact ⟨measurable_gcStatRV hZ, fun _ => antitone_chiSqOneTailReal,
      fun i hi s => by simpa [ofReal_chiSqOneTailReal] using h i hi s⟩

/-- **Bonferroni needs no dependence assumption.** Under the calibration assumption for
`S / λ̂` at threshold `s`, the probability that some true null is rejected is at most
`|H0| · P(χ²₁ > s)`, however strongly `λ̂` couples the statistics. -/
theorem measure_exists_le_gcStatRV_le (Z : Fin m → Ω → ℝ) {H0 : Finset (Fin m)} {s : ℝ}
    (hcal : ∀ i ∈ H0, P {ω | s ≤ gcStatRV Z i ω} ≤ chiSqOneTail s) :
    P {ω | ∃ i ∈ H0, s ≤ gcStatRV Z i ω} ≤ H0.card * chiSqOneTail s := by
  have hset : {ω | ∃ i ∈ H0, s ≤ gcStatRV Z i ω} = ⋃ i ∈ H0, {ω | s ≤ gcStatRV Z i ω} := by
    ext ω
    simp
  rw [hset]
  calc P (⋃ i ∈ H0, {ω | s ≤ gcStatRV Z i ω})
      ≤ ∑ i ∈ H0, P {ω | s ≤ gcStatRV Z i ω} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ H0, chiSqOneTail s := Finset.sum_le_sum hcal
    _ = H0.card * chiSqOneTail s := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### When calibration holds approximately: `λ̂` concentrating around `λ`

Here `L : Ω → ℝ` is any random estimate of the inflation factor (mean, median, leave-one-out,
...), and only the marginal law `𝒩(0, λ)` of one null score is assumed. Nothing is assumed
about the joint law of the score and `L`: the coupling is absorbed into the probability
`P Eᶜ` of the event where `L` is far from `λ`. -/

/-- **Upper sandwich.** If `L ≥ κ λ` on an event `E` (`κ > 0`, e.g. `κ = 1 - δ`), then for
`c ≥ 0`, `P(Z² / L > c) ≤ P(χ²₁ > c κ) + P(Eᶜ)`. -/
theorem measure_lt_div_le_chiSqOneTail_add {Z : Ω → ℝ} {lam : ℝ≥0} (hlam : lam ≠ 0)
    (hZ : HasLaw Z (gaussianReal 0 lam) P) {L : Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) {E : Set Ω}
    (hE : ∀ ω ∈ E, κ * lam ≤ L ω) {c : ℝ} (hc : 0 ≤ c) :
    P {ω | c < Z ω ^ 2 / L ω} ≤ chiSqOneTail (c * κ) + P Eᶜ := by
  have hlam0 : (0 : ℝ) < lam := lt_of_le_of_ne lam.2 (by exact_mod_cast hlam.symm)
  have htrue : P {ω | c * κ < Z ω ^ 2 / lam} = chiSqOneTail (c * κ) := by
    rw [measure_reject_eq_chiSqOneTail hlam hZ hlam0, mul_div_cancel_right₀ _ hlam0.ne']
  calc P {ω | c < Z ω ^ 2 / L ω}
      ≤ P ({ω | c < Z ω ^ 2 / L ω} ∩ E) + P ({ω | c < Z ω ^ 2 / L ω} \ E) :=
        measure_le_inter_add_sdiff _ _ _
    _ ≤ P {ω | c * κ < Z ω ^ 2 / lam} + P Eᶜ := by
        gcongr
        · rintro ω ⟨hω, hωE⟩
          have hL := hE ω hωE
          have hLpos : 0 < L ω := lt_of_lt_of_le (by positivity) hL
          simp only [Set.mem_ofPred_eq] at hω ⊢
          rw [lt_div_iff₀ hLpos] at hω
          rw [lt_div_iff₀ hlam0]
          nlinarith [mul_le_mul_of_nonneg_left hL hc]
        · exact fun ω hω => hω.2
    _ = chiSqOneTail (c * κ) + P Eᶜ := by rw [htrue]

/-- **Lower sandwich.** If `0 < L ≤ κ λ` on an event `E` (e.g. `κ = 1 + δ`), then for `c ≥ 0`,
`P(χ²₁ > c κ) ≤ P(Z² / L > c) + P(Eᶜ)`. -/
theorem chiSqOneTail_le_measure_lt_div_add {Z : Ω → ℝ} {lam : ℝ≥0} (hlam : lam ≠ 0)
    (hZ : HasLaw Z (gaussianReal 0 lam) P) {L : Ω → ℝ} {κ : ℝ} {E : Set Ω}
    (hE : ∀ ω ∈ E, 0 < L ω ∧ L ω ≤ κ * lam) {c : ℝ} (hc : 0 ≤ c) :
    chiSqOneTail (c * κ) ≤ P {ω | c < Z ω ^ 2 / L ω} + P Eᶜ := by
  have hlam0 : (0 : ℝ) < lam := lt_of_le_of_ne lam.2 (by exact_mod_cast hlam.symm)
  have htrue : P {ω | c * κ < Z ω ^ 2 / lam} = chiSqOneTail (c * κ) := by
    rw [measure_reject_eq_chiSqOneTail hlam hZ hlam0, mul_div_cancel_right₀ _ hlam0.ne']
  rw [← htrue]
  calc P {ω | c * κ < Z ω ^ 2 / lam}
      ≤ P ({ω | c * κ < Z ω ^ 2 / lam} ∩ E) + P ({ω | c * κ < Z ω ^ 2 / lam} \ E) :=
        measure_le_inter_add_sdiff _ _ _
    _ ≤ P {ω | c < Z ω ^ 2 / L ω} + P Eᶜ := by
        gcongr
        · rintro ω ⟨hω, hωE⟩
          obtain ⟨hLpos, hL⟩ := hE ω hωE
          simp only [Set.mem_ofPred_eq] at hω ⊢
          rw [lt_div_iff₀ hlam0] at hω
          rw [lt_div_iff₀ hLpos]
          nlinarith [mul_le_mul_of_nonneg_left hL hc]
        · exact fun ω hω => hω.2

/-! ### When calibration fails: a biased `λ̂` -/

/-- **Under-estimated `λ̂` is anti-conservative.** If `0 < L ≤ κ λ` everywhere with `κ < 1`,
then `P(Z² / L > c) > P(χ²₁ > c)` at every `c > 0`. -/
theorem chiSqOneTail_lt_measure_lt_div_of_le_mul {Z : Ω → ℝ} {lam : ℝ≥0} (hlam : lam ≠ 0)
    (hZ : HasLaw Z (gaussianReal 0 lam) P) {L : Ω → ℝ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hL : ∀ ω, 0 < L ω ∧ L ω ≤ κ * lam) {c : ℝ} (hc : 0 < c) :
    chiSqOneTail c < P {ω | c < Z ω ^ 2 / L ω} := by
  have h := chiSqOneTail_le_measure_lt_div_add hlam hZ (E := Set.univ) (fun ω _ => hL ω) hc.le
  rw [Set.compl_univ, measure_empty, add_zero] at h
  refine lt_of_lt_of_le (chiSqOneTail_lt_of_lt (by positivity) ?_) h
  nlinarith

/-- **Over-estimated `λ̂` is conservative.** If `L ≥ κ λ` everywhere with `κ > 1`, then
`P(Z² / L > c) < P(χ²₁ > c)` at every `c > 0`. Contamination of `λ̂` by non-null genes
(`gcStat_update_lt`) pushes in this direction. -/
theorem measure_lt_div_lt_chiSqOneTail_of_mul_le {Z : Ω → ℝ} {lam : ℝ≥0} (hlam : lam ≠ 0)
    (hZ : HasLaw Z (gaussianReal 0 lam) P) {L : Ω → ℝ} {κ : ℝ} (hκ1 : 1 < κ)
    (hL : ∀ ω, κ * lam ≤ L ω) {c : ℝ} (hc : 0 < c) :
    P {ω | c < Z ω ^ 2 / L ω} < chiSqOneTail c := by
  have h := measure_lt_div_le_chiSqOneTail_add hlam hZ (E := Set.univ) (by linarith)
    (fun ω _ => hL ω) hc.le
  rw [Set.compl_univ, measure_empty, add_zero] at h
  refine lt_of_le_of_lt h (chiSqOneTail_lt_of_lt hc.le ?_)
  nlinarith

/-! ### Dependence: negative coupling and failure of PRDS -/

/-- The corrected statistics are bounded (in `[0, m]`), hence square integrable. -/
theorem memLp_gcStatRV [IsFiniteMeasure P] {Z : Fin m → Ω → ℝ} (hZ : ∀ k, Measurable (Z k))
    (j : Fin m) : MemLp (gcStatRV Z j) 2 P :=
  memLp_of_bounded (a := 0) (b := m)
    (ae_of_all _ fun _ => ⟨gcStat_nonneg _ _, gcStat_le_card _ _⟩)
    (measurable_gcStatRV hZ j).aestronglyMeasurable 2

/-- The covariances of the corrected statistics sum to zero: `∑ᵢ ∑ₖ Cov(Tᵢ, Tₖ) = 0`, because
`∑ᵢ Tᵢ = m` almost surely (`sum_gcStat`). -/
theorem sum_sum_covariance_gcStatRV [IsProbabilityMeasure P] {Z : Fin m → Ω → ℝ}
    (hZ : ∀ k, Measurable (Z k)) (hne : ∀ᵐ ω ∂P, ∑ k, Z k ω ^ 2 ≠ 0) :
    ∑ i, ∑ k, cov[gcStatRV Z i, gcStatRV Z k; P] = 0 := by
  rw [← variance_fun_sum (memLp_gcStatRV hZ)]
  rw [variance_congr (Y := fun _ => (m : ℝ)) (hne.mono fun ω h => by
    simpa [gcStatRV] using sum_gcStat (fun k => Z k ω) h)]
  simp [variance_eq_integral]

/-- **Negative coupling.** If some corrected statistic is nondegenerate (`Var(T_j) > 0`), then
some pair of distinct genes has strictly negative covariance. Pairwise nonnegative covariance,
which positive dependence (PRDS, association) would give for these increasing statistics, is
therefore impossible for the mean-`λ̂` family. -/
theorem exists_covariance_gcStatRV_neg [IsProbabilityMeasure P] {Z : Fin m → Ω → ℝ}
    (hZ : ∀ k, Measurable (Z k)) (hne : ∀ᵐ ω ∂P, ∑ k, Z k ω ^ 2 ≠ 0) {j : Fin m}
    (hvar : 0 < Var[gcStatRV Z j; P]) :
    ∃ i k, i ≠ k ∧ cov[gcStatRV Z i, gcStatRV Z k; P] < 0 := by
  have hsum := sum_sum_covariance_gcStatRV hZ hne
  by_contra hneg
  push Not at hneg
  have hnn : ∀ i k, 0 ≤ cov[gcStatRV Z i, gcStatRV Z k; P] := fun i k => by
    by_cases hik : i = k
    · subst hik
      rw [covariance_self (measurable_gcStatRV hZ i).aemeasurable]
      exact variance_nonneg _ _
    · exact hneg i k hik
  have hpos : 0 < ∑ i, ∑ k, cov[gcStatRV Z i, gcStatRV Z k; P] :=
    calc (0 : ℝ) < cov[gcStatRV Z j, gcStatRV Z j; P] := by
          rwa [covariance_self (measurable_gcStatRV hZ j).aemeasurable]
      _ ≤ ∑ k, cov[gcStatRV Z j, gcStatRV Z k; P] :=
          Finset.single_le_sum (fun k _ => hnn j k) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ k, cov[gcStatRV Z i, gcStatRV Z k; P] :=
          Finset.single_le_sum (f := fun i => ∑ k, cov[gcStatRV Z i, gcStatRV Z k; P])
            (fun i _ => Finset.sum_nonneg fun k _ => hnn i k) (Finset.mem_univ j)
  linarith

/-- **Size of the coupling with equal second moments.** If all corrected statistics have the
same variance `v` and all distinct pairs the same covariance `γ` (as for exchangeable scores),
then `γ = -v / (m - 1)`: the negative coupling is exact and of order `1 / m`. -/
theorem covariance_gcStatRV_eq_of_forall_eq [IsProbabilityMeasure P] {Z : Fin m → Ω → ℝ}
    (hZ : ∀ k, Measurable (Z k)) (hne : ∀ᵐ ω ∂P, ∑ k, Z k ω ^ 2 ≠ 0) (hm : 2 ≤ m) {v γ : ℝ}
    (hv : ∀ i, Var[gcStatRV Z i; P] = v)
    (hγ : ∀ i k, i ≠ k → cov[gcStatRV Z i, gcStatRV Z k; P] = γ) :
    γ = -v / (m - 1) := by
  classical
  have hsum := sum_sum_covariance_gcStatRV hZ hne
  have hrow : ∀ i, ∑ k, cov[gcStatRV Z i, gcStatRV Z k; P] = v + (m - 1) * γ := fun i => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      covariance_self (measurable_gcStatRV hZ i).aemeasurable, hv i,
      Finset.sum_congr rfl fun k hk => hγ i k (Finset.ne_of_mem_erase hk).symm,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  field_simp
  have := (mul_eq_zero.mp hsum).resolve_left hm0
  linarith

/-- **A separation criterion that refutes PRDS.** Suppose gene `k`'s p-value is at least `u`
(almost surely) whenever `p i ≤ s`, and below `u` whenever `s < p i ≤ t`, with both events of
positive probability. Then the increasing set `D = {x | u ≤ x k}` has
`P(P ∈ D | p i ≤ t) < P(P ∈ D | p i ≤ s)`, contradicting `IsPRDSOn.measure_inter_mul_le`. -/
theorem not_isPRDSOn_of_separated {μ : Measure Ω} [IsFiniteMeasure μ] {p : Fin m → Ω → ℝ}
    (hp : ∀ i, Measurable (p i)) {H0 : Finset (Fin m)} {i k : Fin m} (hi : i ∈ H0)
    {s t u : ℝ} (hst : s ≤ t) (hA : μ {ω | p i ω ≤ s} ≠ 0)
    (hB : μ {ω | s < p i ω ∧ p i ω ≤ t} ≠ 0) (hAu : ∀ᵐ ω ∂μ, p i ω ≤ s → u ≤ p k ω)
    (hBu : ∀ᵐ ω ∂μ, s < p i ω → p i ω ≤ t → p k ω < u) :
    ¬ IsPRDSOn μ p H0 := by
  intro h
  have hD : MeasurableSet {x : Fin m → ℝ | u ≤ x k} :=
    measurableSet_le measurable_const (measurable_pi_apply k)
  have hup : IsUpperSet {x : Fin m → ℝ | u ≤ x k} := fun x y hxy hx => le_trans hx (hxy k)
  have key := h.measure_inter_mul_le hp hi hD hup hst
  have hDs : μ ({ω | (fun j => p j ω) ∈ {x : Fin m → ℝ | u ≤ x k}} ∩ {ω | p i ω ≤ s}) =
      μ {ω | p i ω ≤ s} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hAu] with ω hω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hω h, h⟩⟩
  have hDt : μ ({ω | (fun j => p j ω) ∈ {x : Fin m → ℝ | u ≤ x k}} ∩ {ω | p i ω ≤ t}) =
      μ {ω | p i ω ≤ s} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hAu, hBu] with ω hωA hωB
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h => ⟨hωA h, h.trans hst⟩⟩
    by_contra hs
    exact absurd h.1 (not_le.2 (hωB (not_le.1 hs) h.2))
  have hBm : MeasurableSet {ω | s < p i ω ∧ p i ω ≤ t} :=
    (measurableSet_lt measurable_const (hp i)).inter (measurableSet_le (hp i) measurable_const)
  have hT : μ {ω | p i ω ≤ t} = μ {ω | p i ω ≤ s} + μ {ω | s < p i ω ∧ p i ω ≤ t} := by
    rw [← measure_union _ hBm]
    · congr 1
      ext ω
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases hs : p i ω ≤ s
        · exact Or.inl hs
        · exact Or.inr ⟨not_le.1 hs, h⟩
      · rintro (h | h)
        · exact h.trans hst
        · exact h.2
    · exact Set.disjoint_left.2 fun ω h1 h2 => absurd h1 (not_le.2 h2.1)
  rw [hDs, hDt, hT, mul_add] at key
  have hfin : μ {ω | p i ω ≤ s} * μ {ω | p i ω ≤ s} ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hzero : μ {ω | p i ω ≤ s} * μ {ω | s < p i ω ∧ p i ω ≤ t} ≤ 0 :=
    ENNReal.le_of_add_le_add_left hfin (by simpa using key)
  exact (mul_ne_zero hA hB) (le_antisymm hzero (zero_le))

/-- With two genes the coupling is total: `T₀ + T₁ = 2` whenever some score is nonzero. -/
theorem gcStat_two_add (z : Fin 2 → ℝ) (h : ∑ k, z k ^ 2 ≠ 0) : gcStat z 0 + gcStat z 1 = 2 := by
  have := sum_gcStat z h
  rw [Fin.sum_univ_two] at this
  rw [this]
  norm_num

/-- **PRDS fails for the coupled two-gene family.** With `m = 2` genes and the mean estimate
`λ̂`, the `χ²₁` p-values `pⱼ = P(χ²₁ > Sⱼ / λ̂)` are not PRDS on any set of true nulls
containing gene `0`, as soon as both `{T₀ ≥ 1}` and `{T₀ < 1}` have positive probability and
the scores do not vanish simultaneously (almost surely). No independence, Gaussianity or other
assumption on the scores is involved: `T₁ = 2 - T₀` makes `p₁` a decreasing function of `p₀`. -/
theorem not_isPRDSOn_tailPValue_gcStatRV_two [IsFiniteMeasure P] {Z : Fin 2 → Ω → ℝ}
    (hZ : ∀ k, Measurable (Z k)) (hne : ∀ᵐ ω ∂P, ∑ k, Z k ω ^ 2 ≠ 0) {H0 : Finset (Fin 2)}
    (h0 : 0 ∈ H0) (hA : P {ω | 1 ≤ gcStatRV Z 0 ω} ≠ 0) (hB : P {ω | gcStatRV Z 0 ω < 1} ≠ 0) :
    ¬ IsPRDSOn P (MultipleTesting.tailPValue (gcStatRV Z) fun _ => chiSqOneTailReal) H0 := by
  set G := chiSqOneTailReal
  have hnn (i : Fin 2) (ω : Ω) : 0 ≤ gcStatRV Z i ω := gcStat_nonneg _ _
  -- `G T₀ ≤ G 1` forces `T₀ ≥ 1`, and `G 1 < G T₀` forces `T₀ < 1`.
  have hge (ω : Ω) (h : G (gcStatRV Z 0 ω) ≤ G 1) : 1 ≤ gcStatRV Z 0 ω := by
    by_contra hlt
    exact absurd h (not_le.2 (chiSqOneTailReal_lt_of_lt (hnn 0 ω) (not_le.1 hlt)))
  have hlt (ω : Ω) (h : G 1 < G (gcStatRV Z 0 ω)) : gcStatRV Z 0 ω < 1 := by
    by_contra hle
    exact absurd h (not_lt.2 (antitone_chiSqOneTailReal (not_lt.1 hle)))
  refine not_isPRDSOn_of_separated (i := 0) (k := 1) (s := G 1) (t := G 0) (u := G 1)
    (fun i => antitone_chiSqOneTailReal.measurable.comp (measurable_gcStatRV hZ i)) h0
    (antitone_chiSqOneTailReal zero_le_one) ?_ ?_ ?_ ?_
  · refine fun h => hA (measure_mono_null (fun ω hω => ?_) h)
    exact antitone_chiSqOneTailReal hω
  · refine fun h => hB (measure_mono_null (fun ω hω => ?_) h)
    exact ⟨chiSqOneTailReal_lt_of_lt (hnn 0 ω) hω, antitone_chiSqOneTailReal (hnn 0 ω)⟩
  · filter_upwards [hne] with ω hω h
    change G (gcStatRV Z 0 ω) ≤ G 1 at h
    change G 1 ≤ G (gcStatRV Z 1 ω)
    have hsum := gcStat_two_add (fun k => Z k ω) hω
    have h1 := hge ω h
    exact antitone_chiSqOneTailReal (show gcStatRV Z 1 ω ≤ 1 by
      change gcStat (fun k => Z k ω) 1 ≤ 1
      change 1 ≤ gcStat (fun k => Z k ω) 0 at h1
      linarith)
  · filter_upwards [hne] with ω hω h _
    change G 1 < G (gcStatRV Z 0 ω) at h
    change G (gcStatRV Z 1 ω) < G 1
    have hsum := gcStat_two_add (fun k => Z k ω) hω
    have h1 := hlt ω h
    exact chiSqOneTailReal_lt_of_lt zero_le_one (show 1 < gcStatRV Z 1 ω by
      change 1 < gcStat (fun k => Z k ω) 1
      change gcStat (fun k => Z k ω) 0 < 1 at h1
      linarith)

/-! ### Two independent Gaussian null genes: the assumption fails in T38's model -/

/-- `P(|N(0,1)| ≤ 1) > 1/2`, from the density bounds `φ ≥ 7c/8` on `[-1/2, 1/2]` and `φ ≥ c/2` on
`[-1, 1]`, where `c = 1/√(2π) > 4/11`. -/
private theorem half_lt_gaussianReal_Icc : (1 / 2 : ℝ≥0∞) < gaussianReal 0 1 (Set.Icc (-1) 1) := by
  set c : ℝ := (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ with hc_def
  have hsqrt : √(2 * Real.pi * ((1 : ℝ≥0) : ℝ)) < 11 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    have := Real.pi_lt_d2
    push_cast
    nlinarith
  have hsqrt0 : 0 < √(2 * Real.pi * ((1 : ℝ≥0) : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hc : 4 / 11 < c := by
    rw [hc_def, lt_inv_comm₀ (by norm_num) hsqrt0]
    linarith
  have hpdf (x : ℝ) : gaussianPDF 0 1 x = ENNReal.ofReal (c * Real.exp (-x ^ 2 / 2)) := by
    simp [gaussianPDF, gaussianPDFReal, hc_def]
  have hexp (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.exp (-x ^ 2 / 2) := by
    have := Real.add_one_le_exp (-x ^ 2 / 2)
    linarith
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  set I := Set.Icc (-1 : ℝ) 1
  set J := Set.Icc (-1 / 2 : ℝ) (1 / 2)
  have hJI : J ⊆ I := Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hJ : ENNReal.ofReal (7 * c / 8) ≤ gaussianReal 0 1 J := by
    rw [gaussianReal_apply 0 one_ne_zero]
    calc ENNReal.ofReal (7 * c / 8) = ∫⁻ _ in J, ENNReal.ofReal (7 * c / 8) := by
          rw [setLIntegral_const, Real.volume_Icc]; norm_num
      _ ≤ ∫⁻ x in J, gaussianPDF 0 1 x := by
          refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
          rw [hpdf]
          refine ENNReal.ofReal_le_ofReal ?_
          have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [hx.1, hx.2]
          nlinarith [hexp x]
  have hIJ : ENNReal.ofReal (c / 2) ≤ gaussianReal 0 1 (I \ J) := by
    rw [gaussianReal_apply 0 one_ne_zero]
    calc ENNReal.ofReal (c / 2) = ∫⁻ _ in I \ J, ENNReal.ofReal (c / 2) := by
          rw [setLIntegral_const, measure_sdiff hJI measurableSet_Icc.nullMeasurableSet
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top), Real.volume_Icc,
            Real.volume_Icc, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ ≤ ∫⁻ x in I \ J, gaussianPDF 0 1 x := by
          refine setLIntegral_mono' (measurableSet_Icc.diff measurableSet_Icc) fun x hx => ?_
          rw [hpdf]
          refine ENNReal.ofReal_le_ofReal ?_
          have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1.1, hx.1.2]
          nlinarith [hexp x]
  have hsplit : gaussianReal 0 1 I = gaussianReal 0 1 J + gaussianReal 0 1 (I \ J) := by
    rw [← measure_union Set.disjoint_sdiff_right (measurableSet_Icc.diff measurableSet_Icc),
      Set.union_sdiff_cancel hJI]
  rw [hsplit]
  calc (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    _ < ENNReal.ofReal (7 * c / 8 + c / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    _ = ENNReal.ofReal (7 * c / 8) + ENNReal.ofReal (c / 2) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
    _ ≤ _ := add_le_add hJ hIJ

/-- `P(χ²₁ > 1) < 1/2` (its value is `≈ 0.317`). -/
theorem chiSqOneTail_one_lt_half : chiSqOneTail 1 < 1 / 2 := by
  have hset : {x : ℝ | 1 < x ^ 2} = (Set.Icc (-1) 1)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
    rw [← one_lt_sq_iff_one_lt_abs]
  rw [chiSqOneTail_eq_gaussianReal, hset, prob_compl_eq_one_sub measurableSet_Icc]
  have h := half_lt_gaussianReal_Icc
  rw [ENNReal.sub_lt_iff_lt_right (measure_ne_top _ _) prob_le_one]
  calc (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
    _ < 1 / 2 + gaussianReal 0 1 (Set.Icc (-1) 1) :=
        ENNReal.add_lt_add_left (by norm_num) h

/-- With two genes and a nonzero score vector, `T₀ ≥ 1` iff `z₁² ≤ z₀²`, and `T₀ < 1` iff
`z₀² < z₁²`. -/
theorem one_le_gcStat_two_iff (z : Fin 2 → ℝ) (h : ∑ k, z k ^ 2 ≠ 0) :
    (1 ≤ gcStat z 0 ↔ z 1 ^ 2 ≤ z 0 ^ 2) ∧ (gcStat z 0 < 1 ↔ z 0 ^ 2 < z 1 ^ 2) := by
  rw [Fin.sum_univ_two] at h
  have hpos : 0 < z 0 ^ 2 + z 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  rw [gcStat_eq, Fin.sum_univ_two, le_div_iff₀ hpos, div_lt_iff₀ hpos]
  push_cast
  constructor <;> constructor <;> intro <;> linarith

section TwoGaussian

variable [IsProbabilityMeasure P] (G : CommonInflationModel P (Fin 2))

/-- The joint law of two independent null scores of T38's model is `𝒩(0, λ) ⊗ 𝒩(0, λ)`. -/
private theorem map_pair_eq (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    P.map (fun ω => (G.score 0 ω, G.score 1 ω)) =
      (gaussianReal 0 G.lam).prod (gaussianReal 0 G.lam) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hmeas 0).aemeasurable (hmeas 1).aemeasurable).1
    hind, (G.hasLaw_score 0).map_eq, (G.hasLaw_score 1).map_eq]

/-- Exchangeability of two independent null scores. -/
private theorem measure_swap_eq (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    P ((fun ω => (G.score 1 ω, G.score 0 ω)) ⁻¹' S) =
      P ((fun ω => (G.score 0 ω, G.score 1 ω)) ⁻¹' S) := by
  have hpair : Measurable fun ω => (G.score 0 ω, G.score 1 ω) := (hmeas 0).prodMk (hmeas 1)
  change P ((fun ω => (G.score 0 ω, G.score 1 ω)) ⁻¹' (Prod.swap ⁻¹' S)) = _
  rw [← Measure.map_apply hpair (measurable_swap hS), ← Measure.map_apply hpair hS,
    map_pair_eq G hmeas hind, ← Measure.map_apply measurable_swap hS, Measure.prod_swap]

/-- Two independent `𝒩(0, λ)` scores have equal squares with probability `0`. -/
private theorem measure_sq_eq_sq_eq_zero (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    P {ω | G.score 0 ω ^ 2 = G.score 1 ω ^ 2} = 0 := by
  have hpair : Measurable fun ω => (G.score 0 ω, G.score 1 ω) := (hmeas 0).prodMk (hmeas 1)
  have hS : MeasurableSet {x : ℝ × ℝ | x.1 ^ 2 = x.2 ^ 2} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  change P ((fun ω => (G.score 0 ω, G.score 1 ω)) ⁻¹' {x : ℝ × ℝ | x.1 ^ 2 = x.2 ^ 2}) = 0
  rw [← Measure.map_apply hpair hS, map_pair_eq G hmeas hind, Measure.prod_apply hS]
  have hpt (x : ℝ) :
      gaussianReal 0 G.lam (Prod.mk x ⁻¹' {x : ℝ × ℝ | x.1 ^ 2 = x.2 ^ 2}) = 0 := by
    refine measure_mono_null (t := {x, -x}) (fun y hy => ?_) ?_
    · simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hy.symm with h | h <;> simp [h]
    · exact (gaussianReal_absolutelyContinuous 0 G.lam_ne_zero) ((Set.toFinite _).measure_zero _)
  rw [lintegral_congr hpt]
  exact lintegral_zero

omit [IsProbabilityMeasure P] in
/-- Under T38's model the scores do not vanish simultaneously, almost surely. -/
theorem ae_sum_sq_ne_zero (hmeas : ∀ i, Measurable (G.score i)) :
    ∀ᵐ ω ∂P, ∑ k, G.score k ω ^ 2 ≠ 0 := by
  have h0 : P (G.score 0 ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply (hmeas 0) (measurableSet_singleton 0), (G.hasLaw_score 0).map_eq]
    exact (gaussianReal_absolutelyContinuous 0 G.lam_ne_zero) Real.volume_singleton
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [Set.mem_ofPred_eq, not_not, Fin.sum_univ_two] at hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact (pow_eq_zero_iff two_ne_zero).1
    (by nlinarith [sq_nonneg (G.score 0 ω), sq_nonneg (G.score 1 ω)])

private theorem half_le_measure_sq_le_sq (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    1 / 2 ≤ P {ω | G.score 1 ω ^ 2 ≤ G.score 0 ω ^ 2} := by
  have hS : MeasurableSet {x : ℝ × ℝ | x.2 ^ 2 ≤ x.1 ^ 2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hsym : P {ω | G.score 0 ω ^ 2 ≤ G.score 1 ω ^ 2} =
      P {ω | G.score 1 ω ^ 2 ≤ G.score 0 ω ^ 2} := measure_swap_eq G hmeas hind hS
  have hcover : (1 : ℝ≥0∞) ≤ P {ω | G.score 1 ω ^ 2 ≤ G.score 0 ω ^ 2} +
      P {ω | G.score 1 ω ^ 2 ≤ G.score 0 ω ^ 2} := by
    rw [← measure_univ (μ := P)]
    nth_rewrite 2 [← hsym]
    refine le_trans (measure_mono fun ω _ => ?_) (measure_union_le _ _)
    exact le_total (G.score 1 ω ^ 2) (G.score 0 ω ^ 2)
  by_contra hlt
  push Not at hlt
  have := ENNReal.add_lt_add hlt hlt
  rw [ENNReal.add_halves] at this
  exact absurd hcover (not_le.2 this)

/-- **The calibration assumption fails at `s = 1`.** With two genes whose null scores are
independent `𝒩(0, λ)` (T38's model plus independence), `P(S₀ / λ̂ ≥ 1) ≥ 1/2`. -/
theorem half_le_measure_one_le_gcStatRV_two (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    1 / 2 ≤ P {ω | 1 ≤ gcStatRV G.score 0 ω} := by
  refine (half_le_measure_sq_le_sq G hmeas hind).trans_eq (measure_congr ?_)
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_sum_sq_ne_zero G hmeas] with ω hω
  exact ((one_le_gcStat_two_iff (fun k => G.score k ω) hω).1).symm

/-- With two independent `𝒩(0, λ)` null scores, `P(S₀ / λ̂ < 1) ≥ 1/2`. -/
theorem half_le_measure_gcStatRV_two_lt_one (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    1 / 2 ≤ P {ω | gcStatRV G.score 0 ω < 1} := by
  have hS : MeasurableSet {x : ℝ × ℝ | x.2 ^ 2 ≤ x.1 ^ 2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hsym : P {ω | G.score 0 ω ^ 2 ≤ G.score 1 ω ^ 2} =
      P {ω | G.score 1 ω ^ 2 ≤ G.score 0 ω ^ 2} := measure_swap_eq G hmeas hind hS
  have hdiag := measure_sq_eq_sq_eq_zero G hmeas hind
  rw [measure_eq_zero_iff_ae_notMem] at hdiag
  refine (half_le_measure_sq_le_sq G hmeas hind).trans_eq (hsym.symm.trans (measure_congr ?_))
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_sum_sq_ne_zero G hmeas, hdiag] with ω hω hne
  change _ ↔ gcStat (fun k => G.score k ω) 0 < 1
  rw [(one_le_gcStat_two_iff (fun k => G.score k ω) hω).2]
  exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩

/-- **Anti-conservative in T38's model.** With two independent `𝒩(0, λ)` null scores the
estimated-`λ̂` test rejects at threshold `1` with probability at least `1/2`, more than the
nominal `P(χ²₁ > 1) ≈ 0.317`, although dividing by the true `λ` is exactly calibrated. -/
theorem chiSqOneTail_lt_measure_one_le_gcStatRV_two (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    chiSqOneTail 1 < P {ω | 1 ≤ gcStatRV G.score 0 ω} :=
  chiSqOneTail_one_lt_half.trans_le (half_le_measure_one_le_gcStatRV_two G hmeas hind)

/-- **Calibration of `S / λ̂` does not follow from true-`λ` calibration.** In T38's model with two
independent null genes, the estimated-`λ̂` family is not a tail-calibrated family against
`χ²₁` on any null set containing gene `0`. -/
theorem not_isTailCalibratedFamily_gcStatRV_two (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) {H0 : Finset (Fin 2)} (h0 : 0 ∈ H0) :
    ¬ MultipleTesting.IsTailCalibratedFamily P (gcStatRV G.score) (fun _ => chiSqOneTailReal)
      H0 := fun h =>
  absurd (((isTailCalibratedFamily_gcStatRV_iff hmeas H0).1 h) 0 h0 1)
    (not_le.2 (chiSqOneTail_lt_measure_one_le_gcStatRV_two G hmeas hind))

/-- **PRDS fails in T38's model.** With two independent `𝒩(0, λ)` null scores, the `χ²₁`
p-values of the estimated-`λ̂` statistics are not PRDS on any null set containing gene `0`. -/
theorem not_isPRDSOn_tailPValue_gcStatRV_two_of_indep (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) {H0 : Finset (Fin 2)} (h0 : 0 ∈ H0) :
    ¬ IsPRDSOn P (MultipleTesting.tailPValue (gcStatRV G.score) fun _ => chiSqOneTailReal) H0 :=
  not_isPRDSOn_tailPValue_gcStatRV_two hmeas (ae_sum_sq_ne_zero G hmeas) h0
    (lt_of_lt_of_le (by norm_num) (half_le_measure_one_le_gcStatRV_two G hmeas hind)).ne'
    (lt_of_lt_of_le (by norm_num) (half_le_measure_gcStatRV_two_lt_one G hmeas hind)).ne'

/-- With two independent `𝒩(0, λ)` null scores the corrected statistic `T₀` is nondegenerate. -/
theorem variance_gcStatRV_two_pos (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) : 0 < Var[gcStatRV G.score 0; P] := by
  refine lt_of_le_of_ne (variance_nonneg _ _) fun h => ?_
  have hconst := ae_eq_integral_of_variance_eq_zero (memLp_gcStatRV hmeas 0) h.symm
  have hhalf : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
  by_cases hE : 1 ≤ P[gcStatRV G.score 0]
  · refine (lt_of_lt_of_le hhalf (half_le_measure_gcStatRV_two_lt_one G hmeas hind)).ne'
      (measure_mono_null_ae ?_ (measure_empty (μ := P)))
    filter_upwards [hconst] with ω hω hlt
    rw [hω] at hlt
    exact absurd hE (not_le.2 hlt)
  · refine (lt_of_lt_of_le hhalf (half_le_measure_one_le_gcStatRV_two G hmeas hind)).ne'
      (measure_mono_null_ae ?_ (measure_empty (μ := P)))
    filter_upwards [hconst] with ω hω hle
    rw [hω] at hle
    exact absurd hle hE

/-- **Negative covariance in T38's model.** With two independent `𝒩(0, λ)` null scores,
`Cov(S₀ / λ̂, S₁ / λ̂) < 0`. -/
theorem covariance_gcStatRV_two_neg (hmeas : ∀ i, Measurable (G.score i))
    (hind : IndepFun (G.score 0) (G.score 1) P) :
    cov[gcStatRV G.score 0, gcStatRV G.score 1; P] < 0 := by
  have hsum := sum_sum_covariance_gcStatRV hmeas (ae_sum_sq_ne_zero G hmeas)
  simp only [Fin.sum_univ_two] at hsum
  rw [covariance_self (measurable_gcStatRV hmeas 0).aemeasurable,
    covariance_self (measurable_gcStatRV hmeas 1).aemeasurable,
    covariance_comm (X := gcStatRV G.score 1)] at hsum
  have h0 := variance_gcStatRV_two_pos G hmeas hind
  have h1 := variance_nonneg (gcStatRV G.score 1) P
  linarith

end TwoGaussian

end MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControlEstimated
