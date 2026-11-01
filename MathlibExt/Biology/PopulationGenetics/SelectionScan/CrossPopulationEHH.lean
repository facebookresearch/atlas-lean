/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.SelectionScan.SelectiveSweep
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Cross-population haplotype statistics and their exchangeability symmetry

The cross-population extended haplotype homozygosity score (XP-EHH, Sabeti et al. 2007) is a
log ratio of two haplotype-homozygosity statistics, one per population, while the relative
extended haplotype homozygosity of the long-range haplotype test (Sabeti et al. 2002) is the
plain (unlogged) ratio of the two core-allele homozygosities.

Exchangeability is an additional calibration assumption, stronger than — not identical
to — the ordinary neutral null of these tests: two neutral populations can have different
demographic histories or sample sizes, and the two carrier groups can have different allele
frequencies, so their joint law need not be swap-invariant. An exchangeable pair is one
whose joint law is invariant under swapping the two statistics. This file proves that
exchangeability alone — no model of the genealogy, no distributional assumption — forces
the log ratio to have a symmetric law, so the two tails of the test carry exactly the same
probability, and gives the resulting equal-tail identities.

`IsExchangeablePair μ X Y` says the law of `(X, Y)` is the law of `(Y, X)`. The main results
are stated for a general pair, then specialised to the two statistics.

## Main results

* `IsExchangeablePair.map_comp`: exchangeability is preserved by applying one measurable
  function to both coordinates.
* `IsExchangeablePair.map_sub_neg`: the difference `X - Y` of an exchangeable pair has a
  symmetric law.
* `IsExchangeablePair.measure_le_sub`, `IsExchangeablePair.measure_abs_sub`: the equal-tail
  identities `μ {t ≤ X - Y} = μ {X - Y ≤ -t}` and `μ {t ≤ |X - Y|} = 2 μ {t ≤ X - Y}`.
* `IsExchangeablePair.measure_le_logRatio`: for positive statistics, the two-sided test on the
  log ratio has equal tails.
* `IsExchangeablePair.measure_le_ratio`: in terms of the ratio itself, `μ {c ≤ I₁ / I₂}` equals
  `μ {I₁ / I₂ ≤ c⁻¹}` — the form used for relative EHH.

## References

* P. C. Sabeti, P. Varilly, B. Fry, J. Lohmueller, E. Hostetter, C. Cotsapas, X. Xie,
  E. H. Byrne, S. A. McCarroll, R. Gaudet, S. F. Schaffner and E. S. Lander (The International
  HapMap Consortium), *Genome-wide detection and characterization of positive selection in
  human populations*, Nature 449 (2007), 913–918.
* P. C. Sabeti et al., *Detecting recent positive selection in the human genome from haplotype
  structure*, Nature 419 (2002), 832–837.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005,
  §15.2 (tests built on a group of transformations leaving the null law invariant).
-/

open MeasureTheory Set Real

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.SelectionScan

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

/-- The pair of statistics `(X, Y)` is exchangeable under `μ`: the joint law is unchanged by
swapping the two coordinates. This is an additional calibration assumption for a two-group
haplotype test, stronger than the ordinary neutral null.
Defined as `IdentDistrib` of the two orderings, so the measurability of the joint laws is
part of the hypothesis rather than restored separately in each theorem. -/
def IsExchangeablePair (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ProbabilityTheory.IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω)) μ μ

namespace IsExchangeablePair

theorem swap (h : IsExchangeablePair μ X Y) : IsExchangeablePair μ Y X := ProbabilityTheory.IdentDistrib.symm h

/-- Applying the same measurable function to both statistics preserves exchangeability. -/
theorem map_comp (h : IsExchangeablePair μ X Y) (hX : Measurable X) (hY : Measurable Y)
    {f : ℝ → ℝ} (hf : Measurable f) :
    IsExchangeablePair μ (fun ω => f (X ω)) (fun ω => f (Y ω)) := by
  have hff : Measurable fun p : ℝ × ℝ => (f p.1, f p.2) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  exact ProbabilityTheory.IdentDistrib.comp h hff

/-- The difference of an exchangeable pair has a symmetric law. -/
theorem map_sub_neg (h : IsExchangeablePair μ X Y) (hX : Measurable X) (hY : Measurable Y) :
    μ.map (fun ω => X ω - Y ω) = μ.map (fun ω => -(X ω - Y ω)) := by
  have hg : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
  calc μ.map (fun ω => X ω - Y ω)
      = (μ.map (fun ω => (X ω, Y ω))).map (fun p : ℝ × ℝ => p.1 - p.2) :=
        (Measure.map_map hg (hX.prodMk hY)).symm
    _ = (μ.map (fun ω => (Y ω, X ω))).map (fun p : ℝ × ℝ => p.1 - p.2) := by rw [ProbabilityTheory.IdentDistrib.map_eq h]
    _ = μ.map (fun ω => Y ω - X ω) := Measure.map_map hg (hY.prodMk hX)
    _ = μ.map (fun ω => -(X ω - Y ω)) := by simp [neg_sub]

/-- Equal tails: the upper tail of `X - Y` at `t` has the same probability as the lower tail
at `-t`. -/
theorem measure_le_sub (h : IsExchangeablePair μ X Y) (hX : Measurable X) (hY : Measurable Y)
    (t : ℝ) : μ {ω | t ≤ X ω - Y ω} = μ {ω | X ω - Y ω ≤ -t} := by
  have hZ : Measurable fun ω => X ω - Y ω := hX.sub hY
  have h1 : μ.map (fun ω => X ω - Y ω) (Set.Ici t)
      = μ.map (fun ω => -(X ω - Y ω)) (Set.Ici t) := by rw [h.map_sub_neg hX hY]
  have hZn : Measurable fun ω => -(X ω - Y ω) := hZ.neg
  rw [Measure.map_apply hZ measurableSet_Ici,
    Measure.map_apply hZn measurableSet_Ici] at h1
  have e2 : (fun ω => -(X ω - Y ω)) ⁻¹' Set.Ici t = {ω | X ω - Y ω ≤ -t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq]
    constructor <;> intro hw <;> linarith
  rw [e2] at h1
  exact h1

/-- A two-sided rejection region splits into two tails of equal probability. -/
theorem measure_abs_sub (h : IsExchangeablePair μ X Y) (hX : Measurable X) (hY : Measurable Y)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ |X ω - Y ω|} = 2 * μ {ω | t ≤ X ω - Y ω} := by
  have hZ : Measurable fun ω => X ω - Y ω := hX.sub hY
  have hsplit : {ω | t ≤ |X ω - Y ω|}
      = {ω | t ≤ X ω - Y ω} ∪ {ω | X ω - Y ω ≤ -t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
    constructor
    · rintro (hw | hw)
      · exact Or.inl hw
      · exact Or.inr (by linarith)
    · rintro (hw | hw)
      · exact Or.inl hw
      · exact Or.inr (by linarith)
  have hdisj : Disjoint {ω | t ≤ X ω - Y ω} {ω | X ω - Y ω ≤ -t} := by
    rw [Set.disjoint_left]
    intro ω hw hw'
    simp only [Set.mem_ofPred_eq] at hw hw'
    linarith
  rw [hsplit, measure_union hdisj (measurableSet_le hZ measurable_const),
    ← h.measure_le_sub hX hY t, two_mul]

/-- For positive statistics, the log ratio — the XP-EHH form — has equal tails. -/
theorem measure_le_logRatio (h : IsExchangeablePair μ X Y) (hX : Measurable X)
    (hY : Measurable Y) (t : ℝ) :
    μ {ω | t ≤ log (X ω) - log (Y ω)} = μ {ω | log (X ω) - log (Y ω) ≤ -t} :=
  (h.map_comp hX hY Real.measurable_log).measure_le_sub hX.log hY.log t

/-- The same statement for the ratio itself, the form used for relative EHH: the probability
that the ratio exceeds `c` equals the probability that it falls below `1 / c`. -/
theorem measure_le_ratio (h : IsExchangeablePair μ X Y) (hX : Measurable X) (hY : Measurable Y)
    (hXpos : ∀ ω, 0 < X ω) (hYpos : ∀ ω, 0 < Y ω) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ X ω / Y ω} = μ {ω | X ω / Y ω ≤ c⁻¹} := by
  have hset₁ : {ω | c ≤ X ω / Y ω} = {ω | log c ≤ log (X ω) - log (Y ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [← Real.log_div (hXpos ω).ne' (hYpos ω).ne',
      Real.log_le_log_iff hc (div_pos (hXpos ω) (hYpos ω))]
  have hset₂ : {ω | X ω / Y ω ≤ c⁻¹} = {ω | log (X ω) - log (Y ω) ≤ -log c} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [← Real.log_div (hXpos ω).ne' (hYpos ω).ne', ← Real.log_inv,
      Real.log_le_log_iff (div_pos (hXpos ω) (hYpos ω)) (by positivity)]
  rw [hset₁, hset₂]
  exact h.measure_le_logRatio hX hY (log c)

end IsExchangeablePair

/-- The cross-population extended haplotype homozygosity score (Sabeti et al. 2007): the log
ratio of the integrated haplotype homozygosities of the same core region in two populations.
Both arguments must be positive for the score to be meaningful. Outside that domain
`Real.log` is totalized by Mathlib, not by the stated junk value: `Real.log 0 = 0` and
`Real.log (-x) = Real.log x`, so for example `xpehh (-2) 1 = log 2`. -/
noncomputable def xpehh (iA iB : ℝ) : ℝ := log iA - log iB

/-- XP-EHH computed from two star-genealogy sweep models with the same recombination rate is
the log ratio of the two ages, with the opposite sign to `ihs`. -/
theorem xpehh_ihh {r T₁ T₂ : ℝ} (hr : 0 < r) (h₁ : 0 < T₁) (h₂ : 0 < T₂) :
    xpehh (ihh r T₁) (ihh r T₂) = log (T₂ / T₁) := by
  rw [xpehh, ihh_eq hr h₁, ihh_eq hr h₂, ← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- Under exchangeability, the XP-EHH score has a symmetric law: the two tails of the
two-sided test carry the same probability. -/
theorem measure_le_xpehh {I₁ I₂ : Ω → ℝ} (h : IsExchangeablePair μ I₁ I₂) (h₁ : Measurable I₁)
    (h₂ : Measurable I₂) (t : ℝ) :
    μ {ω | t ≤ xpehh (I₁ ω) (I₂ ω)} = μ {ω | xpehh (I₁ ω) (I₂ ω) ≤ -t} :=
  h.measure_le_logRatio h₁ h₂ t

end MathlibExt.Biology.PopulationGenetics.SelectionScan
