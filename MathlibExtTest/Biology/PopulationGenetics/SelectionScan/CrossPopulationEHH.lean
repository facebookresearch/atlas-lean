/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.SelectionScan.CrossPopulationEHH
public import Mathlib.Tactic.NormNum

@[expose] public section

open Real MeasureTheory
open MathlibExt.Biology.PopulationGenetics.SelectionScan

namespace MathlibExtTest.Biology.PopulationGenetics.SelectionScan.CrossPopulationEHH

/-! ### A non-vacuous exchangeable pair

Two populations whose integrated haplotype homozygosities are the same random variable: the
pair is exchangeable, and the two tails of the XP-EHH test agree. -/

/-- The common statistic: a positive, measurable function on the sample space `ℝ`. -/
noncomputable def stat : ℝ → ℝ := fun ω => Real.exp ω

theorem measurable_stat : Measurable stat := Real.measurable_exp

theorem stat_pos (ω : ℝ) : 0 < stat ω := Real.exp_pos ω

/-- Equal statistics form an exchangeable pair (the non-vacuity witness). -/
theorem isExchangeablePair_stat (μ : Measure ℝ) : IsExchangeablePair μ stat stat :=
  ProbabilityTheory.IdentDistrib.refl
    (measurable_stat.prodMk measurable_stat).aemeasurable

example (μ : Measure ℝ) (t : ℝ) :
    μ {ω | t ≤ stat ω - stat ω} = μ {ω | stat ω - stat ω ≤ -t} :=
  (isExchangeablePair_stat μ).measure_le_sub measurable_stat measurable_stat t

example (μ : Measure ℝ) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ |stat ω - stat ω|} = 2 * μ {ω | t ≤ stat ω - stat ω} :=
  (isExchangeablePair_stat μ).measure_abs_sub measurable_stat measurable_stat ht

example (μ : Measure ℝ) (t : ℝ) :
    μ {ω | t ≤ xpehh (stat ω) (stat ω)} = μ {ω | xpehh (stat ω) (stat ω) ≤ -t} :=
  measure_le_xpehh (isExchangeablePair_stat μ) measurable_stat measurable_stat t

example (μ : Measure ℝ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ stat ω / stat ω} = μ {ω | stat ω / stat ω ≤ c⁻¹} :=
  (isExchangeablePair_stat μ).measure_le_ratio measurable_stat measurable_stat stat_pos stat_pos hc

/-! ### Without exchangeability the two tails differ

Under a point mass, the constant statistics `1` and `2` give `X - Y = -1`: the upper tail at
`0` is empty and the lower tail at `0` is everything. -/

example : (Measure.dirac (0 : ℝ)) {_ω : ℝ | (0 : ℝ) ≤ (1 : ℝ) - 2} = 0 := by
  norm_num

example : (Measure.dirac (0 : ℝ)) {_ω : ℝ | (1 : ℝ) - 2 ≤ -0} = 1 := by
  norm_num

/-! ### XP-EHH of two star-genealogy sweeps -/

/-- Two populations whose swept haplotypes have star ages `1` and `2`. -/
example : xpehh (ihh 1 1) (ihh 1 2) = log 2 := by
  rw [xpehh_ihh one_pos one_pos (by norm_num)]
  norm_num

#print axioms IsExchangeablePair.map_sub_neg
#print axioms IsExchangeablePair.measure_abs_sub
#print axioms measure_le_xpehh

end MathlibExtTest.Biology.PopulationGenetics.SelectionScan.CrossPopulationEHH
