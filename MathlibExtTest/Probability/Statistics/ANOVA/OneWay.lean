/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ANOVA.OneWay

/-!
# Tests for one-way analysis of variance

The two-group `F(1, n-2)` use case in variance-free form, the two-group chi-square laws,
concrete sums of squares, the single-group boundary `G - 1 = 0`, and an empty group
violating the nonemptiness hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.ANOVA.OneWay

/-- Use case: two groups give the observable statistic `SSB / (SSW / (n - 2)) ~ F(1, n - 2)`,
with no unknown variance in the statistic. -/
example {n : ℕ} (hn : 3 ≤ n) (grp : Fin n → Fin 2)
    (hne : ∀ g, ∃ i, grp i = g)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → Fin n → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal m0 v) μ) :
    HasLaw (fun ω => sumSqBetween grp (X ω) / (sumSqWithin grp (X ω) / ((n - 2 : ℕ) : ℝ)))
      (snedecorFMeasure 1 (n - 2)) μ := by
  have hG : 2 ≤ Fintype.card (Fin 2) := by simp
  have hι : Fintype.card (Fin 2) < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  have h := hasLaw_oneWay_ANOVA_F_varianceFree grp hne hG hι hv hX
  simp only [Fintype.card_fin, Nat.add_one_sub_one, Nat.cast_one, div_one] at h
  exact h

/-- Two groups: the between-group sum of squares is `χ²₁` after scaling by `v`. -/
example {n : ℕ} (grp : Fin n → Fin 2) (hne : ∀ g, ∃ i, grp i = g)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → Fin n → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal m0 v) μ) :
    HasLaw (fun ω => sumSqBetween grp (X ω) / (v : ℝ)) (chiSquareMeasure 1) μ := by
  have h := hasLaw_sumSqBetween_div grp hne (by simp) hv hX
  simpa using h

/-- Two groups: the within-group sum of squares is `χ²_{n-2}` after scaling by `v`. -/
example {n : ℕ} (hn : 3 ≤ n) (grp : Fin n → Fin 2) (hne : ∀ g, ∃ i, grp i = g)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → Fin n → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal m0 v) μ) :
    HasLaw (fun ω => sumSqWithin grp (X ω) / (v : ℝ)) (chiSquareMeasure (n - 2)) μ := by
  have h := hasLaw_sumSqWithin_div grp hne (by simp; omega) hv hX
  simpa using h

/-- Concrete data: groups `{1, 3}` and `{5, 7}` (means `2` and `6`, grand mean `4`) give
`SSB = 16`. -/
example : sumSqBetween (![0, 0, 1, 1] : Fin 4 → Fin 2) ![1, 3, 5, 7] = 16 := by
  simp only [sumSqBetween, groupMean, Finset.sum_filter, Finset.card_filter, Fin.sum_univ_four]
  norm_num

/-- Concrete data: the same groups give `SSW = 4`. -/
example : sumSqWithin (![0, 0, 1, 1] : Fin 4 → Fin 2) ![1, 3, 5, 7] = 4 := by
  simp only [sumSqWithin, groupMean, Finset.sum_filter, Finset.card_filter, Fin.sum_univ_four]
  norm_num

/-- Concrete data: the variance-free statistic of `hasLaw_oneWay_ANOVA_F_varianceFree` is
`(16 / 1) / (4 / 2) = 8`. -/
example :
    (sumSqBetween (![0, 0, 1, 1] : Fin 4 → Fin 2) ![1, 3, 5, 7] /
        ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ)) /
      (sumSqWithin (![0, 0, 1, 1] : Fin 4 → Fin 2) ![1, 3, 5, 7] /
        ((Fintype.card (Fin 4) - Fintype.card (Fin 2) : ℕ) : ℝ)) = 8 := by
  simp only [sumSqBetween, sumSqWithin, groupMean, Finset.sum_filter, Finset.card_filter,
    Fin.sum_univ_four, Fintype.card_fin]
  norm_num

/-- Degenerate boundary: a single group has zero between degrees of freedom. -/
example : Fintype.card (Fin 1) - 1 = 0 := by
  simp

/-- An empty group violates the nonemptiness hypothesis. -/
example {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G) (g : G)
    (hempty : ∀ i, grp i ≠ g) : ¬ ∀ g', ∃ i, grp i = g' := by
  intro h
  obtain ⟨i, hi⟩ := h g
  exact hempty i hi

end MathlibExtTest.Probability.Statistics.ANOVA.OneWay
