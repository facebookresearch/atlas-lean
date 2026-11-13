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

The two-group `F(1, n-2)` use case, the single-group boundary `G - 1 = 0`, and an empty group
violating the nonemptiness hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.ANOVA.OneWay

/-- Use case: two groups give `F(1, n-2)`. -/
example {n : ℕ} (hn : 3 ≤ n) (grp : Fin n → Fin 2)
    (hne : ∀ g, ∃ i, grp i = g)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → Fin n → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal m0 v) μ) :
    HasLaw (fun ω => (sumSqBetween grp (X ω) / (v : ℝ) / ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ)) /
        (sumSqWithin grp (X ω) / (v : ℝ) / ((Fintype.card (Fin n) - Fintype.card (Fin 2) : ℕ) : ℝ)))
      (snedecorFMeasure (Fintype.card (Fin 2) - 1) (Fintype.card (Fin n) - Fintype.card (Fin 2))) μ := by
  have hG : 2 ≤ Fintype.card (Fin 2) := by simp
  have hι : Fintype.card (Fin 2) < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  exact hasLaw_oneWay_ANOVA_F grp hne hG hι hv hX

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
