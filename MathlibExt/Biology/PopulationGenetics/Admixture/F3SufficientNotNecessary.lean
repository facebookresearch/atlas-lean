/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
public import MathlibExt.Biology.PopulationGenetics.Admixture.F3TargetPositivity
import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

/-!
# Negative `f3` is sufficient, but not necessary, for admixture

Inside the drift-model class, a negative `f3(C; A, B)` forces the target `C`
to have a non-binary lineage weight when the source weights lie in `[0, 1]`.
The converse fails. In the three-population admixture model with mixture
proportion `α`, source drift lengths `a, b` and private drift `c`, the exact
value is `f3(C; A, B) = c - α (1 - α) (a + b)`. When
`c ≥ α (1 - α) (a + b)`, realized admixed and star-tree models have the same
`f2`, `f3` and `f4`, while the admixed model has `f3 ≥ 0`.

These are statements about the drift-model class. Sample-statistic
corrections, ascertainment conditioning and non-neutral dynamics are outside
their scope.

## Main results

* `FStatistics.DriftModel.exists_weight_ne_zero_ne_one_of_f3_neg`: the
  drift-model target contrapositive of target-only `f3` positivity.
* `FStatisticsCovariance.f3_admixWeight`: the exact masking formula.
* `FStatisticsCovariance.exists_admix_star_f3_nonneg`: realized admixed and
  star-tree models with identical f-statistics in the masked regime.

## References

* N. Patterson et al., *Ancient admixture in human history*, Genetics 192
  (2012), 1065–1093, Appendix B and Appendix C.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]

/-- Sufficiency of a negative `f3`, target form, in a general drift model: if
the source weights of `A` and `B` lie in `[0, 1]` and `f3 C A B < 0`, then the
target `C` itself has a lineage weight that is neither `0` nor `1` (so `C`
does not have the binary weights of an unadmixed population). The
admixture-graph form is `AdmixtureGraph.exists_weight_ne_zero_ne_one_of_f3_neg`;
this is the contrapositive of `DriftModel.f3_nonneg_of_binary_target`. Only the
sources' weights are assumed in `[0, 1]`; no range assumption on `C` is needed. -/
theorem DriftModel.exists_weight_ne_zero_ne_one_of_f3_neg (M : DriftModel μ E P) {C A B : P}
    (hA : ∀ e, 0 ≤ M.weight A e ∧ M.weight A e ≤ 1)
    (hB : ∀ e, 0 ≤ M.weight B e ∧ M.weight B e ≤ 1)
    (h : f3 μ M.freq C A B < 0) :
    ∃ e, M.weight C e ≠ 0 ∧ M.weight C e ≠ 1 := by
  by_contra hcon
  refine (M.f3_nonneg_of_binary_target C A B (fun e => ?_) hA hB).not_gt h
  by_cases h0 : M.weight C e = 0
  · exact Or.inl h0
  · exact Or.inr (by
      by_contra h1
      exact hcon ⟨e, h0, h1⟩)

end MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {μ' : Measure Ω'}

/-- The exact `f3` value in the three-population admixture model
(`admixWeight α`, lengths `![a, b, c]`): with `A = 0`, `B = 1`, `C = 2`,
`f3 C A B = c - α (1 - α) (a + b)`, the private drift `c` of `C` minus the
admixture term. In particular `f3 C A B ≥ 0` exactly when
`c ≥ α (1 - α) (a + b)`, for every value of `α`. -/
theorem f3_admixWeight {α a b c : ℝ} {M : DriftModel μ (Fin 3) (Fin 3)}
    (hw : M.weight = admixWeight α) (hl : M.len = ![a, b, c]) :
    f3 μ M.freq 2 0 1 = c - α * (1 - α) * (a + b) := by
  rw [M.f3_freq, hw, hl]
  simp [admixWeight, starWeight, Fin.sum_univ_three]
  ring

/-- Non-necessity of a negative `f3` for admixture, with realized models: for
every `0 < α < 1`, `a, b ≥ 0` and private drift `c ≥ α (1 - α) (a + b)` there
are drift models `M` (admixed: weights `admixWeight α`, lengths `![a, b, c]`,
not binary loadings) and `M'` (star tree: weights `starWeight`, lengths
`starLen α a b c`, binary loadings) on probability spaces, with
`f3(C;A,B) = c - α (1 - α) (a + b) ≥ 0` in `M` and identical `f2`, `f3` and
`f4` in the two models. So a nonnegative `f3` does not rule out admixture
inside the drift-model class, and no f-statistic distinguishes the admixed
model from the star tree. -/
theorem exists_admix_star_f3_nonneg {α a b c : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : α * (1 - α) * (a + b) ≤ c) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 3)) (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (_ : IsProbabilityMeasure μ') (M' : DriftModel μ' (Fin 3) (Fin 3)),
        M.weight = admixWeight α ∧ M.len = ![a, b, c] ∧ ¬ M.HasBinaryLoadings ∧
        f3 μ M.freq 2 0 1 = c - α * (1 - α) * (a + b) ∧ 0 ≤ f3 μ M.freq 2 0 1 ∧
        M'.weight = starWeight ∧ M'.len = starLen α a b c ∧ M'.HasBinaryLoadings ∧
        (∀ X Y, f2 μ M.freq X Y = f2 μ' M'.freq X Y) ∧
        (∀ C A B, f3 μ M.freq C A B = f3 μ' M'.freq C A B) ∧
        (∀ A B C D, f4 μ M.freq A B C D = f4 μ' M'.freq A B C D) := by
  have hc0 : 0 ≤ c :=
    le_trans (mul_nonneg (mul_nonneg hα0.le (by linarith)) (by linarith)) hc
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel (admixWeight α) ![a, b, c]
      (by
        intro e
        fin_cases e <;> simp [ha, hb, hc0])
  obtain ⟨Ω', hΩ', μ', hμ', M', hw', hl'⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel starWeight
      (starLen α a b c) (starLen_nonneg hα0.le hα1.le ha hb hc)
  have hf3 : f3 μ M.freq 2 0 1 = c - α * (1 - α) * (a + b) := f3_admixWeight hw hl
  refine ⟨Ω, hΩ, μ, hμ, M, Ω', hΩ', μ', hμ', M', hw, hl,
    not_hasBinaryLoadings_admix (ne_of_gt hα0) (ne_of_lt hα1) hw, hf3, by rw [hf3]; linarith,
    hw', hl', hasBinaryLoadings_star hw',
    fun X Y => (f2_star_eq_f2_admix hw' hl' hw hl X Y).symm, ?_,
    fun A B C D => (f4_star_eq_f4_admix hw' hl' hw hl A B C D).symm⟩
  intro C A B
  rw [f3_eq_f4, f3_eq_f4, (f4_star_eq_f4_admix hw' hl' hw hl C A C B).symm]

/-- For `0 ≤ α ≤ 1` and `a, b ≥ 0`, the matching star tree has nonnegative edge lengths exactly
when `f3 C A B ≥ 0` in the admixture model (`A = 0`, `B = 1`, `C = 2`). -/
theorem starLen_nonneg_iff_f3_nonneg {α a b c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) {M : DriftModel μ (Fin 3) (Fin 3)} (hw : M.weight = admixWeight α)
    (hl : M.len = ![a, b, c]) :
    (∀ e, 0 ≤ starLen α a b c e) ↔ 0 ≤ f3 μ M.freq 2 0 1 := by
  rw [f3_admixWeight hw hl]
  constructor
  · intro h
    simpa [starLen] using h 2
  · intro h
    exact starLen_nonneg hα0 hα1 ha hb (by linarith)

end MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
