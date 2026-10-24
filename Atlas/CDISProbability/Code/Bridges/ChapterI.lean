/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Code.Basic
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# CDIS Probabilités I: bridge statements

Faithful Lean versions of statements of the Mines Paris course CDIS
(Boisgérault et al., CC BY-NC-SA 4.0), each proved from existing Mathlib lemmas. Each theorem
states the whole course statement, so a statement with several items is one conjunction.
Probabilities are real-valued (`P.real`), as in the course.

* id 5: elementary properties of a probability (items 1 to 5, including Poincaré's formula).
* id 24: the distribution function characterises the law.
* id 25: characterisation of distribution functions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace CDIS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- CDIS P.I, id 5 (elementary properties of a probability), all five items: `P(A) ∈ [0,1]` and
`P(Aᶜ) = 1 - P(A)`; monotonicity; `P(A ∪ B) = P(A) + P(B) - P(A ∩ B)`; Boole's inequality; and
Poincaré's formula (inclusion-exclusion). The course writes the alternating sum by intersection
size; here it is indexed by the nonempty subsets `u`. -/
theorem prob_properties {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {ι : Type*} (s : Finset ι) {C : ι → Set Ω} (hC : ∀ i ∈ s, MeasurableSet (C i)) :
    (P.real A ∈ Icc (0 : ℝ) 1 ∧ P.real Aᶜ = 1 - P.real A) ∧
      (A ⊆ B → P.real A ≤ P.real B) ∧
      P.real (A ∪ B) = P.real A + P.real B - P.real (A ∩ B) ∧
      P.real (⋃ i ∈ s, C i) ≤ ∑ i ∈ s, P.real (C i) ∧
      P.real (⋃ i ∈ s, C i) =
        ∑ u ∈ s.powerset with u.Nonempty, (-1 : ℝ) ^ (u.card + 1) * P.real (⋂ i ∈ u, C i) := by
  refine ⟨⟨⟨measureReal_nonneg, measureReal_le_one⟩, probReal_compl_eq_one_sub hA⟩,
    fun h ↦ measureReal_mono h, ?_, measureReal_biUnion_finset_le s C,
    measureReal_biUnion_eq_sum_powerset hC⟩
  have := measureReal_union_add_inter (μ := P) (s := A) hB
  linarith

/-- CDIS P.I, id 24: two real random variables with the same distribution function have the same
law. -/
theorem law_eq_of_cdf_eq {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : cdf (P.map X) = cdf (P.map Y)) : P.map X = P.map Y := by
  have := isProbabilityMeasure_map hX
  have := isProbabilityMeasure_map hY
  exact Measure.eq_of_cdf _ _ h

/-- CDIS P.I, id 25: `F` is the distribution function of a unique probability on `ℝ` if and only
if it is nondecreasing, right-continuous, with limits `0` at `-∞` and `1` at `+∞`. -/
theorem existsUnique_cdf_iff (F : ℝ → ℝ) :
    (∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧ cdf μ = F) ↔
      Monotone F ∧ (∀ x, ContinuousWithinAt F (Ici x) x) ∧
        Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) := by
  constructor
  · rintro ⟨μ, ⟨hμ, rfl⟩, -⟩
    exact ⟨(cdf μ).mono, (cdf μ).right_continuous, tendsto_cdf_atBot μ, tendsto_cdf_atTop μ⟩
  · rintro ⟨hmono, hrc, hbot, htop⟩
    let f : StieltjesFunction ℝ := ⟨F, hmono, hrc⟩
    have hprob : IsProbabilityMeasure f.measure :=
      ⟨by simp [f, StieltjesFunction.measure_univ f hbot htop]⟩
    refine ⟨f.measure, ⟨hprob, ?_⟩, ?_⟩
    · exact congrArg (⇑) (cdf_measure_stieltjesFunction f hbot htop)
    · rintro ν ⟨hν, hνF⟩
      refine Measure.eq_of_cdf _ _ ?_
      ext x
      rw [hνF, cdf_measure_stieltjesFunction f hbot htop]

end CDIS
