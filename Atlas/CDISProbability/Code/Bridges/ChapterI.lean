/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# CDIS Probabilités I: bridge statements (V3 sample)

Faithful Lean versions of three statements of the Mines Paris course CDIS
(Boisgérault et al., CC BY-NC-SA 4.0), each proved from an existing Mathlib lemma.
Probabilities are real-valued (`P.real`), as in the course.

* id 5: elementary properties of a probability (items 1 to 5, including Poincaré's formula).
* id 24: the distribution function characterises the law.
* id 25: characterisation of distribution functions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace CDIS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- CDIS P.I, id 5, item 1: `P(A) ∈ [0,1]` and `P(Aᶜ) = 1 - P(A)`. -/
theorem prob_mem_Icc_and_compl {A : Set Ω} (hA : MeasurableSet A) :
    P.real A ∈ Icc (0 : ℝ) 1 ∧ P.real Aᶜ = 1 - P.real A :=
  ⟨⟨measureReal_nonneg, measureReal_le_one⟩, probReal_compl_eq_one_sub hA⟩

/-- CDIS P.I, id 5, item 2: monotonicity. -/
theorem prob_mono {A B : Set Ω} (hAB : A ⊆ B) : P.real A ≤ P.real B :=
  measureReal_mono hAB

/-- CDIS P.I, id 5, item 3: `P(A ∪ B) = P(A) + P(B) - P(A ∩ B)`. -/
theorem prob_union {A B : Set Ω} (hB : MeasurableSet B) :
    P.real (A ∪ B) = P.real A + P.real B - P.real (A ∩ B) := by
  have := measureReal_union_add_inter (μ := P) (s := A) hB
  linarith

omit [IsProbabilityMeasure P] in
/-- CDIS P.I, id 5, item 4 (Boole's inequality). -/
theorem prob_biUnion_le {ι : Type*} (s : Finset ι) (A : ι → Set Ω) :
    P.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P.real (A i) :=
  measureReal_biUnion_finset_le s A

/-- CDIS P.I, id 5, item 5 (Poincaré's formula, i.e. inclusion-exclusion). The course writes the
alternating sum by intersection size; here it is indexed by the nonempty subsets `u`. -/
theorem prob_biUnion_eq_sum_powerset {ι : Type*} (s : Finset ι) {A : ι → Set Ω}
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    P.real (⋃ i ∈ s, A i) =
      ∑ u ∈ s.powerset with u.Nonempty, (-1 : ℝ) ^ (u.card + 1) * P.real (⋂ i ∈ u, A i) :=
  measureReal_biUnion_eq_sum_powerset hA

/-- CDIS P.I, id 24: two real random variables with the same distribution function have the same
law. -/
theorem law_eq_of_cdf_eq {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : cdf (P.map X) = cdf (P.map Y)) : P.map X = P.map Y := by
  have := (Measure.isProbabilityMeasure_map_iff hX).2 ‹_›
  have := (Measure.isProbabilityMeasure_map_iff hY).2 ‹_›
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
