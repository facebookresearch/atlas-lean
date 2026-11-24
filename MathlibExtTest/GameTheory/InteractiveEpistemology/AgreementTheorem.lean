/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.InteractiveEpistemology.AgreementTheorem
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Tactic.FinCases

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

open MeasureTheory MathlibExt.GameTheory.InteractiveEpistemology

open Classical in
-- The real measure of a set on a finite space is the sum of the masses of its points.
private theorem measureReal_eq_sum_ite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) :
    μ.real S = ∑ x, if x ∈ S then μ.real {x} else 0 := by
  rw [← Finset.sum_filter, sum_measureReal_singleton]
  congr 1
  ext x
  simp

/-! Aumann's four-state example (Aumann 1976, p. 1237) with the uniform (counting) prior:
`𝒫₁ = {{0, 1}, {2, 3}}`, `𝒫₂ = {{0, 1, 2}, {3}}`, `A = {0, 3}`, true state `0`. -/

/-- Agent 1's partition. -/
def P₁ : Setoid (Fin 4) := Setoid.ker ![0, 0, 1, 1]

/-- Agent 2's partition. -/
def P₂ : Setoid (Fin 4) := Setoid.ker ![0, 0, 0, 1]

theorem P₁_iff {x y : Fin 4} : P₁ x y ↔ ![0, 0, 1, 1] x = ![0, 0, 1, 1] y := Setoid.ker_def

theorem P₂_iff {x y : Fin 4} : P₂ x y ↔ ![0, 0, 0, 1] x = ![0, 0, 0, 1] y := Setoid.ker_def

/-- Agent 1's posterior of `A = {0, 3}` at `0` is `1/2`. -/
example : posterior Measure.count P₁ {0, 3} 0 = 1 / 2 := by
  rw [posterior, measureReal_eq_sum_ite, measureReal_eq_sum_ite]
  simp only [Fin.sum_univ_four]
  simp [P₁_iff, measureReal_def]
  norm_num

/-- Agent 2's posterior of `A = {0, 3}` at `0` is `1/3`. -/
example : posterior Measure.count P₂ {0, 3} 0 = 1 / 3 := by
  rw [posterior, measureReal_eq_sum_ite, measureReal_eq_sum_ite]
  simp only [Fin.sum_univ_four]
  simp [P₂_iff, measureReal_def]
  norm_num

/-- So the posteriors differ; by `agreeing_to_disagree` they cannot be common knowledge (the meet
cell of `0` has positive mass). -/
example : ¬ cell (P₁ ⊔ P₂) 0 ⊆
    {ω | posterior Measure.count P₁ {0, 3} ω = 1 / 2 ∧
      posterior Measure.count P₂ {0, 3} ω = 1 / 3} := by
  intro h
  have hM : Measure.count.real (cell (P₁ ⊔ P₂) (0 : Fin 4)) ≠ 0 := by
    have h1 : Measure.count.real ({0} : Set (Fin 4)) ≤ Measure.count.real (cell (P₁ ⊔ P₂) 0) :=
      measureReal_mono (by simp)
    have h2 : Measure.count.real ({0} : Set (Fin 4)) = 1 := by simp
    linarith
  have := agreeing_to_disagree Measure.count P₁ P₂ {0, 3} 0 (1 / 2) (1 / 3) h hM
  norm_num at this

/-- The hypotheses of `agreeing_to_disagree` are jointly satisfiable: two uninformed agents
(trivial partition `⊤`) commonly know their posteriors. -/
example : (1 / 2 : ℝ) = 1 / 2 := by
  refine agreeing_to_disagree Measure.count ⊤ ⊤ ({0, 3} : Set (Fin 4)) 0 (1 / 2) (1 / 2)
    (fun ω _ => ?_) ?_
  · have hc : ∀ ω' : Fin 4, cell (⊤ : Setoid (Fin 4)) ω' = Set.univ := fun ω' => by
      ext x; simp [Setoid.top_def]
    simp only [Set.mem_ofPred_eq, posterior, hc, Set.inter_univ, and_self]
    rw [measureReal_eq_sum_ite, measureReal_eq_sum_ite]
    simp only [Fin.sum_univ_four]
    simp [measureReal_def]
    norm_num
  · have hc : cell ((⊤ : Setoid (Fin 4)) ⊔ ⊤) 0 = Set.univ := by
      ext x; simp [Setoid.top_def]
    rw [hc, measureReal_eq_sum_ite]
    simp only [Fin.sum_univ_four]
    simp [measureReal_def]
    norm_num

/-- The dialogue theorem applies to Aumann's example: after finitely many rounds of announcing
posteriors the two agents agree at every state. -/
example : ∃ T, ∀ ω : Fin 4, ∀ i j : Fin 2,
    posterior Measure.count (dialogue Measure.count {0, 3} ![P₁, P₂] T i) {0, 3} ω =
      posterior Measure.count (dialogue Measure.count {0, 3} ![P₁, P₂] T j) {0, 3} ω := by
  obtain ⟨T, -, hT⟩ := geanakoplos_polemarchakis Measure.count ({0, 3} : Set (Fin 4)) ![P₁, P₂]
  refine ⟨T, fun ω i j => hT ω ?_ i j⟩
  have h1 : Measure.count.real ({ω} : Set (Fin 4)) ≤
      Measure.count.real (cell (⨆ i, dialogue Measure.count {0, 3} ![P₁, P₂] T i) ω) :=
    measureReal_mono (by simp)
  have h2 : Measure.count.real ({ω} : Set (Fin 4)) = 1 := by simp
  linarith
