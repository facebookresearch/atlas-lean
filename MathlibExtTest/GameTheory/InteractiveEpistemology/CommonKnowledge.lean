/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.InteractiveEpistemology.CommonKnowledge
public import Mathlib.Tactic.FinCases

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

open MathlibExt.GameTheory.InteractiveEpistemology

/-! Aumann's four-state example (Aumann 1976, p. 1237): `𝒫₁ = {{a, b}, {c, d}}`,
`𝒫₂ = {{a, b, c}, {d}}`, with states `a, b, c, d = 0, 1, 2, 3`. -/

/-- Agent 1's partition `{{0, 1}, {2, 3}}`. -/
def aumannP₁ : Setoid (Fin 4) := Setoid.ker ![0, 0, 1, 1]

/-- Agent 2's partition `{{0, 1, 2}, {3}}`. -/
def aumannP₂ : Setoid (Fin 4) := Setoid.ker ![0, 0, 0, 1]

theorem aumannP₁_iff {x y : Fin 4} : aumannP₁ x y ↔ ![0, 0, 1, 1] x = ![0, 0, 1, 1] y :=
  Setoid.ker_def

theorem aumannP₂_iff {x y : Fin 4} : aumannP₂ x y ↔ ![0, 0, 0, 1] x = ![0, 0, 0, 1] y :=
  Setoid.ker_def

/-- Both agents know `{0, 1, 2}` at state `0`. -/
example : (0 : Fin 4) ∈ knows aumannP₁ {0, 1, 2} ∩ knows aumannP₂ {0, 1, 2} := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
  · simp only [mem_cell, aumannP₁_iff, aumannP₂_iff] at hx
    fin_cases x <;> simp_all

/-- But `{0, 1, 2}` is not common knowledge at `0`: the chain `3 ∼₁ 2 ∼₂ 0` puts `3` in the
cell of the meet. -/
example : ¬ IsCommonKnowledgeAt ![aumannP₁, aumannP₂] {0, 1, 2} 0 := by
  intro h
  have h32 : (⨆ i, ![aumannP₁, aumannP₂] i) 3 2 :=
    Setoid.le_def.mp (le_iSup _ (0 : Fin 2)) (show aumannP₁ 3 2 from aumannP₁_iff.mpr rfl)
  have h20 : (⨆ i, ![aumannP₁, aumannP₂] i) 2 0 :=
    Setoid.le_def.mp (le_iSup _ (1 : Fin 2)) (show aumannP₂ 2 0 from aumannP₂_iff.mpr rfl)
  have := h ((⨆ i, ![aumannP₁, aumannP₂] i).trans h32 h20)
  simp at this

/-- The failure is detected by a finite chain of knowledge: at `0` agent 2 does not know that
agent 1 knows `{0, 1, 2}`. -/
example : (0 : Fin 4) ∉ knowsChain ![aumannP₁, aumannP₂] [1, 0] {0, 1, 2} := by
  intro h
  have h2 : (2 : Fin 4) ∈ knows aumannP₁ {0, 1, 2} :=
    h (show aumannP₂ 2 0 from aumannP₂_iff.mpr rfl)
  have := h2 (show aumannP₁ 3 2 from aumannP₁_iff.mpr rfl)
  simp at this

/-- The whole space is common knowledge everywhere (non-vacuity of the definition). -/
example (ω : Fin 4) : IsCommonKnowledgeAt ![aumannP₁, aumannP₂] Set.univ ω :=
  Set.subset_univ _

/-- Cell sums: summing `f` over each cell of `𝒫₁` gives `0`, hence the total is `0`. -/
example : ∑ x : Fin 4, ![1, -1, 2, -2] x = (0 : ℝ) :=
  sum_eq_zero_of_forall_sum_cell_eq_zero aumannP₁ fun ω => by
    fin_cases ω <;>
    · simp [cellFinset, aumannP₁_iff, Finset.sum_filter, Fin.sum_univ_four]
