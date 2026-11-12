/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Preference.OrdinalInvariance
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics

namespace MathlibExtTest.Economics.Preference.OrdinalInvariance

namespace PreferenceExamples

/-- Scores `1, 1, 0` on three alternatives: alternatives `0` and `1` tie at the top. -/
def tieUtility : Fin 3 → ℝ := ![1, 1, 0]

theorem utilityChoice_tieUtility : utilityChoice tieUtility Set.univ = {0, 1} := by
  ext x
  fin_cases x
  · simp only [utilityChoice, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro _
      left
      rfl
    · intro _
      refine ⟨Set.mem_univ _, ?_⟩
      intro y _
      fin_cases y <;> simp [tieUtility]
  · simp only [utilityChoice, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro _
      right
      rfl
    · intro _
      refine ⟨Set.mem_univ _, ?_⟩
      intro y _
      fin_cases y <;> simp [tieUtility]
  · simp only [utilityChoice, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨-, h⟩ := h
      have hmem := h 0 (Set.mem_univ 0)
      simp [tieUtility] at hmem
      norm_num at hmem
    · intro h
      rcases h with h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)

theorem utilityChoice_affine_tieUtility :
    utilityChoice ((fun t : ℝ => 2 * t + 1) ∘ tieUtility) Set.univ = {0, 1} := by
  have hf : StrictMono (fun t : ℝ => 2 * t + 1) := by
    intro a b h
    dsimp only
    linarith
  rw [utilityChoice_comp_strictMono tieUtility hf]
  exact utilityChoice_tieUtility

/-- A constant (not strictly increasing) transformation enlarges the choice set. -/
theorem utilityChoice_const_tieUtility :
    utilityChoice ((fun _ : ℝ => (0 : ℝ)) ∘ tieUtility) Set.univ ≠
      utilityChoice tieUtility Set.univ := by
  rw [utilityChoice_tieUtility]
  intro h
  have h2mem : (2 : Fin 3) ∈ utilityChoice ((fun _ : ℝ => (0 : ℝ)) ∘ tieUtility) Set.univ := by
    simp only [utilityChoice, Set.mem_ofPred_eq]
    refine ⟨Set.mem_univ _, ?_⟩
    intro y _
    simp only [Function.comp_apply]
    exact le_rfl
  rw [h] at h2mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2mem
  rcases h2mem with h2 | h2
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

end PreferenceExamples

end MathlibExtTest.Economics.Preference.OrdinalInvariance
