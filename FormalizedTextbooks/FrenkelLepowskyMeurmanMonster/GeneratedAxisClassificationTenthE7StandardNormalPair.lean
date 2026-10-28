/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardFlagPermutation

/-! The entire actual flag group preserves both orientations of the original normal pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual pair component fixes the entire unordered normal pair in the standard octad. -/
theorem generatedTenth_e7_standard_flag_pair_map
    (p : generatedTenthE7StandardFlagPermutationGroup) :
    ({4, 5} : Finset (Fin 8)).map
      (generatedTenthE7OctadPointPermutationHom p.val).toEmbedding = {4, 5} := by
  have h := congrArg (fun z : generatedTenthE7OctadPairs × Fin 4096 => z.1.val) p.property
  exact h

/-- The whole genuine permutation either fixes both normal coordinates or interchanges them. -/
theorem generatedTenth_e7_standard_flag_normal_pair
    (p : generatedTenthE7StandardFlagPermutationGroup) :
    (p.val.val.val 4 = 4 ∧ p.val.val.val 5 = 5) ∨
      (p.val.val.val 4 = 5 ∧ p.val.val.val 5 = 4) := by
  have h := generatedTenth_e7_standard_flag_pair_map p
  have h4 : generatedTenthE7OctadPointPermutationHom p.val 4 ∈ ({4, 5} : Finset (Fin 8)) := by
    rw [← h]
    exact Finset.mem_map.mpr ⟨4, by decide, rfl⟩
  have h5 : generatedTenthE7OctadPointPermutationHom p.val 5 ∈ ({4, 5} : Finset (Fin 8)) := by
    rw [← h]
    exact Finset.mem_map.mpr ⟨5, by decide, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h4 h5
  have h4' : p.val.val.val 4 = 4 ∨ p.val.val.val 4 = 5 := by
    rcases h4 with h4 | h4
    · left
      exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h4)
    · right
      exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h4)
  have h5' : p.val.val.val 5 = 4 ∨ p.val.val.val 5 = 5 := by
    rcases h5 with h5 | h5
    · left
      exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h5)
    · right
      exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h5)
  rcases h4' with h4' | h4' <;> rcases h5' with h5' | h5'
  · have he := p.val.val.val.injective (h4'.trans h5'.symm)
    exact False.elim ((by decide : (4 : Fin 24) ≠ 5) he)
  · exact Or.inl ⟨h4', h5'⟩
  · exact Or.inr ⟨h4', h5'⟩
  · have he := p.val.val.val.injective (h4'.trans h5'.symm)
    exact False.elim ((by decide : (4 : Fin 24) ≠ 5) he)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
