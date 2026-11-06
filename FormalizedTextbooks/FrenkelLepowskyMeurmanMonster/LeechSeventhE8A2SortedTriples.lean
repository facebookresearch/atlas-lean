/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SpanTriple

/-! Increasing three-root lists are intrinsically determined by their underlying root sets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Two increasing three-element lists with the same underlying root set agree exactly. -/
theorem leechSeventh_sorted_triple_unique (a b : Fin 3 → Fin 120)
    (ha : a 0 < a 1 ∧ a 1 < a 2) (hb : b 0 < b 1 ∧ b 1 < b 2)
    (h : ∀ r : Fin 120, (∃ j, a j = r) ↔ ∃ j, b j = r) : a = b := by
  have hlow (c : Fin 3 → Fin 120) (hc : c 0 < c 1 ∧ c 1 < c 2) (j : Fin 3) :
      c 0 ≤ c j := by
    fin_cases j
    · exact le_rfl
    · exact le_of_lt hc.1
    · exact le_of_lt (lt_trans hc.1 hc.2)
  have hhigh (c : Fin 3 → Fin 120) (hc : c 0 < c 1 ∧ c 1 < c 2) (j : Fin 3) :
      c j ≤ c 2 := by
    fin_cases j
    · exact le_of_lt (lt_trans hc.1 hc.2)
    · exact le_of_lt hc.2
    · exact le_rfl
  have hz : a 0 = b 0 := by
    obtain ⟨j,hj⟩ := (h (a 0)).mp ⟨0,rfl⟩
    obtain ⟨k,hk⟩ := (h (b 0)).mpr ⟨0,rfl⟩
    have h1:=hlow b hb j
    have h2:=hlow a ha k
    rw [hj] at h1
    rw [hk] at h2
    exact le_antisymm h2 h1
  have ht : a 2 = b 2 := by
    obtain ⟨j,hj⟩ := (h (a 2)).mp ⟨2,rfl⟩
    obtain ⟨k,hk⟩ := (h (b 2)).mpr ⟨2,rfl⟩
    have h1:=hhigh b hb j
    have h2:=hhigh a ha k
    rw [hj] at h1
    rw [hk] at h2
    exact le_antisymm h1 h2
  have hm : a 1 = b 1 := by
    obtain ⟨j,hj⟩ := (h (a 1)).mp ⟨1,rfl⟩
    fin_cases j
    · have h0 : b 0 = a 1 := hj
      omega
    · exact hj.symm
    · have h2 : b 2 = a 1 := hj
      omega
  funext j
  fin_cases j <;> first | exact hz | exact hm | exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
