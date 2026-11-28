/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HomologyLocalizationDefs

namespace MetaMathlibExt.Complexity.NPComplete.HomologyLocalization

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open scoped symmDiff

private theorem accepts_encoding (i : HomologyLocalizationInstance) :
    homologyLocalizationDec (bitEncode i) = true ↔
      WellFormed i ∧ HomologyLocalizationFeasible i := by
  simp [homologyLocalizationDec, bitDecode_bitEncode]

/-- The faces of the hollow triangle on `0, 1, 2`: the empty face, three vertices, three
edges. -/
private abbrev hollow : List (List ℕ) := [[], [0], [1], [2], [0, 1], [1, 2], [0, 2]]

/-- The filled triangle: the hollow triangle plus the face `{0, 1, 2}`. -/
private abbrev filled : List (List ℕ) := hollow ++ [[0, 1, 2]]

/-- The boundary cycle `01 + 12 + 02` of the triangle. -/
private abbrev boundary : List (List ℕ) := [[0, 1], [1, 2], [0, 2]]

/-- Every vertex lies on zero or two edges of the triangle boundary. -/
private theorem boundary_even (v : ℕ) :
    Even (((boundary.map List.toFinset).toFinset).filter (v ∈ ·)).card := by
  by_cases hv : v < 3
  · have : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · have h₀ : v ≠ 0 := by omega
    have h₁ : v ≠ 1 := by omega
    have h₂ : v ≠ 2 := by omega
    simp [Finset.filter_insert, Finset.filter_singleton, h₀, h₁, h₂]

private theorem wellFormed_of (faces : List (List ℕ)) (k : ℕ)
    (h₁ : ∀ f ∈ faces, f.Nodup) (h₂ : (faces.map List.toFinset).Nodup)
    (h₃ : ∀ σ ∈ complex (faces, boundary, k), ∀ τ ∈ σ.powerset, τ ∈ complex (faces, boundary, k))
    (h₄ : ∀ e ∈ cycle (faces, boundary, k), e ∈ complex (faces, boundary, k) ∧ e.card = 2) :
    WellFormed (faces, boundary, k) :=
  ⟨h₁, h₂, fun σ hσ τ hτ => h₃ σ hσ τ (Finset.mem_powerset.2 hτ),
    (by decide : (boundary.map List.toFinset).Nodup), h₄,
    boundary_even⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : homologyLocalizationDec [true] = false := by
  have h : bitDecode (α := HomologyLocalizationInstance) [true] = none := rfl
  simp [homologyLocalizationDec, h]

/-- In the filled triangle the boundary cycle bounds the face `{0, 1, 2}`, so it is homologous
to the empty cycle, which has `0` edges. -/
example :
    homologyLocalizationDec (bitEncode ((filled, boundary, 0) : HomologyLocalizationInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨wellFormed_of _ _ (by decide) (by decide) (by decide) (by decide), ∅, {{0, 1, 2}},
    by simp, by simp, by decide, ?_, by simp⟩
  unfold cycle
  decide

/-- In the hollow triangle there is no face to fill, so the boundary cycle is homologous only to
itself, and it has three edges, more than `2`. -/
example :
    homologyLocalizationDec (bitEncode ((hollow, boundary, 2) : HomologyLocalizationInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, z', T, -, -, hT, hbd, hk⟩ := (accepts_encoding _).1 hacc
  have hnotri : ∀ t ∈ complex ((hollow, boundary, 2) : HomologyLocalizationInstance),
      t.card ≠ 3 := by decide
  have hT0 : T = ∅ := Finset.eq_empty_of_forall_notMem fun t ht =>
    hnotri t (hT t ht).1 (hT t ht).2
  have hsub : cycle ((hollow, boundary, 2) : HomologyLocalizationInstance) ⊆ z' := by
    intro e he
    have hc : e ∈ complex ((hollow, boundary, 2) : HomologyLocalizationInstance) ∧
        e.card = 2 := by
      revert e
      decide
    have h := hbd e hc.1 hc.2
    simp only [hT0, Finset.filter_empty, Finset.card_empty, Nat.not_odd_zero, iff_false,
      Finset.mem_symmDiff, not_or, not_and, not_not] at h
    exact h.1 he
  have h3 : (cycle ((hollow, boundary, 2) : HomologyLocalizationInstance)).card = 3 := by decide
  have hk' : z'.card ≤ 2 := hk
  have := Finset.card_le_card hsub
  omega

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((hollow, boundary, 2) : HomologyLocalizationInstance) :=
  wellFormed_of _ _ (by decide) (by decide) (by decide) (by decide)

end MetaMathlibExt.Complexity.NPComplete.HomologyLocalization
