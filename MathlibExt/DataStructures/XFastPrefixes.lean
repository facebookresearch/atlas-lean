/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

/-!
# X-fast trie prefixes

Stored prefixes of a set of bitstrings: every prefix of a
stored key is stored, and a full-length stored prefix
determines its key. Maintenance bounds are not included
here.
-/

@[expose] public section

/-- Stored prefixes for an x-fast trie (ALG-37 core).
Keys are bitstrings `Fin k → Bool`. The trie stores, for
every key in `S` and every level `l ≤ k`, the length-`l`
prefix of the key, represented by its values on the first
`l` coordinates. -/
def storedPrefix {k : ℕ} (S : Finset (Fin k → Bool)) (l : ℕ)
    (hl : l ≤ k) (p : Fin l → Bool) : Prop :=
  ∃ x ∈ S, ∀ i : Fin l, p i = x ⟨i.val, lt_of_lt_of_le i.isLt hl⟩

/-- Every prefix of a stored key is stored. -/
theorem storedPrefix_of_mem {k : ℕ} (S : Finset (Fin k → Bool))
    (x : Fin k → Bool) (hx : x ∈ S) (l : ℕ) (hl : l ≤ k) :
    storedPrefix S l hl (fun i : Fin l => x ⟨i.val, lt_of_lt_of_le i.isLt hl⟩) := by
  exact ⟨x, hx, fun i => rfl⟩

/-- A key whose full-length prefix is stored (with the
prefix equal to the key) is in the set: at level `k` the
prefix determines the key. -/
theorem mem_of_storedPrefix_full {k : ℕ} (S : Finset (Fin k → Bool))
    (x : Fin k → Bool)
    (h : storedPrefix S k (le_refl k) (fun i : Fin k => x i)) : x ∈ S := by
  obtain ⟨y, hyS, hy⟩ := h
  have hxy : x = y := by
    funext i
    have hi : (⟨i.val, lt_of_lt_of_le i.isLt (le_refl k)⟩ : Fin k) = i := Fin.ext rfl
    have h2 := hy i
    simp only at h2
    rw [hi] at h2
    exact h2
  rw [hxy]
  exact hyS

end
