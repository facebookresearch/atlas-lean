/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.AllKSimplicialRecognitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.AllKSimplicialRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (k : ℕ) (i : AllKSimplicialRecognitionInstance) :
    allKSimplicialRecognitionDec k (bitEncode i) = true ↔
      WellFormed i ∧ AllKSimplicialRecognitionFeasible k i := by
  simp [allKSimplicialRecognitionDec, bitDecode_bitEncode]

private theorem adj_iff (i : AllKSimplicialRecognitionInstance) (u v : Fin i.1) :
    (Graph i).Adj u v ↔ u ≠ v ∧ ((u.val, v.val) ∈ i.2 ∨ (v.val, u.val) ∈ i.2) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- A lone continuation bit is a truncated instance encoding, for every `k`. -/
example (k : ℕ) : allKSimplicialRecognitionDec k [true] = false := by
  have h : bitDecode (α := AllKSimplicialRecognitionInstance) [true] = none := rfl
  simp [allKSimplicialRecognitionDec, h]

/-- The path `0 - 1 - 2`. -/
private abbrev path : AllKSimplicialRecognitionInstance := (3, [(0, 1), (1, 2)])

set_option synthInstance.maxSize 1024 in
private theorem path_labels : ∀ v a b : Fin 3,
    v ≠ a ∧ ((v.val, a.val) ∈ path.2 ∨ (a.val, v.val) ∈ path.2) →
    v ≠ b ∧ ((v.val, b.val) ∈ path.2 ∨ (b.val, v.val) ∈ path.2) → a ≠ b →
    ((if a.val = 0 then (0 : Fin 2) else 1) = if b.val = 0 then 0 else 1) →
    a ≠ b ∧ ((a.val, b.val) ∈ path.2 ∨ (b.val, a.val) ∈ path.2) := by
  decide

/-- In the path `0 - 1 - 2` every neighbourhood splits into two cliques: label `0` for vertex `0`
and label `1` for the others separates the non-adjacent neighbours `0` and `2` of `1`. -/
example : allKSimplicialRecognitionDec 2 (bitEncode path) = true := by
  refine (accepts_encoding 2 _).2 ⟨by unfold WellFormed; decide, ?_⟩
  intro v
  refine ⟨fun a => if (a.val : ℕ) = 0 then 0 else 1, ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab hc
  simp only [ne_eq, Subtype.mk.injEq] at hab hc
  exact (adj_iff _ _ _).2 (path_labels v a b ((adj_iff _ _ _).1 ha) ((adj_iff _ _ _).1 hb) hab hc)

/-- The neighbours `0` and `2` of vertex `1` are not adjacent, so the neighbourhood of `1` is not
a single clique and the path is not all-`1`-simplicial. -/
example : allKSimplicialRecognitionDec 1 (bitEncode path) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, h⟩
  obtain ⟨c, hc⟩ := h 1
  have h₀ : (Graph path).Adj 1 0 := (adj_iff _ _ _).2 (by decide)
  have h₂ : (Graph path).Adj 1 2 := (adj_iff _ _ _).2 (by decide)
  have := hc ⟨0, h₀⟩ ⟨2, h₂⟩ (by simp) (Subsingleton.elim _ _)
  have := ((adj_iff _ _ _).1 this).2
  simp at this

end MetaMathlibExt.Complexity.NPComplete.AllKSimplicialRecognition
