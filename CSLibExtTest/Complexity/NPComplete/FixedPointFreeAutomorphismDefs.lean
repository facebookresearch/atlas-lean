/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FixedPointFreeAutomorphismDefs

namespace MetaMathlibExt.Complexity.NPComplete.FixedPointFreeAutomorphism

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem adj_iff (i : FixedPointFreeAutomorphismInstance) (a b : Fin i.1) :
    (Graph i).Adj a b ↔ a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ i.2 ∨ ((b : ℕ), (a : ℕ)) ∈ i.2) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The `4`-cycle `0 - 1 - 2 - 3 - 0`. -/
private abbrev cycle : FixedPointFreeAutomorphismInstance := (4, [(0, 1), (1, 2), (2, 3), (3, 0)])

/-- The path `0 - 1 - 2`: every automorphism fixes the middle vertex. -/
private abbrev path : FixedPointFreeAutomorphismInstance := (3, [(0, 1), (1, 2)])

/-- The half-turn `0 ↔ 2`, `1 ↔ 3` of the `4`-cycle is an automorphism. -/
private def rotation : Graph cycle ≃g Graph cycle where
  toEquiv := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
  map_rel_iff' := by
    intro a b
    rw [adj_iff, adj_iff]
    revert a b
    decide

/-- The decision problem accepts the `4`-cycle, with the half-turn as witness. -/
example : fixedPointFreeAutomorphismDec (bitEncode cycle) = true := by
  have hw : WellFormed cycle := by unfold WellFormed; decide
  have hf : FixedPointFreeAutomorphismFeasible cycle := ⟨rotation, by
    show ∀ v : Fin 4, (Equiv.swap 1 3) ((Equiv.swap 0 2) v) ≠ v
    decide⟩
  simp [fixedPointFreeAutomorphismDec, bitDecode_bitEncode, hw, hf]

/-- In the path, a vertex other than `1` has at most one neighbor. -/
private theorem path_aux : ∀ a b c : Fin 3, b ≠ 1 → a ≠ c →
    b ≠ a ∧ (((b : ℕ), (a : ℕ)) ∈ path.2 ∨ ((a : ℕ), (b : ℕ)) ∈ path.2) →
    b ≠ c ∧ (((b : ℕ), (c : ℕ)) ∈ path.2 ∨ ((c : ℕ), (b : ℕ)) ∈ path.2) → False := by
  decide

/-- The decision problem rejects the well-formed path: an automorphism `f` moving `1` sends it to
an endpoint, whose only neighbor `1` would be the image of both `0` and `2`. -/
example : WellFormed path ∧ fixedPointFreeAutomorphismDec (bitEncode path) = false := by
  have hf : ¬ FixedPointFreeAutomorphismFeasible path := by
    rintro ⟨f, hf⟩
    have h10 : (Graph path).Adj (f 1) (f 0) := f.map_adj_iff.2 ((adj_iff _ _ _).2 (by decide))
    have h12 : (Graph path).Adj (f 1) (f 2) := f.map_adj_iff.2 ((adj_iff _ _ _).2 (by decide))
    have hne : f 0 ≠ f 2 := fun h => absurd (f.injective h) (by decide)
    rw [adj_iff] at h10 h12
    exact path_aux _ _ _ (hf 1) hne h10 h12
  exact ⟨by unfold WellFormed; decide,
    by simp [fixedPointFreeAutomorphismDec, bitDecode_bitEncode, hf]⟩

/-- An edge listed in both orientations is malformed, although the swap of its endpoints is a
fixed-point-free automorphism. -/
example :
    FixedPointFreeAutomorphismFeasible ((2, [(0, 1), (1, 0)]) : FixedPointFreeAutomorphismInstance) ∧
      fixedPointFreeAutomorphismDec
        (bitEncode ((2, [(0, 1), (1, 0)]) : FixedPointFreeAutomorphismInstance)) = false := by
  have hw : ¬ WellFormed ((2, [(0, 1), (1, 0)]) : FixedPointFreeAutomorphismInstance) := by
    unfold WellFormed; decide
  refine ⟨⟨⟨Equiv.swap 0 1, ?_⟩, ?_⟩,
    by simp [fixedPointFreeAutomorphismDec, bitDecode_bitEncode, hw]⟩
  · intro a b
    rw [adj_iff, adj_iff]
    revert a b
    decide
  · show ∀ v : Fin 2, Equiv.swap 0 1 v ≠ v
    decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : fixedPointFreeAutomorphismDec [true] = false := by
  have h : bitDecode (α := FixedPointFreeAutomorphismInstance) [true] = none := rfl
  simp [fixedPointFreeAutomorphismDec, h]

end MetaMathlibExt.Complexity.NPComplete.FixedPointFreeAutomorphism
