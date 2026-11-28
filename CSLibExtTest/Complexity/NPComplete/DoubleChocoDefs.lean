/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DoubleChocoDefs

namespace MetaMathlibExt.Complexity.NPComplete.DoubleChoco

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.ChainedBlock (SameShape coords latticeSymm)

private theorem accepts_encoding (i : DoubleChocoInstance) :
    doubleChocoDec (bitEncode i) = true ↔ WellFormed i ∧ DoubleChocoFeasible i := by
  simp [doubleChocoDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : doubleChocoDec [true] = false := by
  have h : bitDecode (α := DoubleChocoInstance) [true] = none := rfl
  simp [doubleChocoDec, h]

private instance {m n : ℕ} :
    DecidableRel (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n).Adj := fun x y =>
  decidable_of_iff ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2 ∨
      (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1 = y.1)
    (by simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj])

/-- A nonempty set whose distinct members are pairwise adjacent induces a connected graph. -/
private theorem connected_induce {V : Type} (G : SimpleGraph V) (S : Set V) (a : V)
    (ha : a ∈ S) (h : ∀ x ∈ S, ∀ y ∈ S, x = y ∨ G.Adj x y) : (G.induce S).Connected := by
  have : Nonempty S := ⟨⟨a, ha⟩⟩
  refine ⟨fun u v => ?_⟩
  rcases h u.1 u.2 v.1 v.2 with e | hadj
  · rw [Subtype.ext e]
  · exact SimpleGraph.Adj.reachable (G := G.induce S) hadj

/-- One row: a white cell with the number `1`, then a gray cell. -/
private abbrev yesBoard : DoubleChocoInstance := [[(0, 1), (1, 0)]]

private abbrev c₀ : Fin (rows yesBoard) × Fin (cols yesBoard) :=
  (⟨0, by decide⟩, ⟨0, by decide⟩)

private abbrev c₁ : Fin (rows yesBoard) × Fin (cols yesBoard) :=
  (⟨0, by decide⟩, ⟨1, by decide⟩)

/-- The whole board is one block: its white half `{(0, 0)}` and gray half `{(0, 1)}` are
translates of each other, and the number `1` is the size of the white half. -/
example : doubleChocoDec (bitEncode yesBoard) = true := by
  have hW : {x | (fun _ => 0) x = 0 ∧ (cell yesBoard x).1 = 0} = {c₀} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, true_and]
    revert x
    decide
  have hG : {x | (fun _ => 0) x = 0 ∧ (cell yesBoard x).1 = 1} = {c₁} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, true_and]
    revert x
    decide
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ => 0, fun _ => ?_⟩
  show GoodBlock yesBoard (fun _ => 0) 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hW]
    exact connected_induce _ _ c₀ rfl fun x hx y hy => Or.inl (hx.trans hy.symm)
  · rw [hG]
    exact connected_induce _ _ c₁ rfl fun x hx y hy => Or.inl (hx.trans hy.symm)
  · exact connected_induce _ _ c₀ rfl fun x _ y _ => by revert x y; decide
  · rw [hW, hG]
    refine ⟨(false, false, false), (0, 1), ?_⟩
    simp [coords, latticeSymm]
  · intro x _ hx
    obtain rfl : x = c₀ := by revert x; decide
    rw [hW, Set.ncard_singleton]
    rfl

/-- One row of two white cells is well formed, but every block needs a nonempty, connected
gray half. -/
example : doubleChocoDec (bitEncode ([[(0, 0), (0, 0)]] : DoubleChocoInstance)) = false := by
  cases h : doubleChocoDec (bitEncode ([[(0, 0), (0, 0)]] : DoubleChocoInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, blk, hblk⟩ := (accepts_encoding _).1 h
    obtain ⟨-, hgray, -⟩ := hblk (⟨0, by decide⟩, ⟨0, by decide⟩)
    obtain ⟨⟨y, -, hy⟩⟩ := hgray.nonempty
    revert hy
    revert y
    decide

end MetaMathlibExt.Complexity.NPComplete.DoubleChoco
