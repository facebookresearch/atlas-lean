/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EntryExitDefs

namespace MetaMathlibExt.Complexity.NPComplete.EntryExit

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : EntryExitInstance) :
    entryExitDec (bitEncode i) = true ↔ WellFormed i ∧ EntryExitFeasible i := by
  simp [entryExitDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : entryExitDec [true] = false := by
  have h : bitDecode (α := EntryExitInstance) [true] = none := rfl
  simp [entryExitDec, h]

/-- The 2 × 2 grid graph. -/
private abbrev G₂ : SimpleGraph (Fin 2 × Fin 2) :=
  SimpleGraph.pathGraph 2 □ SimpleGraph.pathGraph 2

private instance : DecidableRel G₂.Adj := fun x y =>
  decidable_of_iff ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2 ∨
      (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1 = y.1)
    (by simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj])

/-- The loop around the four cells of the 2 × 2 grid. -/
private def loop : G₂.Walk (0, 0) (0, 0) :=
  .cons (v := (0, 1)) (by decide) <| .cons (v := (1, 1)) (by decide) <|
    .cons (v := (1, 0)) (by decide) <| .cons (by decide) .nil

private theorem loop_isHamiltonianCycle : loop.IsHamiltonianCycle :=
  SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.2
    ⟨(SimpleGraph.Walk.isCycle_def _).2 ⟨⟨by decide⟩, by simp [loop], by decide⟩, by decide⟩

/-- Top row region `0`, bottom row region `1`: the loop enters and leaves each row once. -/
example : entryExitDec (bitEncode ((2, [[0, 0], [1, 1]]) : EntryExitInstance)) = true :=
  (accepts_encoding _).2 ⟨by unfold WellFormed; decide, (0, 0), loop, loop_isHamiltonianCycle,
    by decide⟩

/-- A single region: the grid is well formed and has a Hamiltonian cycle, but no step ever
enters the region from outside. -/
example : entryExitDec (bitEncode ((2, [[0, 0], [0, 0]]) : EntryExitInstance)) = false := by
  cases h : entryExitDec (bitEncode ((2, [[0, 0], [0, 0]]) : EntryExitInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, v, W, -, hW⟩ := (accepts_encoding _).1 h
    have hr : ∀ x : Cell ((2, [[0, 0], [0, 0]]) : EntryExitInstance),
        region ((2, [[0, 0], [0, 0]]) : EntryExitInstance) x = 0 := by decide
    have := (hW v).1
    simp [hr] at this

end MetaMathlibExt.Complexity.NPComplete.EntryExit
