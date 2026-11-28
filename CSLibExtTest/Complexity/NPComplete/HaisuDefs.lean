/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HaisuDefs

namespace MetaMathlibExt.Complexity.NPComplete.Haisu

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : HaisuInstance) :
    haisuDec (bitEncode i) = true ↔ WellFormed i ∧ HaisuFeasible i := by
  simp [haisuDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : haisuDec [true] = false := by
  have h : bitDecode (α := HaisuInstance) [true] = none := rfl
  simp [haisuDec, h]

/-- A row of three cells: the start (region `0`), a middle cell of region `2` with number `n`,
and the finish (region `1`). -/
private abbrev row (n : ℕ) : HaisuInstance := [[(0, 0, 1), (2, n, 0), (1, 0, 2)]]

private abbrev a (n : ℕ) : Fin (rows (row n)) × Fin (cols (row n)) :=
  (⟨0, by simp [rows]⟩, ⟨0, by simp [cols]⟩)
private abbrev b (n : ℕ) : Fin (rows (row n)) × Fin (cols (row n)) :=
  (⟨0, by simp [rows]⟩, ⟨1, by simp [cols]⟩)
private abbrev c (n : ℕ) : Fin (rows (row n)) × Fin (cols (row n)) :=
  (⟨0, by simp [rows]⟩, ⟨2, by simp [cols]⟩)

/-- The path from the start through the middle cell to the finish visits every cell once, and it
enters region `2` for the first time at the middle cell, which carries the number `1`. -/
example : haisuDec (bitEncode (row 1)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, a 1, c 1, by decide, by decide,
    .cons (v := b 1) (by decide) (.cons (by decide) .nil), ?_, ?_⟩
  · unfold SimpleGraph.Walk.IsHamiltonian
    decide
  · unfold Solves
    decide

/-- With the number `2` in the middle cell the instance is well formed, but every path from the
start reaches the middle cell on its first move, on its first visit to region `2`. -/
example : haisuDec (bitEncode (row 2)) = false := by
  have h : ¬ HaisuFeasible (row 2) := by
    rintro ⟨s, f, hs, hf, w, -, hsol⟩
    have start : ∀ x, (cell (row 2) x).2.2 = 1 → x = a 2 := by decide
    have finish : ∀ x, (cell (row 2) x).2.2 = 2 → x = c 2 := by decide
    have step : ∀ v, (Grid (row 2)).Adj (a 2) v → v = b 2 := by decide
    obtain rfl := start s hs
    obtain rfl := finish f hf
    cases w with
    | cons hadj p =>
      obtain rfl := step _ hadj
      have := hsol 1 (by simp) (by simp [SimpleGraph.Walk.getVert]; decide)
      simp [SimpleGraph.Walk.getVert, region, cell] at this
  simpa [haisuDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Haisu
