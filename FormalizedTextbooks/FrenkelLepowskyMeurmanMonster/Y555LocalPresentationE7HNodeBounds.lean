/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact acyclicity and literal chronological ordering of the E7 transporter ancestor cone. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7HNodeData
public import Mathlib.Order.Fin.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- All 4413 actual ancestor instructions are checked, with final finite padding separated.
/-- Every ancestor instruction has strictly earlier references. -/
theorem y322E7HNodeAllowedBlock (block : Fin 5) (i : Fin 1024) :
    y322E7HNodeAllowedAt (block.val * 1024 + i.val) := by
  fin_cases block <;> revert i <;> decide +kernel

/-- Each actual ancestor instruction retains its checked earlier-reference bounds. -/
theorem y322E7HNodeRaw_allowed (i : Fin 4413) : (y322E7HNodeRaw i).Allowed i.val := by
  let block : Fin 5 := ⟨i.val / 1024, by omega⟩
  let offset : Fin 1024 := ⟨i.val % 1024, Nat.mod_lt _ (by decide)⟩
  have h := y322E7HNodeAllowedBlock block offset
  have he : block.val * 1024 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  rw [he] at h
  simpa only [y322E7HNodeAllowedAt, dite_eq_left i.isLt] using h

/-- The exact chronological ancestor-cone word program, now checked acyclic. -/
def y322E7HNodeProgram : Y322WordProgram 4413 :=
  y322RawWordProgram y322E7HNodeRaw y322E7HNodeRaw_allowed

/-- The bound-checked ancestor program retains every literal raw instruction exactly. -/
theorem y322E7HNodeProgram_raw (i : Fin 4413) :
    y322InstructionRaw (y322E7HNodeProgram i) = y322E7HNodeRaw i :=
  y322RawWordProgram_raw _ _ i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Successive literal chronological positions are checked; transitivity gives the full order.
/-- The ancestor table embeds strictly increasingly into the actual chronological word table. -/
theorem y322E7HNodeEmbedding_strictMono : StrictMono y322E7HNodeEmbedding := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
