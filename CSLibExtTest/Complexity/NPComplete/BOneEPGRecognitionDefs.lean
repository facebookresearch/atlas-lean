/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BOneEPGRecognitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.BOneEPGRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BkVPGRecognition (BkVPGInstance Graph IsGridPath GridAdj bends)

private theorem accepts_encoding (i : BkVPGInstance) :
    bOneEPGRecognitionDec (bitEncode i) = true ↔
      BkVPGRecognition.WellFormed i ∧ BOneEPGRecognitionFeasible i := by
  simp [bOneEPGRecognitionDec, bitDecode_bitEncode]

private theorem adj_iff (i : BkVPGInstance) (u v : Fin i.1) :
    (Graph i).Adj u v ↔ u ≠ v ∧ ((u.val, v.val) ∈ i.2 ∨ (v.val, u.val) ∈ i.2) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem sharesGridEdge_iff (P Q : List (ℕ × ℕ)) :
    SharesGridEdge P Q ↔ ∃ e ∈ P.zip P.tail, e ∈ Q.zip Q.tail ∨ (e.2, e.1) ∈ Q.zip Q.tail :=
  ⟨fun ⟨p, q, h₁, h₂⟩ => ⟨(p, q), h₁, h₂⟩, fun ⟨⟨p, q⟩, h₁, h₂⟩ => ⟨p, q, h₁, h₂⟩⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : bOneEPGRecognitionDec [true] = false := by
  have h : bitDecode (α := BkVPGInstance) [true] = none := rfl
  simp [bOneEPGRecognitionDec, h]

/-- The path `0 - 1 - 2`. -/
private abbrev path : BkVPGInstance := (3, [(0, 1), (1, 2)])

/-- Straight grid paths: `(0,0)-(1,0)` for `0`, `(0,0)-(1,0)-(2,0)` for `1`, `(1,0)-(2,0)`
for `2`. The paths of `0` and `2` meet in the point `(1, 0)` but share no grid edge. -/
private def rep (v : Fin 3) : List (ℕ × ℕ) :=
  [[(0, 0), (1, 0)], [(0, 0), (1, 0), (2, 0)], [(1, 0), (2, 0)]].getD v.val []

set_option synthInstance.maxSize 1024 in
private theorem rep_edges : ∀ u v : Fin 3, u ≠ v →
    ((u ≠ v ∧ ((u.val, v.val) ∈ path.2 ∨ (v.val, u.val) ∈ path.2)) ↔
      ∃ e ∈ (rep u).zip (rep u).tail,
        e ∈ (rep v).zip (rep v).tail ∨ (e.2, e.1) ∈ (rep v).zip (rep v).tail) := by
  decide

/-- The path `0 - 1 - 2` is an edge-intersection graph of straight grid paths. -/
example : bOneEPGRecognitionDec (bitEncode path) = true := by
  refine (accepts_encoding _).2 ⟨by unfold BkVPGRecognition.WellFormed; decide, rep,
    fun v => ⟨?_, ?_⟩, fun u v huv => ?_⟩
  · revert v
    simp [Fin.forall_fin_succ, rep, IsGridPath, GridAdj]
  · revert v
    simp [Fin.forall_fin_succ, rep, bends]
  · rw [adj_iff, sharesGridEdge_iff]
    exact rep_edges u v huv

/-- A self-loop is not a simple edge, so the input is rejected. -/
example : bOneEPGRecognitionDec (bitEncode ((2, [(0, 1), (1, 1)]) : BkVPGInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨hw, -⟩
  exact absurd hw (by unfold BkVPGRecognition.WellFormed; decide)

end MetaMathlibExt.Complexity.NPComplete.BOneEPGRecognition
