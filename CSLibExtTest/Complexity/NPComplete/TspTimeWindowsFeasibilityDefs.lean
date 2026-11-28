/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TspTimeWindowsFeasibilityDefs

namespace MetaMathlibExt.Complexity.NPComplete.TspTimeWindowsFeasibility

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TspTimeWindowsFeasibilityInstance) :
    tspTimeWindowsFeasibilityDec (bitEncode i) = true ↔
      WellFormed i ∧ TspTimeWindowsFeasible i := by
  simp [tspTimeWindowsFeasibilityDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : tspTimeWindowsFeasibilityDec [true] = false := by
  have h : bitDecode (α := TspTimeWindowsFeasibilityInstance) [true] = none := rfl
  simp [tspTimeWindowsFeasibilityDec, h]

/-- Three points on a line at unit spacing. -/
private abbrev line : List (List ℕ) := [[0, 1, 2], [1, 0, 1], [2, 1, 0]]

/-- With three vertices, the only tour from `0` to `2` is `0, 1, 2`. -/
private theorem path_eq (path : List ℕ) (hperm : path.Perm (List.range 3))
    (hhead : path.head? = some 0) (hlast : path.getLast? = some 2) : path = [0, 1, 2] := by
  have hlen := hperm.length_eq
  have hnodup := hperm.nodup_iff.2 List.nodup_range
  have hmem : ∀ x ∈ path, x < 3 := fun x hx => List.mem_range.1 (hperm.mem_iff.1 hx)
  match path, hlen with
  | [a, b, c], _ =>
    simp at hhead hlast hnodup hmem
    subst hhead hlast
    simp only [List.cons.injEq, true_and, and_true]
    omega

/-- Windows `[0, 0]`, `[1, 1]`, `[2, 2]` are met exactly by the tour `0, 1, 2`. -/
example :
    tspTimeWindowsFeasibilityDec
      (bitEncode ((line, [(0, 0), (1, 1), (2, 2)]) : TspTimeWindowsFeasibilityInstance)) =
        true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [0, 1, 2], ?_, rfl, rfl, id, ?_, ?_⟩
  · exact List.perm_of_nodup_nodup_toFinset_eq (by decide) List.nodup_range (by decide)
  · decide
  · decide

/-- Narrowing the window of vertex `1` to `[0, 0]` is infeasible: the tour must reach
vertex `1` from vertex `0`, which takes one time unit after time `0`. -/
example :
    tspTimeWindowsFeasibilityDec
      (bitEncode ((line, [(0, 0), (0, 0), (2, 2)]) : TspTimeWindowsFeasibilityInstance)) =
        false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, path, hperm, hhead, hlast, D, hwin, hstep⟩
  obtain rfl := path_eq path hperm hhead hlast
  have h01 := hstep (0, 1) (by simp)
  have h0 := hwin 0 (by decide)
  have h1 := hwin 1 (by decide)
  simp [earliest, latest, travelTime] at h01 h0 h1
  omega

/-- The rejected instance is well formed, so the rejection comes from the time windows. -/
example : WellFormed ((line, [(0, 0), (0, 0), (2, 2)]) : TspTimeWindowsFeasibilityInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.TspTimeWindowsFeasibility
