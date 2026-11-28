/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SnakeCubeDefs

namespace MetaMathlibExt.Complexity.NPComplete.SnakeCube

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SnakeCubeInstance) :
    snakeCubeDec (bitEncode i) = true ↔ WellFormed i ∧ SnakeCubeFeasible i := by
  simp [snakeCubeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : snakeCubeDec [true] = false := by
  have h : bitDecode (α := SnakeCubeInstance) [true] = none := rfl
  simp [snakeCubeDec, h]

/-- The binary reflected Gray code `000, 001, 011, 010, 110, 111, 101, 100`: bit `a` of entry `k`
is coordinate `a` of the `k`-th cell of a Hamiltonian path through the `2 × 2 × 2` cube. -/
private def gray : List ℕ := [0, 1, 3, 2, 6, 7, 5, 4]

private def cellOf (k : Fin (2 ^ 3)) : Cell 2 := fun a =>
  if (gray.getD k 0).testBit a then 1 else 0

/-- The exit face of cell `k`: the axis and direction of the next step (an arbitrary face across
the last axis for the last cell). -/
private def exitFace (k : Fin (2 ^ 3)) : Fin 3 × Bool :=
  [(0, true), (1, true), (0, false), (2, true), (0, true), (1, false), (0, false), (1, true)].getD
    k (0, true)

/-- The entry face of cell `k`: opposite to the previous exit face (a face across another axis
for the first cell). -/
private def entryFace (k : Fin (2 ^ 3)) : Fin 3 × Bool :=
  if h : k.1 = 0 then (1, false) else opp (exitFace ⟨k.1 - 1, by omega⟩)

/-- All eight cubes turning: the Gray-code path changes axis at every step, so it folds the
puzzle `TTTTTTTT` into the `2 × 2 × 2` cube. -/
example : snakeCubeDec (bitEncode ((2, List.replicate 8 true) : SnakeCubeInstance)) = true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, rfl⟩, cellOf, entryFace, exitFace, ?_, ?_, ?_⟩
  · decide
  · unfold Across
    decide
  · decide

/-- A straight cube in second position cannot be placed in the `2 × 2 × 2` cube: the first three
cubes would be three distinct cells in a line of length `2`. -/
example : snakeCubeDec
    (bitEncode ((2, [true, false, true, true, true, true, true, true]) : SnakeCubeInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, c, e, o, -, hstep, hsym⟩ := (accepts_encoding _).1 h
  have h01 : Across (c ⟨0, by decide⟩) (o ⟨0, by decide⟩) (c ⟨1, by decide⟩) :=
    (hstep ⟨0, by decide⟩ (by decide)).1
  have h12 : Across (c ⟨1, by decide⟩) (o ⟨1, by decide⟩) (c ⟨2, by decide⟩) :=
    (hstep ⟨1, by decide⟩ (by decide)).1
  have he1 : e ⟨1, by decide⟩ = opp (o ⟨0, by decide⟩) := (hstep ⟨0, by decide⟩ (by decide)).2
  have hs1 : e ⟨1, by decide⟩ = opp (o ⟨1, by decide⟩) := by
    have h := hsym ⟨1, by decide⟩
    simpa using h
  have hface : o ⟨1, by decide⟩ = o ⟨0, by decide⟩ := by
    have h := congrArg opp (hs1.symm.trans he1)
    simpa [opp] using h
  rw [hface] at h12
  unfold Across at h01 h12
  generalize o ⟨0, by decide⟩ = f at h01 h12
  obtain ⟨a, s⟩ := f
  have h0 := (c ⟨0, by decide⟩ a).isLt
  have h1 := (c ⟨1, by decide⟩ a).isLt
  have h2 := (c ⟨2, by decide⟩ a).isLt
  have h01a := h01.1
  have h12a := h12.1
  cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h01a h12a <;> omega

/-- A puzzle with `7` cubes cannot fill the `2 × 2 × 2` cube, so the instance is malformed. -/
example : snakeCubeDec (bitEncode ((2, List.replicate 7 true) : SnakeCubeInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SnakeCube
