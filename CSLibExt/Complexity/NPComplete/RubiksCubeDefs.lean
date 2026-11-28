/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RUBIK'S CUBE (n × n × n, Slice Turn Metric): definitions

Source:
E. D. Demaine, S. Eisenstat and M. Rudoy, "Solving the Rubik's Cube Optimally is NP-complete",
35th Symposium on Theoretical Aspects of Computer Science (STACS 2018), LIPIcs 96 (2018),
24:1-24:13, doi:10.4230/LIPIcs.STACS.2018.24, Problem 2 (the STM Rubik's Cube problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RubiksCube

/-- An instance `(n, faces, k)`: the side length `n`, the sticker colours, and the move budget
`k`. `faces` lists the six faces in the order `+x, -x, +y, -y, +z, -z`, so the face with normal
axis `a` and sign `s` is entry `2 a + (if s then 0 else 1)`; in it, `face[u][v]` is the colour
of the sticker whose cubie has coordinate `u` along axis `a + 1` and `v` along axis `a + 2`
(mod 3). -/
abbrev RubiksCubeInstance := ℕ × List (List (List ℕ)) × ℕ

/-- A configuration of the `n × n × n` cube: `C a s u v` is the colour of the sticker on the
face with outward normal along axis `a` with sign `s` (`true` for `+`), on the cubie with
coordinate `u` along axis `a + 1` and `v` along axis `a + 2` (mod 3). -/
abbrev Config (n : ℕ) := Fin 3 → Bool → Fin n → Fin n → ℕ

variable {n : ℕ}

/-- The cubie carrying the sticker `(a, s, u, v)`: coordinate `n - 1` (if `s`) or `0` (if not)
along axis `a`, `u` along axis `a + 1` and `v` along axis `a + 2`. -/
def stickerCubie (a : Fin 3) (s : Bool) (u v : Fin n) : Fin 3 → Fin n := fun c =>
  if c = a then ⟨if s then n - 1 else 0, by have := u.isLt; split <;> omega⟩
  else if c = a + 1 then u else v

/-- The quarter turn about axis `b` of a sticker, given by its normal and its face coordinates:
the cubie's coordinates `(p, q)` along `(b + 1, b + 2)` become `(n - 1 - q, p)` (centred:
`(-q, p)`), the coordinate along `b` is unchanged, and the normal turns the same way
(`+(b + 1)` to `+(b + 2)`, `+(b + 2)` to `-(b + 1)`). -/
def turnSticker (b : Fin 3) (x : Fin 3 × Bool × Fin n × Fin n) : Fin 3 × Bool × Fin n × Fin n :=
  let p := stickerCubie x.1 x.2.1 x.2.2.1 x.2.2.2
  let p' : Fin 3 → Fin n := fun c =>
    if c = b + 1 then (p (b + 2)).rev else if c = b + 2 then p (b + 1) else p c
  let d : Fin 3 × Bool :=
    if x.1 = b + 1 then (b + 2, x.2.1) else if x.1 = b + 2 then (b + 1, !x.2.1) else (x.1, x.2.1)
  (d.1, d.2, p' (d.1 + 1), p' (d.1 + 2))

/-- The move `(b, j, t)`: the slice of cubies with coordinate `j` along axis `b` turns by `t + 1`
quarter turns (pulling colours back along `turnSticker b`); stickers outside the slice keep
their colours. -/
def applyMove (m : Fin 3 × Fin n × Fin 3) (C : Config n) : Config n := fun a s u v =>
  if stickerCubie a s u v m.1 = m.2.1 then
    let x := (turnSticker m.1)^[(m.2.2 : ℕ) + 1] (a, s, u, v)
    C x.1 x.2.1 x.2.2.1 x.2.2.2
  else C a s u v

/-- The result of applying a sequence of moves, in order. -/
def applyMoves (moves : List (Fin 3 × Fin n × Fin 3)) (C : Config n) : Config n :=
  moves.foldl (fun C m => applyMove m C) C

/-- A configuration is solved when each of the six faces is monochromatic, in six pairwise
different colours. -/
def Solved (C : Config n) : Prop :=
  ∃ col : Fin 3 → Bool → ℕ, Function.Injective (fun d : Fin 3 × Bool => col d.1 d.2) ∧
    ∀ a s u v, C a s u v = col a s

/-- The canonical solved cube `C₀` (Section 2.4): `+x` orange, `-x` red, `+y` green, `-y`
yellow, `+z` white, `-z` blue, coded as colours `0, …, 5` in that order, i.e. the face with
normal axis `a` and sign `s` has colour `2 a + (if s then 0 else 1)`. -/
def solvedConfig (n : ℕ) : Config n := fun a s _ _ => 2 * (a : ℕ) + if s then 0 else 1

/-- The configuration described by an instance (missing entries read as colour `0`; they do
not occur in well-formed instances). -/
def config (i : RubiksCubeInstance) : Config i.1 := fun a s u v =>
  ((i.2.1.getD (2 * (a : ℕ) + if s then 0 else 1) []).getD u []).getD v 0

/-- Well-formedness: `n ≥ 1`, there are six faces, each an `n × n` array of colours below `6`,
and the colouring is a configuration of the cube: some sequence of moves turns the canonical
solved cube `C₀` into it. -/
def WellFormed (i : RubiksCubeInstance) : Prop :=
  1 ≤ i.1 ∧ i.2.1.length = 6 ∧
    (∀ face ∈ i.2.1, face.length = i.1 ∧ ∀ row ∈ face, row.length = i.1 ∧ ∀ c ∈ row, c < 6) ∧
    ∃ moves : List (Fin 3 × Fin i.1 × Fin 3), applyMoves moves (solvedConfig i.1) = config i

/-- The configuration can be solved in at most `k` moves: some sequence of at most `k` slice
turns, applied in order, leaves it solved. -/
def RubiksCubeFeasible (i : RubiksCubeInstance) : Prop :=
  ∃ moves : List (Fin 3 × Fin i.1 × Fin 3), moves.length ≤ i.2.2 ∧
    Solved (applyMoves moves (config i))

open Classical in
/-- RUBIK'S CUBE (n × n × n, Slice Turn Metric) as a decision problem over bitstrings. -/
noncomputable def rubiksCubeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RubiksCubeInstance) x with
  | some i => decide (WellFormed i ∧ RubiksCubeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RubiksCube
