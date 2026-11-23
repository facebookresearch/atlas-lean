/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RUBIK'S SQUARE is NP-complete

Source:
E. D. Demaine, S. Eisenstat and M. Rudoy, "Solving the Rubik's Cube Optimally is NP-complete",
35th Symposium on Theoretical Aspects of Computer Science (STACS 2018), LIPIcs 96 (2018),
24:1-24:13, doi:10.4230/LIPIcs.STACS.2018.24, Problem 1 (the Rubik's Square problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RubiksSquare

/-!
# RUBIK'S SQUARE is NP-complete

The `n × n` Rubik's Square (the `n × n × 1` Rubik's Cube) is an `n × n` array of unit cubies;
every cubie face on the outside of the puzzle carries a sticker of one of six colours. A move
flips a single row or column of cubies through space by a rotation in the long direction
(Demaine, Eisenstat and Rudoy, Section 2.1): the half turn about the axis that lies in the plane
of the square and is perpendicular to the row or column, so that the cubie at `(x, y)` of a
flipped row moves to `(-x, y)` in coordinates centred at the origin (Section 2.3), turned upside
down. The puzzle is solved when each of its six faces is monochromatic in a different colour. Given a configuration and a number `k`, the question is
whether the configuration can be solved in `k` moves or fewer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(n, top, bottom, east, west, north, south, k)`: the side length `n`, the colours
(numbers below `6`) of the stickers, and the move budget `k`. Cubies are indexed by their column
`x` and row `y` in `Fin n`. `top[y][x]` and `bottom[y][x]` are the colours of the top (`+z`) and
bottom (`-z`) stickers of cubie `(x, y)`; `east[y]` is the `+x` side sticker of cubie
`(n - 1, y)`, `west[y]` the `-x` side sticker of cubie `(0, y)`, `north[x]` the `+y` side
sticker of cubie `(x, n - 1)` and `south[x]` the `-y` side sticker of cubie `(x, 0)`. -/
abbrev RubiksSquareInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × List ℕ × List ℕ × List ℕ × List ℕ × ℕ

/-- The sticker colours of an `n × n` Rubik's Square, with the conventions of
`RubiksSquareInstance`: `top x y` and `bottom x y` belong to cubie `(x, y)`, `east y` to cubie
`(n - 1, y)`, `west y` to cubie `(0, y)`, `north x` to cubie `(x, n - 1)` and `south x` to cubie
`(x, 0)`. -/
structure Config (n : ℕ) where
  /-- The top (`+z`) sticker of cubie `(x, y)`. -/
  top : Fin n → Fin n → ℕ
  /-- The bottom (`-z`) sticker of cubie `(x, y)`. -/
  bottom : Fin n → Fin n → ℕ
  /-- The `+x` side sticker of cubie `(n - 1, y)`. -/
  east : Fin n → ℕ
  /-- The `-x` side sticker of cubie `(0, y)`. -/
  west : Fin n → ℕ
  /-- The `+y` side sticker of cubie `(x, n - 1)`. -/
  north : Fin n → ℕ
  /-- The `-y` side sticker of cubie `(x, 0)`. -/
  south : Fin n → ℕ

variable {n : ℕ}

/-- Flipping row `y₀` (the cubies with `y = y₀`): the `180°` rotation of the row about the
`y`-axis. The cubie at `(x, y₀)` moves to `(n - 1 - x, y₀)` (`Fin.rev x`), its top and bottom
stickers exchange, the `-x` and `+x` side stickers of the row exchange ends, and a boundary row
carries its `±y` side stickers along in reversed order. -/
def flipRow (y₀ : Fin n) (C : Config n) : Config n where
  top x y := if y = y₀ then C.bottom x.rev y else C.top x y
  bottom x y := if y = y₀ then C.top x.rev y else C.bottom x y
  east y := if y = y₀ then C.west y else C.east y
  west y := if y = y₀ then C.east y else C.west y
  north x := if (y₀ : ℕ) + 1 = n then C.north x.rev else C.north x
  south x := if (y₀ : ℕ) = 0 then C.south x.rev else C.south x

/-- Flipping column `x₀` (the cubies with `x = x₀`): the `180°` rotation of the column about the
`x`-axis. The cubie at `(x₀, y)` moves to `(x₀, n - 1 - y)` (`Fin.rev y`), its top and bottom
stickers exchange, the `-y` and `+y` side stickers of the column exchange ends, and a boundary
column carries its `±x` side stickers along in reversed order. -/
def flipColumn (x₀ : Fin n) (C : Config n) : Config n where
  top x y := if x = x₀ then C.bottom x y.rev else C.top x y
  bottom x y := if x = x₀ then C.top x y.rev else C.bottom x y
  east y := if (x₀ : ℕ) + 1 = n then C.east y.rev else C.east y
  west y := if (x₀ : ℕ) = 0 then C.west y.rev else C.west y
  north x := if x = x₀ then C.south x else C.north x
  south x := if x = x₀ then C.north x else C.south x

/-- A move: `Sum.inl y` flips row `y`, `Sum.inr x` flips column `x`. -/
def applyMove : Fin n ⊕ Fin n → Config n → Config n
  | Sum.inl y, C => flipRow y C
  | Sum.inr x, C => flipColumn x C

/-- A configuration is solved when each of the six faces is monochromatic, in six pairwise
different colours. -/
def Solved (C : Config n) : Prop :=
  ∃ cT cB cE cW cN cS : ℕ, [cT, cB, cE, cW, cN, cS].Nodup ∧
    (∀ x y, C.top x y = cT) ∧ (∀ x y, C.bottom x y = cB) ∧
    (∀ y, C.east y = cE) ∧ (∀ y, C.west y = cW) ∧
    (∀ x, C.north x = cN) ∧ (∀ x, C.south x = cS)

/-- The configuration in which every face has a single colour: top `t`, bottom `b`, `+x` side
`e`, `-x` side `w`, `+y` side `no`, `-y` side `so`. -/
def monoConfig (n t b e w no so : ℕ) : Config n where
  top _ _ := t
  bottom _ _ := b
  east _ := e
  west _ := w
  north _ := no
  south _ := so

/-- Placements of the canonical solved puzzle `C₀` from which flips reach every rigid placement of
it. `C₀` follows Section 2.4 ("top face red, bottom face blue, and the other four faces green,
orange, yellow, and white in some fixed order") with colours `0, …, 5` on the top, bottom, `+x`,
`-x`, `+y`, `-y` faces. The list holds `C₀` and `C₀` after a quarter turn about the `z`-axis;
the flips supply the half turns of the whole puzzle about the `x`- and `y`-axes (flip every
column, every row). For `n = 1` the puzzle is a single cube, and the list also holds the four
placements with a side face of `C₀` on top (a quarter turn about the `x`- or the `y`-axis,
each also turned a quarter turn about the `z`-axis). -/
def solvedPlacements (n : ℕ) : List (Config n) :=
  [monoConfig n 0 1 2 3 4 5, monoConfig n 0 1 5 4 2 3] ++
    if n = 1 then
      [monoConfig n 4 5 2 3 1 0, monoConfig n 4 5 0 1 2 3,
        monoConfig n 3 2 0 1 4 5, monoConfig n 3 2 5 4 0 1]
    else []

/-- The configuration described by an instance. -/
def config (i : RubiksSquareInstance) : Config i.1 where
  top x y := (i.2.1.getD y []).getD x 0
  bottom x y := (i.2.2.1.getD y []).getD x 0
  east y := i.2.2.2.1.getD y 0
  west y := i.2.2.2.2.1.getD y 0
  north x := i.2.2.2.2.2.1.getD x 0
  south x := i.2.2.2.2.2.2.1.getD x 0

/-- Well-formedness: `n ≥ 1`, both face arrays are `n × n`, the four side lists have length
`n`, every sticker has one of the six colours `0, …, 5`, and the colouring is a configuration of
the puzzle: a sequence of moves turns some rigid placement of the solved puzzle
(`solvedPlacements n`) into it. (An assembled configuration that is not of this form can never
become monochromatic, so it would be a no-instance in any case.) -/
def WellFormed (i : RubiksSquareInstance) : Prop :=
  1 ≤ i.1 ∧
    i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1 ∧ ∀ c ∈ row, c < 6) ∧
    i.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.1, row.length = i.1 ∧ ∀ c ∈ row, c < 6) ∧
    i.2.2.2.1.length = i.1 ∧ (∀ c ∈ i.2.2.2.1, c < 6) ∧
    i.2.2.2.2.1.length = i.1 ∧ (∀ c ∈ i.2.2.2.2.1, c < 6) ∧
    i.2.2.2.2.2.1.length = i.1 ∧ (∀ c ∈ i.2.2.2.2.2.1, c < 6) ∧
    i.2.2.2.2.2.2.1.length = i.1 ∧ (∀ c ∈ i.2.2.2.2.2.2.1, c < 6) ∧
    ∃ C₀ ∈ solvedPlacements i.1, ∃ moves : List (Fin i.1 ⊕ Fin i.1),
      moves.foldl (fun C m => applyMove m C) C₀ = config i

/-- The configuration can be solved in at most `k` moves: some sequence of at most `k` row and
column flips, applied in order, leaves it solved. -/
def RubiksSquareFeasible (i : RubiksSquareInstance) : Prop :=
  ∃ moves : List (Fin i.1 ⊕ Fin i.1), moves.length ≤ i.2.2.2.2.2.2.2 ∧
    Solved (moves.foldl (fun C m => applyMove m C) (config i))

open Classical in
/-- RUBIK'S SQUARE as a decision problem over bitstrings. -/
noncomputable def rubiksSquareDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RubiksSquareInstance) x with
  | some i => decide (WellFormed i ∧ RubiksSquareFeasible i)
  | none => false

/-- **RUBIK'S SQUARE is NP-complete.** Source: Demaine, Eisenstat and Rudoy (2018), Problem 1. -/
public theorem_wanted rubiksSquare_npComplete :
    rubiksSquareDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rubiksSquareDec

end MetaMathlibExt.Complexity.NPComplete.RubiksSquare
