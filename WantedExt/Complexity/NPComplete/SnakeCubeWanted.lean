/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SNAKE CUBE is NP-complete

Source:
Z. Abel, E. D. Demaine, M. L. Demaine, S. Eisenstat, J. Lynch and T. B. Schardl,
"Finding a Hamiltonian path in a cube with specified turns is hard", Journal of
Information Processing 21(3) (2013), 368-377, doi:10.2197/ipsjjip.21.368.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SnakeCube

/-!
# SNAKE CUBE is NP-complete

Abel, Demaine, Demaine, Eisenstat, Lynch and Schardl (2013), Section 2: "An (abstract) puzzle
of cubes is a sequence of Ss and Ts, representing straight cells and turn cells, respectively.
A configuration of a length-n abstract puzzle is a sequence of distinct cells `c₁, …, cₙ` and
faces `f₀, …, fₙ`, such that
* for each `1 ≤ i ≤ n`, `fᵢ₋₁` and `fᵢ` are distinct faces of cell `cᵢ`, and
* if the `i`th symbol in the puzzle is an S then `fᵢ₋₁` and `fᵢ` are opposite faces on cell
  `cᵢ`; if this symbol is a T, faces `fᵢ₋₁` and `fᵢ` are adjacent."
Cells are the unit cubes of the integer lattice, and co-located faces of adjacent cells are
identified. Section 1.1: the puzzle is a sequence of `N³` symbols, and the question is "whether
such a puzzle has a folded state in the shape of an `N × N × N` cube".

INSTANCE: a positive integer `N` (the cube's side length) and a sequence of `N³` symbols, each S
or T.
QUESTION: is there a configuration whose cells are exactly the cells of the `N × N × N` cube?

Representation. Symbols are `Bool`, `false` for S and `true` for T. A cell of the cube is its
coordinate vector `Fin 3 → Fin N`. A face of a cell is named by its outward normal
`(a, s) : Fin 3 × Bool`, the axis `a` and the sign `s` (`true` = positive). Two faces of one cell
are opposite when they have the same axis and different signs, and adjacent (share an edge) when
their axes differ. The configuration is listed from index `0` (the paper's `c₁`):
`e k` is the normal of face `f_k` on cell `c k` (the face the chain enters by) and `o k` the
normal of face `f_{k+1}` on cell `c k` (the face it leaves by). Face `f_{k+1}` is shared by
cells `c k` and `c (k+1)`, so `c (k+1)` is the neighbor of `c k` across normal `o k`, and on
`c (k+1)` the same face has the opposite normal: `e (k+1) = opp (o k)`. The S/T clause then
reads `e k = opp (o k)` for S and `(e k).1 ≠ (o k).1` for T; either way the two faces are
distinct. The first face `f₀` (`e 0`) and the last face `fₙ` (`o (n-1)`) are free, as in the
source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the side length `N` and the puzzle, a list of symbols, `false` for a straight
cube (S) and `true` for a turn cube (T). -/
abbrev SnakeCubeInstance := ℕ × List Bool

/-- A cell of the `N × N × N` cube, as its coordinate vector. -/
abbrev Cell (N : ℕ) := Fin 3 → Fin N

/-- The opposite face of a cell: same axis, other sign. -/
def opp (f : Fin 3 × Bool) : Fin 3 × Bool := (f.1, !f.2)

/-- `y` is the cell across the face of `x` with outward normal `f = (a, s)`: coordinate `a`
grows by one if `s = true` and shrinks by one if `s = false`; the other coordinates agree. -/
def Across {N : ℕ} (x : Cell N) (f : Fin 3 × Bool) (y : Cell N) : Prop :=
  (if f.2 then (y f.1 : ℕ) = x f.1 + 1 else (x f.1 : ℕ) = y f.1 + 1) ∧
    ∀ b, b ≠ f.1 → y b = x b

/-- Well-formedness: the side length `N` is positive and the puzzle has exactly `N³` symbols. -/
def WellFormed (i : SnakeCubeInstance) : Prop :=
  0 < i.1 ∧ i.2.length = i.1 ^ 3

/-- A folded state in the shape of the `N × N × N` cube: cells `c k`, pairwise distinct and
covering the cube (`c` is a bijection onto the cube's cells), with entry and exit faces `e k`,
`o k` such that consecutive cells share face `f_{k+1}`, and each cell is straight or turning
as its symbol says. -/
def SnakeCubeFeasible (i : SnakeCubeInstance) : Prop :=
  ∃ c : Fin (i.1 ^ 3) → Cell i.1, ∃ e o : Fin (i.1 ^ 3) → Fin 3 × Bool,
    Function.Bijective c ∧
    (∀ k : Fin (i.1 ^ 3), ∀ h : k.1 + 1 < i.1 ^ 3,
      Across (c k) (o k) (c ⟨k.1 + 1, h⟩) ∧ e ⟨k.1 + 1, h⟩ = opp (o k)) ∧
    ∀ k : Fin (i.1 ^ 3), if i.2.getD k.1 false then (e k).1 ≠ (o k).1 else e k = opp (o k)

open Classical in
/-- SNAKE CUBE as a decision problem over bitstrings. -/
noncomputable def snakeCubeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SnakeCubeInstance) x with
  | some i => decide (WellFormed i ∧ SnakeCubeFeasible i)
  | none => false

/-- **SNAKE CUBE is NP-complete.** Source: Abel, Demaine, Demaine, Eisenstat, Lynch and
Schardl (2013). -/
public theorem_wanted snakeCube_npComplete :
    snakeCubeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L snakeCubeDec

end MetaMathlibExt.Complexity.NPComplete.SnakeCube
