/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILING A POLYGON WITH L- AND I-TROMINOES is NP-complete

Source:
T. Horiyama, T. Ito, K. Nakatsuka, A. Suzuki and R. Uehara, "Complexity of tiling a polygon
with trominoes or bars", Discrete and Computational Geometry 58(3) (2017), 686-704,
doi:10.1007/s00454-017-9884-9, Theorem 3 (LI-tiling).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.List.Perm.Basic
public import WantedExt.Complexity.NPComplete.RightTrominoTilingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LITrominoTiling

/-!
# TILING A POLYGON WITH L- AND I-TROMINOES is NP-complete

Horiyama, Ito, Nakatsuka, Suzuki and Uehara (2017), Section 1: "A polyomino is a rectilinear
polygon (i.e., a polygon made by connecting unit squares along their edges.) Then, we study the
problem of tiling a rectilinear polygon with polyominoes, defined as follows: Given a
rectilinear polygon `P` and a set `S` of polyominoes, determine whether `P` can be covered
without any overlap using translated copies of polyominoes in `S`." The polygon may have holes
(Section 1.2). `L` is the set of the four L-trominoes and `I` the set of the two I-trominoes
(`1 × 3` and `3 × 1` bars); LI-tiling is the tiling problem with `S = L ∪ I`. Theorem 3: LI-tiling
is NP-complete.

INSTANCE: a rectilinear polygon `P` made of unit squares, possibly with holes.
QUESTION: can `P` be covered without overlap by translated copies of the four L-trominoes and
the two I-trominoes?

Representation. `P` is given by its unit cells `(x, y)`, a nonempty duplicate-free list; the
cells are connected along their edges, that is, the cell set induces a connected subgraph of
Mathlib's grid graph `hasse ℕ □ hasse ℕ` (cells adjacent when they share an edge). Coordinates
are natural numbers: tiling is invariant under translation and every such polygon translates
into the quadrant. An L-tromino is a `2 × 2` block without one corner cell
(`RightTrominoTiling.trominoCells`, its four choices of corner being the four L-trominoes); an
I-tromino is three consecutive cells of a row or of a column. A tiling is a list of placed
tiles whose cells, counted with multiplicity, are a permutation of the cells of `P`: every cell
of `P` is covered exactly once and nothing outside `P` is covered.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the unit cells `(x, y)` of the polygon. -/
abbrev LITrominoTilingInstance := List (ℕ × ℕ)

/-- The grid graph on the unit cells of the quadrant: cells sharing an edge are adjacent. -/
abbrev CellGraph : SimpleGraph (ℕ × ℕ) := SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ

/-- Well-formedness: the polygon has at least one cell, no cell is listed twice, and its cells
are connected along their edges. -/
def WellFormed (i : LITrominoTilingInstance) : Prop :=
  i ≠ [] ∧ i.Nodup ∧ (CellGraph.induce {x | x ∈ i}).Connected

/-- The three cells of the I-tromino at `p`: horizontal (`(x, y)`, `(x + 1, y)`, `(x + 2, y)`)
if `v = false`, vertical (`(x, y)`, `(x, y + 1)`, `(x, y + 2)`) if `v = true`. -/
def barCells (v : Bool) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if v then [(p.1, p.2), (p.1, p.2 + 1), (p.1, p.2 + 2)]
  else [(p.1, p.2), (p.1 + 1, p.2), (p.1 + 2, p.2)]

/-- The polygon is tiled by L- and I-trominoes: some placed L-trominoes (a rotation and a
`2 × 2` block position each) and placed I-trominoes (an orientation and a position each) cover
every cell of the polygon exactly once and nothing else. -/
def LITrominoTilingFeasible (i : LITrominoTilingInstance) : Prop :=
  ∃ ls : List (Fin 4 × (ℕ × ℕ)), ∃ bs : List (Bool × (ℕ × ℕ)),
    ((ls.flatMap fun t => RightTrominoTiling.trominoCells t.1 t.2) ++
      bs.flatMap fun t => barCells t.1 t.2).Perm i

open Classical in
/-- TILING A POLYGON WITH L- AND I-TROMINOES as a decision problem over bitstrings. -/
noncomputable def liTrominoTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LITrominoTilingInstance) x with
  | some i => decide (WellFormed i ∧ LITrominoTilingFeasible i)
  | none => false

/-- **TILING A POLYGON WITH L- AND I-TROMINOES is NP-complete.** Source: Horiyama, Ito,
Nakatsuka, Suzuki and Uehara (2017), Theorem 3. -/
public theorem_wanted liTrominoTiling_npComplete :
    liTrominoTilingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L liTrominoTilingDec

end MetaMathlibExt.Complexity.NPComplete.LITrominoTiling
