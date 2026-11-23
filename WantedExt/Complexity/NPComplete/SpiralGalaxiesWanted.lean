/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPIRAL GALAXIES (TENTAI SHOW) is NP-complete

Source:
E. Friedman, "Spiral Galaxies Puzzles are NP-complete", manuscript, Stetson University (2002),
https://erich-friedman.github.io/papers/spiral.pdf;
E. D. Demaine, M. Löffler and C. Schmidt, "Rectangular Spiral Galaxies are still hard",
Computational Geometry 110 (2023), 101949, doi:10.1016/j.comgeo.2022.101949 (Section 1.1 for
the definition below).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SpiralGalaxies

/-!
# SPIRAL GALAXIES (TENTAI SHOW) is NP-complete

A board is an `m × n` grid of unit squares (cells). A puzzle consists of a board and a set of
centres placed at cell centres, edge midpoints, or grid vertices. A solution is a partition of
the grid into polyominoes, called galaxies, such that each galaxy contains a single centre and is
`180°` rotationally symmetric about its centre (Demaine, Löffler and Schmidt, Section 1.1). The
question is whether the puzzle has a solution.

As in the puzzle's rules, a galaxy contains its centre in its interior: every cell whose closed
square contains the centre belongs to the centre's galaxy (one cell for a cell centre, two for
an edge midpoint, four for a grid vertex). Galaxies are therefore indexed by their centres, and
no other centre can lie in a galaxy, even on its boundary.

Coordinates are doubled so that all centres are lattice points: cell `(r, c)` (row `r < m`,
column `c < n`) is the closed square `[2r, 2r + 2] × [2c, 2c + 2]`, and a centre `(a, b)` with
`a ≤ 2m`, `b ≤ 2n` is the point at row coordinate `a / 2` and column coordinate `b / 2`. The
point reflection about `(a, b)` maps cell `(r, c)` to cell `(r', c')` with `r' + r + 1 = a` and
`c' + c + 1 = b`. The puzzle is given explicitly, as the `(2m + 1) × (2n + 1)` array of these
lattice points marking which carry a centre, so its size is proportional to the board's.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the puzzle drawn on the doubled lattice, `2m + 1` rows of `2n + 1` booleans;
entry `b` of row `a` is `true` when a centre sits at the point `(a, b)` (a cell centre when `a`
and `b` are both odd, an edge midpoint when exactly one is odd, a grid vertex when both are
even). -/
abbrev SpiralGalaxiesInstance := List (List Bool)

/-- The number `m` of rows of cells. -/
def rows (i : SpiralGalaxiesInstance) : ℕ := i.length / 2

/-- The number `n` of columns of cells. -/
def cols (i : SpiralGalaxiesInstance) : ℕ := (i.getD 0 []).length / 2

/-- The centres, as the doubled coordinates `(a, b)` of the marked lattice points, row by row. -/
def centres (i : SpiralGalaxiesInstance) : List (ℕ × ℕ) :=
  (List.range i.length).flatMap fun a =>
    ((List.range (i.getD 0 []).length).filter fun b => (i.getD a []).getD b false).map
      fun b => (a, b)

/-- Well-formedness: the array has `2m + 1 ≥ 3` rows, all of the same length `2n + 1 ≥ 3`, so the
board has `m ≥ 1` rows and `n ≥ 1` columns of cells. -/
def WellFormed (i : SpiralGalaxiesInstance) : Prop :=
  i.length % 2 = 1 ∧ 3 ≤ i.length ∧ (i.getD 0 []).length % 2 = 1 ∧ 3 ≤ (i.getD 0 []).length ∧
    ∀ row ∈ i, row.length = (i.getD 0 []).length

/-- `g` is a solution: it assigns every cell to a centre, and for each centre `j` the galaxy
`{p | g p = j}` contains every cell whose closed square contains the centre, is mapped onto
itself by the point reflection about the centre, and is a polyomino (connected in the grid
graph `pathGraph m □ pathGraph n`, whose edges join cells sharing a side). -/
def IsSolution (i : SpiralGalaxiesInstance)
    (g : Fin (rows i) × Fin (cols i) → Fin (centres i).length) : Prop :=
  ∀ j : Fin (centres i).length,
    (∀ p : Fin (rows i) × Fin (cols i),
        2 * (p.1 : ℕ) ≤ ((centres i).get j).1 → ((centres i).get j).1 ≤ 2 * (p.1 : ℕ) + 2 →
        2 * (p.2 : ℕ) ≤ ((centres i).get j).2 → ((centres i).get j).2 ≤ 2 * (p.2 : ℕ) + 2 →
          g p = j) ∧
    (∀ p : Fin (rows i) × Fin (cols i), g p = j →
        ∃ q : Fin (rows i) × Fin (cols i), g q = j ∧
          (q.1 : ℕ) + p.1 + 1 = ((centres i).get j).1 ∧
          (q.2 : ℕ) + p.2 + 1 = ((centres i).get j).2) ∧
    ((SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)).induce
        {p | g p = j}).Connected

/-- The puzzle has a solution. -/
def SpiralGalaxiesFeasible (i : SpiralGalaxiesInstance) : Prop :=
  ∃ g : Fin (rows i) × Fin (cols i) → Fin (centres i).length, IsSolution i g

open Classical in
/-- SPIRAL GALAXIES as a decision problem over bitstrings. -/
noncomputable def spiralGalaxiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SpiralGalaxiesInstance) x with
  | some i => decide (WellFormed i ∧ SpiralGalaxiesFeasible i)
  | none => false

/-- **SPIRAL GALAXIES (TENTAI SHOW) is NP-complete.** Source: Friedman (2002); Demaine, Löffler
and Schmidt (2023). -/
public theorem_wanted spiralGalaxies_npComplete :
    spiralGalaxiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L spiralGalaxiesDec

end MetaMathlibExt.Complexity.NPComplete.SpiralGalaxies
