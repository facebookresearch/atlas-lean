/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LITS is NP-complete

Source:
M. Biro and C. Schmidt, "Computational complexity and bounds for Norinori and LITS", Proc. 33rd
European Workshop on Computational Geometry (EuroCG 2017), Malmö (2017), Theorem 2,
https://itn-web.it.liu.se/~chrsc91/papers/norinori-lits.pdf;
puzzle rules: Nikoli Co., Ltd., "LITS", https://www.nikoli.co.jp/en/puzzles/lits/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Int.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LITS

/-!
# LITS is NP-complete

Biro and Schmidt (2017): LITS is "played on an `m × n` square grid that has been partitioned
into connected polyomino regions"; "the solver places black squares in the regions such that
the final board satisfies the following properties:
1. The black squares form a connected polyomino.
2. Each polyomino region contains a connected black tetromino.
3. No two congruent tetrominos are adjacent.
4. Black squares may not build `2 × 2` squares."
They prove that "the problem of solving Norinori and LITS boards is NP-complete". Nikoli's rules
fix the details: "Color four consecutive squares (tetrominoes) in each of the areas surrounded
by bold lines. Similarly shaped rotated or reversed tetrominoes cannot touch, except at corners.
The colored squares must form a connected network. Colored squares cannot form `2 × 2` or larger
squares."

INSTANCE: an `m × n` grid partitioned into connected regions.
QUESTION: can squares be made black so that the black squares are connected, each region holds
exactly four black squares forming a connected tetromino, no two tetrominoes of different
regions that are congruent (by a rotation or a reflection) share an edge, and no `2 × 2` square
is all black?

Representation. The grid is given row by row, each square carrying the label of its region; a
region is the set of squares with one label (`WellFormed` requires it to be connected), so the
instance size is proportional to the area plus the binary length of the labels. Squares are
`Fin m × Fin n`, adjacent when they share an edge in Mathlib's grid graph
`pathGraph m □ pathGraph n`; connectedness of a set of squares is `SimpleGraph.Connected` of
the subgraph the grid graph induces on it. A choice of black squares is a function
`ℕ → ℕ → Bool` read on the grid. For property 3, the tetromino of a region is the finset of its
black squares as points of `ℤ × ℤ`, and two finsets are congruent when one is the image of the
other under one of the eight symmetries of the square lattice (`isometries`: the rotations by
multiples of a right angle and the reflections) followed by a translation; the translation is
written as the one that sends some point `p` of the first finset to some point `q` of the
second.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the region label of each square, row by row. -/
abbrev LITSInstance := List (List ℕ)

/-- The number of rows `m`. -/
def rows (i : LITSInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : LITSInstance) : ℕ := (i.headD []).length

/-- The region label of square `x`. -/
def region (i : LITSInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ := (i.getD x.1 []).getD x.2 0

/-- The grid graph on the squares: squares sharing an edge are adjacent. -/
abbrev Grid (i : LITSInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The eight symmetries of the square lattice `ℤ × ℤ` fixing the origin: the four rotations by
multiples of a right angle and the four reflections. -/
def isometries : List (ℤ × ℤ → ℤ × ℤ) :=
  [fun p => (p.1, p.2), fun p => (-p.2, p.1), fun p => (-p.1, -p.2), fun p => (p.2, -p.1),
    fun p => (-p.1, p.2), fun p => (p.1, -p.2), fun p => (p.2, p.1), fun p => (-p.2, -p.1)]

/-- `B` is congruent to `A`: `B` is the image of `A` under a lattice symmetry `s` followed by
the translation that sends `s p` to `q`, for some `p ∈ A` and `q ∈ B`. -/
def Congruent (A B : Finset (ℤ × ℤ)) : Prop :=
  ∃ s ∈ isometries, ∃ p ∈ A, ∃ q ∈ B, B = A.image fun x => s x - s p + q

/-- The black squares (for the choice `b`) of the region labelled `k`, as points of
`ℤ × ℤ`. -/
def piece (i : LITSInstance) (b : ℕ → ℕ → Bool) (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.univ.filter fun y : Fin (rows i) × Fin (cols i) =>
      region i y = k ∧ b y.1 y.2 = true).image
    fun y => (((y.1 : ℕ) : ℤ), ((y.2 : ℕ) : ℤ))

/-- Well-formedness: at least one row and one column, rows of equal length, and every region
connected. -/
def WellFormed (i : LITSInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ k, ((Grid i).induce {x | region i x = k}).Preconnected

/-- Some choice `b` of black squares satisfies properties 1-4. -/
def LITSFeasible (i : LITSInstance) : Prop :=
  ∃ b : ℕ → ℕ → Bool,
    -- 1. the black squares are connected
    ((Grid i).induce {x | b x.1 x.2 = true}).Connected ∧
    -- 2. every region holds exactly four black squares, which are connected
    (∀ x : Fin (rows i) × Fin (cols i),
      (Finset.univ.filter fun y => region i y = region i x ∧ b y.1 y.2 = true).card = 4 ∧
      ((Grid i).induce {y | region i y = region i x ∧ b y.1 y.2 = true}).Connected) ∧
    -- 3. tetrominoes of different regions that share an edge are not congruent
    (∀ x y : Fin (rows i) × Fin (cols i), (Grid i).Adj x y → b x.1 x.2 = true →
      b y.1 y.2 = true → region i x ≠ region i y →
        ¬ Congruent (piece i b (region i x)) (piece i b (region i y))) ∧
    -- 4. no `2 × 2` square is all black
    ∀ r c, r + 1 < rows i → c + 1 < cols i →
      ¬ (b r c = true ∧ b r (c + 1) = true ∧ b (r + 1) c = true ∧ b (r + 1) (c + 1) = true)

open Classical in
/-- LITS as a decision problem over bitstrings. -/
noncomputable def litsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LITSInstance) x with
  | some i => decide (WellFormed i ∧ LITSFeasible i)
  | none => false

/-- **LITS is NP-complete.** Source: Biro and Schmidt (2017), Theorem 2. -/
public theorem_wanted lits_npComplete :
    litsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L litsDec

end MetaMathlibExt.Complexity.NPComplete.LITS
