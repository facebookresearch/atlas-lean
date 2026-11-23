/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NORINORI is NP-complete

Source:
M. Biro and C. Schmidt, "Computational complexity and bounds for Norinori and LITS", Proc. 33rd
European Workshop on Computational Geometry (EuroCG 2017), Malmö (2017), Theorem 1,
https://itn-web.it.liu.se/~chrsc91/papers/norinori-lits.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Norinori

/-!
# NORINORI is NP-complete

Biro and Schmidt (2017): Norinori is "played on an `m × n` square grid that has been partitioned
into connected polyomino regions"; "the solver places black squares in the polyominos such that
the final board satisfies the following two properties:
1. Each black square has exactly one black neighbor.
2. There are exactly 2 black squares in each polyomino region."
Theorem 1: "Determining if a Norinori board is solvable is NP-complete".

INSTANCE: an `m × n` grid partitioned into connected regions.
QUESTION: can squares be made black so that every black square has exactly one black neighbor
and every region has exactly two black squares?

Representation. The grid is given row by row, each square carrying the label of its region; a
region is the set of squares with one label, so the instance size is proportional to the area
plus the binary length of the labels. Squares are `Fin m × Fin n`, neighbors when adjacent in
Mathlib's grid graph `pathGraph m □ pathGraph n`; `WellFormed` requires every region to be
connected (`SimpleGraph.Preconnected` of the subgraph the grid graph induces on it). A choice of
black squares is a function `ℕ → ℕ → Bool` read on the grid.

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
abbrev NorinoriInstance := List (List ℕ)

/-- The number of rows `m`. -/
def rows (i : NorinoriInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : NorinoriInstance) : ℕ := (i.headD []).length

/-- The region label of square `x`. -/
def region (i : NorinoriInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- The grid graph on the squares: squares sharing a side are neighbors. -/
abbrev Grid (i : NorinoriInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Adjacency in the grid graph is decidable (via `SimpleGraph.boxProd_adj`). -/
instance (i : NorinoriInstance) : DecidableRel (Grid i).Adj := fun _ _ =>
  decidable_of_iff _ SimpleGraph.boxProd_adj.symm

/-- Well-formedness: at least one row and one column, rows of equal length, and every region
connected. -/
def WellFormed (i : NorinoriInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ k, ((Grid i).induce {x | region i x = k}).Preconnected

/-- Some choice `b` of black squares gives every black square exactly one black neighbor
(property 1) and every region exactly two black squares (property 2). -/
def NorinoriFeasible (i : NorinoriInstance) : Prop :=
  ∃ b : ℕ → ℕ → Bool,
    (∀ x : Fin (rows i) × Fin (cols i), b x.1 x.2 = true →
      (Finset.univ.filter fun y => (Grid i).Adj x y ∧ b y.1 y.2 = true).card = 1) ∧
    ∀ x : Fin (rows i) × Fin (cols i),
      (Finset.univ.filter fun y => region i y = region i x ∧ b y.1 y.2 = true).card = 2

open Classical in
/-- NORINORI as a decision problem over bitstrings. -/
noncomputable def norinoriDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NorinoriInstance) x with
  | some i => decide (WellFormed i ∧ NorinoriFeasible i)
  | none => false

/-- **NORINORI is NP-complete.** Source: Biro and Schmidt (2017), Theorem 1. -/
public theorem_wanted norinori_npComplete :
    norinoriDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L norinoriDec

end MetaMathlibExt.Complexity.NPComplete.Norinori
