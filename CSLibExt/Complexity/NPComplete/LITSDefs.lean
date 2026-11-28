/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LITS: definitions

Source:
M. Biro and C. Schmidt, "Computational complexity and bounds for Norinori and LITS", Proc. 33rd
European Workshop on Computational Geometry (EuroCG 2017), Malmö (2017), Theorem 2,
https://itn-web.it.liu.se/~chrsc91/papers/norinori-lits.pdf;
puzzle rules: Nikoli Co., Ltd., "LITS", https://www.nikoli.co.jp/en/puzzles/lits/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import CSLibExt.Complexity.NPComplete.ChainedBlockDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LITS

open MetaMathlibExt.Complexity.NPComplete.ChainedBlock (SameShape coords)

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
        ¬ SameShape (coords {z | region i z = region i x ∧ b z.1 z.2 = true})
          (coords {z | region i z = region i y ∧ b z.1 z.2 = true})) ∧
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

end MetaMathlibExt.Complexity.NPComplete.LITS
