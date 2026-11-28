/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NORINORI: definitions

Source:
M. Biro and C. Schmidt, "Computational complexity and bounds for Norinori and LITS", Proc. 33rd
European Workshop on Computational Geometry (EuroCG 2017), Malmö (2017), Theorem 1,
https://itn-web.it.liu.se/~chrsc91/papers/norinori-lits.pdf.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Norinori

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

end MetaMathlibExt.Complexity.NPComplete.Norinori
