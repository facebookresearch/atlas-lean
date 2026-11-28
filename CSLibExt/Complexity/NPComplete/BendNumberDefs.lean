/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BEND NUMBER: definitions

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MINIMUM BEND NUMBER.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RectilinearPlanarityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BendNumber

/-- An instance: vertex count, edge list, bound `K` on the number of bends. -/
abbrev BendNumberInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: a simple edge list on the vertices `0, …, n - 1`, and
`0 < K`. -/
def WellFormed (i : BendNumberInstance) : Prop :=
  RectilinearPlanarity.WellFormed (i.1, i.2.1) ∧ 0 < i.2.2

/-- The path replacing the edge `(u, v)` when it is subdivided by the `k` new vertices
`o, …, o + k - 1`: the edges `(u, o), (o, o + 1), …, (o + k - 1, v)`, or `(u, v)` when
`k = 0`. -/
def chain (u v o k : ℕ) : List (ℕ × ℕ) :=
  (u :: (List.range k).map (o + ·)).zip ((List.range k).map (o + ·) ++ [v])

/-- The edge list of the subdivision of the instance's graph in which edge `j` gets `ks[j]` new
vertices, numbered consecutively from `n`. -/
def subdivisionEdges (i : BendNumberInstance) (ks : List ℕ) : List (ℕ × ℕ) :=
  (List.range i.2.1.length).flatMap fun j =>
    chain (i.2.1.getD j (0, 0)).1 (i.2.1.getD j (0, 0)).2 (i.1 + (ks.take j).sum) (ks.getD j 0)

/-- The graph has a planar orthogonal drawing with at most `K` bends: for some numbers of new
vertices per edge, of total at most `K`, the subdivision has a rectilinear planar drawing. -/
def BendNumberFeasible (i : BendNumberInstance) : Prop :=
  ∃ ks : List ℕ, ks.length = i.2.1.length ∧ ks.sum ≤ i.2.2 ∧
    RectilinearPlanarity.RectilinearPlanarityFeasible (i.1 + ks.sum, subdivisionEdges i ks)

open Classical in
/-- BEND NUMBER as a decision problem over bitstrings. -/
noncomputable def bendNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BendNumberInstance) x with
  | some i => decide (WellFormed i ∧ BendNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BendNumber
