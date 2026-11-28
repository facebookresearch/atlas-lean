/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL ORDER DIMENSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN7] PARTIAL ORDER
DIMENSION;
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM Journal on
Algebraic and Discrete Methods 3(3) (1982), 351-358, doi:10.1137/0603036.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialOrderDimension

/-- An instance: the adjacency matrix of the digraph (row `u`, column `v` is `true` when
`(u, v)` is an arc; vertices are `0, …, n - 1` for `n` rows), and the bound `K`. -/
abbrev PartialOrderDimensionInstance := List (List Bool) × ℕ

/-- The arc relation of the instance on `Fin n`, `n` the number of matrix rows. -/
def Arc (i : PartialOrderDimensionInstance) (u v : Fin i.1.length) : Prop :=
  (i.1.getD u []).getD v false = true

/-- Well-formedness of an instance: the matrix is `n × n`, the digraph is acyclic (no vertex
reaches itself by a nonempty directed path) and transitive, and `0 < K ≤ |V|²`. -/
def WellFormed (i : PartialOrderDimensionInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ v : Fin i.1.length, ¬ Relation.TransGen (Arc i) v v) ∧
    (∀ u v w : Fin i.1.length, Arc i u v → Arc i v w → Arc i u w) ∧
    0 < i.2 ∧ i.2 ≤ i.1.length ^ 2

/-- There are `k ≤ K` linear orderings of the vertices such that `(u, v)` is an arc if and
only if `u` precedes `v` in each of them. -/
def PartialOrderDimensionFeasible (i : PartialOrderDimensionInstance) : Prop :=
  ∃ k ≤ i.2, ∃ σ : Fin k → Equiv.Perm (Fin i.1.length),
    ∀ u v : Fin i.1.length, Arc i u v ↔ ∀ j : Fin k, σ j u < σ j v

open Classical in
/-- PARTIAL ORDER DIMENSION as a decision problem over bitstrings. -/
noncomputable def partialOrderDimensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartialOrderDimensionInstance) x with
  | some i => decide (WellFormed i ∧ PartialOrderDimensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialOrderDimension
