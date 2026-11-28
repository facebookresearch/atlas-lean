/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56] GRAPH GRUNDY NUMBERING;
J. van Leeuwen, "Having a Grundy-numbering is NP-complete", Report No. 207, Computer Science
Department, Pennsylvania State University (1976);
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, d_out ≤ 2, d_in ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphGrundyNumbering

/-- An instance: the vertex count `n` and the arc list `A` (pairs `(u, v)` for arcs `u → v`). -/
abbrev GraphGrundyNumberingInstance := ℕ × List (ℕ × ℕ)

/-- The digraph of the instance on `Fin n`: `u → v` is an arc iff `(u, v)` is in the arc
list. -/
def Graph (i : GraphGrundyNumberingInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the arc list has no repeated arcs, its endpoints are
vertices, and it has no loops. -/
def WellFormed (i : GraphGrundyNumberingInstance) : Prop :=
  i.2.Nodup ∧ ∀ a ∈ i.2, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2

/-- A Grundy numbering: for every vertex `v`, `f v` is the least natural number that is not
the value of `f` at an out-neighbor of `v`. -/
def GraphGrundyNumberingFeasible (i : GraphGrundyNumberingInstance) : Prop :=
  ∃ f : Fin i.1 → ℕ, ∀ v, IsLeast (f '' {u | (Graph i).Adj v u})ᶜ (f v)

open Classical in
/-- GRAPH GRUNDY NUMBERING as a decision problem over bitstrings. -/
noncomputable def graphGrundyNumberingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphGrundyNumberingInstance) x with
  | some i => decide (WellFormed i ∧ GraphGrundyNumberingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphGrundyNumbering
