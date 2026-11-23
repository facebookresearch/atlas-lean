/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56] GRAPH GRUNDY NUMBERING;
J. van Leeuwen, "Having a Grundy-numbering is NP-complete", Report No. 207, Computer Science
Department, Pennsylvania State University (1976);
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, d_out ≤ 2, d_in ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphGrundyNumbering

/-!
# GRAPH GRUNDY NUMBERING is NP-complete

Given a directed graph `G = (V, A)`, is there a function `f : V → {0, 1, 2, …}` such that, for
each `v ∈ V`, `f(v)` is the least non-negative integer not contained in the set
`{f(u) : (v, u) ∈ A}`?

The digraph has vertices `Fin n` and is given by its arc list; it is finite, with no loops
and no multiple arcs (`WellFormed`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **GRAPH GRUNDY NUMBERING is NP-complete.** Source: Garey and Johnson (1979), [GT56];
van Leeuwen (1976); Fraenkel (1981). -/
public theorem_wanted graphGrundyNumbering_npComplete :
    graphGrundyNumberingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphGrundyNumberingDec

end MetaMathlibExt.Complexity.NPComplete.GraphGrundyNumbering
