/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FAULT DETECTION IN DIRECTED GRAPHS is NP-complete

Sources:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MS18] FAULT DETECTION IN DIRECTED GRAPHS,
p. 283, crediting T. Ibaraki, T. Kameda and S. Toida (transformation from X3C).

T. Ibaraki, T. Kameda and S. Toida, "NP-complete diagnosis problems on system graphs",
Transactions of the IECE of Japan E62 (1979), 81–88.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FaultDetectionDirectedGraphs

/-!
# FAULT DETECTION IN DIRECTED GRAPHS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)`, with `I ⊆ V` the vertices of in-degree `0` and
`O ⊆ V` the vertices of out-degree `0`, and a positive integer `K`.
QUESTION: is there a "test set" of size `K` or less that can detect every "single fault" in `G`,
i.e. a subset `T ⊆ I × O` with `|T| ≤ K` such that for every `v ∈ V` some pair `(u₁, u₂) ∈ T`
has `v` on a directed path from `u₁` to `u₂` in `G`?

`v` lies on a directed path from `u₁` to `u₂` exactly when `u₁` reaches `v` and `v` reaches
`u₂` (`Relation.ReflTransGen` of the arc relation): in an acyclic digraph every directed walk is
a directed path, so the two walks concatenate to a path through `v`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), arc list `(u, v)` (an arc from `u`
to `v`), and the bound `K`. -/
abbrev FaultDetectionDirectedGraphsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The digraph of the instance on `Fin n`. -/
def Graph (i : FaultDetectionDirectedGraphsInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are
vertices, the digraph is acyclic (no vertex reaches itself by a nonempty directed path), and
`K` is positive. -/
def WellFormed (i : FaultDetectionDirectedGraphsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧ 0 < i.2.2

/-- A test set `T ⊆ I × O` with `|T| ≤ K`: every pair starts at a vertex of in-degree `0` and
ends at a vertex of out-degree `0`, and every vertex lies on a directed path from the first to
the second vertex of some pair. -/
def FaultDetectionDirectedGraphsFeasible (i : FaultDetectionDirectedGraphsInstance) : Prop :=
  ∃ T : Finset (Fin i.1 × Fin i.1), T.card ≤ i.2.2 ∧
    (∀ p ∈ T, (∀ u, ¬ (Graph i).Adj u p.1) ∧ ∀ u, ¬ (Graph i).Adj p.2 u) ∧
    ∀ v, ∃ p ∈ T, Relation.ReflTransGen (Graph i).Adj p.1 v ∧
      Relation.ReflTransGen (Graph i).Adj v p.2

open Classical in
/-- FAULT DETECTION IN DIRECTED GRAPHS as a decision problem over bitstrings. -/
noncomputable def faultDetectionDirectedGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FaultDetectionDirectedGraphsInstance) x with
  | some i => decide (WellFormed i ∧ FaultDetectionDirectedGraphsFeasible i)
  | none => false

/-- **FAULT DETECTION IN DIRECTED GRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[MS18]; Ibaraki, Kameda and Toida (1977). -/
public theorem_wanted faultDetectionDirectedGraphs_npComplete :
    faultDetectionDirectedGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L faultDetectionDirectedGraphsDec

end MetaMathlibExt.Complexity.NPComplete.FaultDetectionDirectedGraphs
