/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-CUT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM MULTI-CUT, citing N. Garg, V. V. Vazirani and M. Yannakakis, "Approximate
max-flow min-(multi)cut theorems and their applications", SIAM Journal on Computing 25(2)
(1996), 235-251, doi:10.1137/S0097539793243016;
E. Dahlhaus, D. S. Johnson, C. H. Papadimitriou, P. D. Seymour and M. Yannakakis, "The
complexity of multiterminal cuts", SIAM Journal on Computing 23(4) (1994), 864-894,
doi:10.1137/S0097539792225297 (MULTIWAY CUT, the special case in which `S` consists of all
pairs of `k` terminals, is NP-hard already for `k = 3`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiCut

/-!
# MULTI-CUT is NP-complete

INSTANCE: a graph `G = (V, E)`, a set `S ⊆ V × V` of source-terminal pairs, a weight function
`w : E → ℕ`, and a positive integer `K`.
QUESTION: is there a multi-cut, i.e. a set `E' ⊆ E` such that the removal of `E'` from `E`
disconnects `sᵢ` from `tᵢ` for every pair `(sᵢ, tᵢ) ∈ S`, of weight `∑_{e ∈ E'} w(e)` at most
`K`?

The graph is a weighted edge list `(u, v, w)` with at most one edge per unordered vertex pair,
so the list is a weighted simple graph and a sublist of it is a subset `E' ⊆ E`. Removal is
Mathlib's `SimpleGraph.deleteEdges` of the edge set of `E'`, and disconnection is the negation
of `SimpleGraph.Reachable` in the resulting graph. A
pair `(v, v)` can never be disconnected, so an instance containing one is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), weighted edge list `(u, v, w(e))`,
the list of source-terminal pairs `S`, and the bound `K`. -/
abbrev MultiCutInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The unweighted graph on `Fin n` of a list of weighted edges. -/
def Graph (i : MultiCutInstance) (T : List (ℕ × ℕ × ℕ)) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (T.map fun e => (e.1, e.2.1))

/-- Well-formedness of an instance: the edge list has no duplicates, no self-loops, endpoints
below `n`, and at most one edge per unordered vertex pair; every pair of `S` has both vertices
below `n`; and `K` is positive. -/
def WellFormed (i : MultiCutInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (∀ e1 ∈ i.2.1, ∀ e2 ∈ i.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1 ∧ p.2 < i.1) ∧ 0 < i.2.2.2

/-- A multi-cut of weight at most `K`: a sublist `E'` of the edges, of total weight at most `K`,
such that after deleting the edges of `E'` from `G` (`SimpleGraph.deleteEdges`) the terminal
of every pair of `S` is not reachable from its source. -/
def MultiCutFeasible (i : MultiCutInstance) : Prop :=
  ∃ C : List (ℕ × ℕ × ℕ), C.Sublist i.2.1 ∧ (C.map fun e => e.2.2).sum ≤ i.2.2.2 ∧
    ∀ p ∈ i.2.2.1, ∀ hs : p.1 < i.1, ∀ ht : p.2 < i.1,
      ¬ ((Graph i i.2.1).deleteEdges (Graph i C).edgeSet).Reachable ⟨p.1, hs⟩ ⟨p.2, ht⟩

open Classical in
/-- MULTI-CUT as a decision problem over bitstrings. -/
noncomputable def multiCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiCutInstance) x with
  | some i => decide (WellFormed i ∧ MultiCutFeasible i)
  | none => false

/-- **MULTI-CUT is NP-complete.** Source: Crescenzi and Kann, MINIMUM MULTI-CUT, citing Garg,
Vazirani and Yannakakis (1996); NP-hard already for MULTIWAY CUT with three terminals, Dahlhaus,
Johnson, Papadimitriou, Seymour and Yannakakis (1994). -/
public theorem_wanted multiCut_npComplete :
    multiCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiCutDec

end MetaMathlibExt.Complexity.NPComplete.MultiCut
