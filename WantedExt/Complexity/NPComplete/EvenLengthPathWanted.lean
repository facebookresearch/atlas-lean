/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EVEN LENGTH PATH (directed) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3 (problem [3] EVEN LENGTH PATH);
A. S. LaPaugh and C. H. Papadimitriou, "The even-path problem for graphs and digraphs",
Networks 14 (1984), 507-513, doi:10.1002/net.3230140403.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Cslib.Foundations.Data.List.IsChainFromTo
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EvenLengthPath

/-!
# EVEN LENGTH PATH (directed) is NP-complete

INSTANCE: a directed graph `G = (V, A)` and specified vertices `s, t ∈ V`.
QUESTION: is there a simple path `P` from `s` to `t` in `G` which contains an even number of
arcs?

Johnson (1982), problem [3]: "EVEN LENGTH PATH. INSTANCE: Directed graph `G = (V, A)`, specified
vertices `s, t ∈ V`. QUESTION: Is there a simple path `P` from `s` to `t` in `G` which contains
an even number of arcs? Reference. LaPaugh and Papadimitriou. Transformation from DIRECTED
SUBGRAPH HOMEOMORPHISM." LaPaugh and Papadimitriou (1984), abstract: "We give a simple
linear-time algorithm for finding even-length simple paths between two specified nodes of a given
graph. We show that the same problem for directed graphs is NP-complete." Membership in NP: the
path is a certificate.

The vertices are `Fin n` and the arcs a list of ordered pairs (an entry `(u, v)` is the arc
`u → v`; no repeated entry, no loop), giving a Mathlib `Digraph`. A path from `s` to `t` is a
vertex list that is a `List.IsChainFromTo` chain of arcs from `s` to `t` (CSLib: nonempty,
starting at `s`, ending at `t`, each vertex joined to the next by an arc), as in
`LongestDirectedPathWanted`; it is simple when its vertices are distinct, and its number of arcs
is its number of vertices minus one. For `s = t` the one-vertex path has zero arcs, so such an
instance is a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the arc list (an entry `(u, v)` is the arc
`u → v`), and the vertices `s` and `t`. -/
abbrev EvenLengthPathInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The directed graph of the instance on `Fin n`: `u → v` is an arc when `(u, v)` is listed. -/
def Graph (i : EvenLengthPathInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list describes a directed graph on `Fin n` (no
repeated entry, no loop, endpoints in range), and `s, t ∈ V`. -/
def WellFormed (i : EvenLengthPathInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧ i.2.2.1 < i.1 ∧
    i.2.2.2 < i.1

/-- Some simple directed path from `s` to `t` has an even number of arcs: a chain of arcs `p`
from the vertex `s` to the vertex `t` with distinct vertices and an even number
`p.length - 1` of arcs. -/
def EvenLengthPathFeasible (i : EvenLengthPathInstance) : Prop :=
  ∃ s t : Fin i.1, (s : ℕ) = i.2.2.1 ∧ (t : ℕ) = i.2.2.2 ∧
    ∃ p : List (Fin i.1), p.IsChainFromTo (Graph i).Adj s t ∧ p.Nodup ∧ Even (p.length - 1)

open Classical in
/-- EVEN LENGTH PATH as a decision problem over bitstrings. -/
noncomputable def evenLengthPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EvenLengthPathInstance) x with
  | some i => decide (WellFormed i ∧ EvenLengthPathFeasible i)
  | none => false

/-- **EVEN LENGTH PATH (directed) is NP-complete.** Source: LaPaugh and Papadimitriou (1984);
Johnson (1982), problem [3]. -/
public theorem_wanted evenLengthPath_npComplete :
    evenLengthPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L evenLengthPathDec

end MetaMathlibExt.Complexity.NPComplete.EvenLengthPath
