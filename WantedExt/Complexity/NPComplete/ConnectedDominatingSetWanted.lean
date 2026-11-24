/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), CONNECTED DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet

/-!
# CONNECTED DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some dominating set of at most `K`
vertices induces a connected subgraph: any two vertices of the set are joined by a path whose
vertices all lie in the set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of CONNECTED DOMINATING SET.** An instance of CONNECTED DOMINATING SET is a triple
$(n, E, K)$ of a natural number $n$ (the number of vertices), a list $E$ of pairs of natural
numbers (the edges) and a natural number $K$ (the bound). -/
abbrev ConnectedDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a CONNECTED DOMINATING SET instance.** For an instance $(n, E, K)$ of CONNECTED
DOMINATING SET, its graph is the simple graph on the vertex set $\{0, \dots, n - 1\}$ in which
distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def Graph (i : ConnectedDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed CONNECTED DOMINATING SET instances.** An instance $(n, E, K)$ of CONNECTED
DOMINATING SET is well formed when the list $E$ has no repeated entries and every pair $(u, v)$
in $E$ has $u < n$, $v < n$ and $u \ne v$, with the reversed pair $(v, u)$ not in $E$. -/
def WellFormed (i : ConnectedDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible CONNECTED DOMINATING SET instances.** An instance $(n, E, K)$ of CONNECTED
DOMINATING SET is feasible when there is a set $S$ of vertices of its graph $G$ with at most $K$
elements such that every vertex of $G$ lies in $S$ or is adjacent in $G$ to a vertex of $S$, and
the subgraph of $G$ induced by $S$ is connected (in particular, $S$ is nonempty). -/
def ConnectedDominatingSetFeasible
    (i : ConnectedDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    (∀ v : Fin i.1, v ∈ S ∨ ∃ u ∈ S, (Graph i).Adj u v) ∧
    ((Graph i).induce (↑S : Set (Fin i.1))).Connected

open Classical in
/-- **The decision problem CONNECTED DOMINATING SET.** CONNECTED DOMINATING SET accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to an instance of CONNECTED
DOMINATING SET that is well formed and feasible. Bitstrings that do not decode to an instance are
rejected. -/
noncomputable def connectedDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedDominatingSetFeasible i)
  | none => false

/-- **CONNECTED DOMINATING SET is NP-complete.** The decision problem CONNECTED DOMINATING SET
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), CONNECTED DOMINATING SET. -/
public theorem_wanted connectedDominatingSet_npComplete :
    connectedDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet
