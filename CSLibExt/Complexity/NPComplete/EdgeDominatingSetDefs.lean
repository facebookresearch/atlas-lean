/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE DOMINATING SET: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EDGE DOMINATING SET; M.
Yannakakis and F. Gavril, "Edge dominating sets in graphs" (1980).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDominatingSet

/-- **EDGE DOMINATING SET instances.** An instance of EDGE DOMINATING SET is a triple
$(n, E, K)$ of a natural number $n$ (the vertex count), a finite list $E$ of ordered pairs of
natural numbers (the edge list) and a natural number $K$ (the bound). -/
abbrev EdgeDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- **Edge-list adjacency for EDGE DOMINATING SET.** For a list $E$ of ordered pairs of natural
numbers and natural numbers $u$ and $v$, the Boolean adjacency of $u$ and $v$ in $E$ is true
exactly when $(u, v)$ or $(v, u)$ occurs in $E$. -/
def Adj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v) || edges.contains (v, u)


/-- **Well-formed EDGE DOMINATING SET instances.** An instance with vertex count $n$, edge list
$E$ and bound $K$ is well formed when $E$ has no repeated entries and every pair $(a, b)$ in $E$
satisfies $a < n$, $b < n$ and $a \ne b$, and $(b, a)$ does not occur in $E$. Thus $E$ lists the
edges of a simple graph on the vertices $0, \dots, n - 1$, each once and in one orientation. -/
def WellFormed (i : EdgeDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible EDGE DOMINATING SET instances.** An instance with vertex count $n$, edge list $E$
and bound $K$ is feasible when some sublist $D$ of $E$ (its entries taken in order) has at most
$K$ entries and dominates every edge of $E$: for every $e \in E$ there is $d \in D$ such that one
of the two entries of $d$ equals one of the two entries of $e$. -/
def EdgeDominatingSetFeasible
    (i : EdgeDominatingSetInstance) : Prop :=
  ∃ D : List (ℕ × ℕ), D.Sublist i.2.1 ∧ D.length ≤ i.2.2 ∧
    ∀ e ∈ i.2.1, ∃ d ∈ D, d.1 = e.1 ∨ d.1 = e.2 ∨ d.2 = e.1 ∨ d.2 = e.2

open Classical in
/-- **The EDGE DOMINATING SET decision problem.** EDGE DOMINATING SET is the decision problem
that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding,
to an EDGE DOMINATING SET instance $(n, E, K)$ that is well formed and feasible, that is, some
sublist of $E$ with at most $K$ entries contains, for every edge of $E$, an edge sharing an
endpoint with it. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def edgeDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ EdgeDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgeDominatingSet
