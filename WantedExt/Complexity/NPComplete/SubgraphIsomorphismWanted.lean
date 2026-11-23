/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SUBGRAPH ISOMORPHISM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism

/-!
# SUBGRAPH ISOMORPHISM is NP-complete

Two undirected graphs, pattern `H` and host `G`. The question is whether `H` is a (not
necessarily induced) subgraph of `G`: an injective map from the vertices of `H` to those of `G`
sending every edge of `H` to an edge of `G`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Subgraph-isomorphism instances.** A subgraph-isomorphism instance is a tuple
$(n, E_G, m, E_H)$ of a natural number $n$ (the number of host vertices), a list $E_G$ of pairs
of natural numbers (the host edges), a natural number $m$ (the number of pattern vertices) and a
list $E_H$ of pairs of natural numbers (the pattern edges). -/
abbrev SubgraphIsomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)


/-- **Host graph of a subgraph-isomorphism instance.** For a subgraph-isomorphism instance
$(n, E_G, m, E_H)$, the host graph is the graph of the edge list $E_G$ on $n$ vertices: the simple
graph on $\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j)$
or $(j, i)$ belongs to $E_G$. -/
def GraphHost (i : SubgraphIsomorphismInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed subgraph-isomorphism instances.** A subgraph-isomorphism instance
$(n, E_G, m, E_H)$ is well formed when the list $E_G$ has no repeated entries and every
$(u, v) \in E_G$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E_G$, and likewise the
list $E_H$ has no repeated entries and every $(u, v) \in E_H$ satisfies $u < m$, $v < m$,
$u \ne v$ and $(v, u) \notin E_H$. -/
def WellFormed (i : SubgraphIsomorphismInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- **Feasible subgraph-isomorphism instances.** A subgraph-isomorphism instance
$(n, E_G, m, E_H)$ is feasible when there is an injective map
$f : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ such that for every $(u, v) \in E_H$ with
$u < m$ and $v < m$, the vertices $f(u)$ and $f(v)$ are adjacent in the host graph of the
instance. -/
def SubgraphIsomorphismFeasible
    (i : SubgraphIsomorphismInstance) : Prop :=
  ∃ f : Fin i.2.2.1 → Fin i.1, Function.Injective f ∧
    ∀ e ∈ i.2.2.2, ∀ (h1 : e.1 < i.2.2.1) (h2 : e.2 < i.2.2.1),
      (GraphHost i).Adj (f ⟨e.1, h1⟩) (f ⟨e.2, h2⟩)

open Classical in
/-- **SUBGRAPH ISOMORPHISM as a decision problem.** The decision problem SUBGRAPH ISOMORPHISM
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of
subgraph-isomorphism instances, to an instance that is well formed and feasible. Bitstrings that
do not decode to an instance are rejected. -/
noncomputable def subgraphIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphIsomorphismFeasible i)
  | none => false

/-- **SUBGRAPH ISOMORPHISM is NP-complete.** The decision problem SUBGRAPH ISOMORPHISM belongs
to NP, and every decision problem $L$ in NP has a polynomial-time many-one reduction to
SUBGRAPH ISOMORPHISM.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), SUBGRAPH ISOMORPHISM. -/
public theorem_wanted subgraphIsomorphism_npComplete :
    subgraphIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subgraphIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
