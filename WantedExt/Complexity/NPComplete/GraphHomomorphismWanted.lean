/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH HOMOMORPHISM; P.
Hell and J. Nesetril, "On the complexity of H-coloring" (1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphism

/-!
# GRAPH HOMOMORPHISM is NP-complete

Two undirected graphs `G` and `H`. The question is whether there is a homomorphism `G → H`: a
map from the vertices of `G` to those of `H` sending every edge of `G` to an edge of `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Graph-homomorphism instances.** A graph-homomorphism instance is a quadruple $(n, E, m, F)$
where $n$ is a natural number (the number of source vertices), $E$ is a list of pairs of natural
numbers (the source edges), $m$ is a natural number (the number of target vertices) and $F$ is a
list of pairs of natural numbers (the target edges). -/
abbrev GraphHomomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)


/-- **Target graph of a graph-homomorphism instance.** The target graph of a graph-homomorphism
instance $(n, E, m, F)$ is the simple graph on $\{0, \dots, m - 1\}$ in which distinct vertices
$i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $F$. Pairs of $F$ with an endpoint
at least $m$ contribute no edge. -/
def GraphTarget (i : GraphHomomorphismInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2


/-- **Well-formed graph-homomorphism instances.** A graph-homomorphism instance $(n, E, m, F)$ is
well formed when $E$ has no repeated entries, every pair $(u, v)$ in $E$ satisfies $u < n$,
$v < n$, $u \ne v$ and $(v, u) \notin E$, $F$ has no repeated entries, and every pair $(u, v)$
in $F$ satisfies $u < m$, $v < m$, $u \ne v$ and $(v, u) \notin F$. -/
def WellFormed (i : GraphHomomorphismInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- **Feasible graph-homomorphism instances.** A graph-homomorphism instance $(n, E, m, F)$ is
feasible when there is a map $f : \{0, \dots, n - 1\} \to \{0, \dots, m - 1\}$ such that, for
every pair $(u, v)$ in $E$ with $u < n$ and $v < n$, the vertices $f(u)$ and $f(v)$ are adjacent
in the target graph of the instance, that is, $f(u) \ne f(v)$ and $(f(u), f(v))$ or
$(f(v), f(u))$ belongs to $F$. Pairs of $E$ with an endpoint at least $n$ impose no condition. -/
def GraphHomomorphismFeasible
    (i : GraphHomomorphismInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.2.1,
    ∀ e ∈ i.2.1, ∀ (h1 : e.1 < i.1) (h2 : e.2 < i.1),
      (GraphTarget i).Adj (f ⟨e.1, h1⟩) (f ⟨e.2, h2⟩)

open Classical in
/-- **GRAPH HOMOMORPHISM as a decision problem.** The decision problem GRAPH HOMOMORPHISM accepts
a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
graph-homomorphism instance $(n, E, m, F)$ that is well formed (neither $E$ nor $F$ has repeated
entries, every pair $(u, v)$ in $E$ has $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$, and
every pair $(u, v)$ in $F$ has $u < m$, $v < m$, $u \ne v$ and $(v, u) \notin F$) and for which
there is a map $f : \{0, \dots, n - 1\} \to \{0, \dots, m - 1\}$ such that, for every pair
$(u, v)$ in $E$, $f(u) \ne f(v)$ and $(f(u), f(v))$ or $(f(v), f(u))$ belongs to $F$. Bitstrings
that do not decode are rejected. -/
noncomputable def graphHomomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphHomomorphismInstance) x with
  | some i => decide (WellFormed i ∧ GraphHomomorphismFeasible i)
  | none => false

/-- **GRAPH HOMOMORPHISM is NP-complete.** The decision problem GRAPH HOMOMORPHISM belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), GRAPH HOMOMORPHISM; P. Hell and J. Nesetril, "On the
complexity of H-coloring" (1990). -/
public theorem_wanted graphHomomorphism_npComplete :
    graphHomomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphHomomorphismDec

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphism
