/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE COPY FILE ALLOCATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR6] MULTIPLE COPY FILE ALLOCATION
(p. 227; transformation from VERTEX COVER), credited there to [Van Sickle and Chandy, 1977],
"The complexity of computer network design problems", listed in the book's bibliography as an
unpublished manuscript.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation

/-!
# MULTIPLE COPY FILE ALLOCATION is NP-complete

INSTANCE: a graph `G = (V, E)`, for each `v ∈ V` a usage `u(v) ∈ ℤ⁺` and a storage cost
`s(v) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a subset `V' ⊆ V` such that, if for
each `v ∈ V` we let `d(v)` denote the number of edges in the shortest path in `G` from `v` to a
member of `V'`, we have `∑_{v ∈ V'} s(v) + ∑_{v ∈ V} d(v) · u(v) ≤ K`?

`d(v)` exists only when `v` can reach `V'`; a vertex that cannot (for instance, any vertex when
`V' = ∅`) has no such path, and the subset `V'` does not qualify. The statement assigns each
vertex `v` a copy `c(v) ∈ V'` reachable from `v` and charges `dist(v, c(v))` (Mathlib's
`SimpleGraph.dist`, the number of edges of a shortest walk); since every term is non-negative,
some assignment meets the bound exactly when the nearest copies do, so this is the source's
condition with `d(v)` the minimum of `dist(v, w)` over the members `w ∈ V'` that `v` can reach
(Mathlib's `dist` is `0` for an unreachable pair, so unreachable members are excluded). Numbers
use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the list of
`(u(v), s(v))` indexed by vertex, and the bound `K`. -/
abbrev MultipleCopyFileAllocationInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MultipleCopyFileAllocationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The usage `u(v)`. -/
def usage (i : MultipleCopyFileAllocationInstance) (v : Fin i.1) : ℕ :=
  (i.2.2.1.getD v (0, 0)).1

/-- The storage cost `s(v)`. -/
def storage (i : MultipleCopyFileAllocationInstance) (v : Fin i.1) : ℕ :=
  (i.2.2.1.getD v (0, 0)).2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one
`(u(v), s(v))` per vertex with both entries positive, and `0 < K`. -/
def WellFormed (i : MultipleCopyFileAllocationInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧ (∀ c ∈ i.2.2.1, 0 < c.1 ∧ 0 < c.2) ∧ 0 < i.2.2.2

/-- Some set `V'` of copies and an assignment of each vertex to a copy it can reach meet the
bound: `∑_{v ∈ V'} s(v) + ∑_v dist(v, c(v)) · u(v) ≤ K`. -/
def MultipleCopyFileAllocationFeasible (i : MultipleCopyFileAllocationInstance) : Prop :=
  ∃ V' : Finset (Fin i.1), ∃ c : Fin i.1 → Fin i.1,
    (∀ v, c v ∈ V' ∧ (Graph i).Reachable v (c v)) ∧
      ∑ v ∈ V', storage i v + ∑ v, (Graph i).dist v (c v) * usage i v ≤ i.2.2.2

open Classical in
/-- MULTIPLE COPY FILE ALLOCATION as a decision problem over bitstrings. -/
noncomputable def multipleCopyFileAllocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleCopyFileAllocationInstance) x with
  | some i => decide (WellFormed i ∧ MultipleCopyFileAllocationFeasible i)
  | none => false

/-- **MULTIPLE COPY FILE ALLOCATION is NP-complete.** Source: Garey and Johnson (1979), [SR6]
(Van Sickle and Chandy, 1977). -/
public theorem_wanted multipleCopyFileAllocation_npComplete :
    multipleCopyFileAllocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleCopyFileAllocationDec

end MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation
