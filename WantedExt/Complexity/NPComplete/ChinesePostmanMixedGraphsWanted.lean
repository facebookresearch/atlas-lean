/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND25] CHINESE POSTMAN FOR MIXED
GRAPHS;
C. H. Papadimitriou, "On the complexity of edge traversing", Journal of the ACM 23 (1976),
544-554, doi:10.1145/321958.321974.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphs

/-!
# CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete

Given a mixed graph `G = (V, A, E)`, where `A` is a set of directed edges and `E` a set of
undirected edges on `V`, a length `l(e) ∈ Z₀⁺` for each `e ∈ A ∪ E`, and a bound `B ∈ Z⁺`,
is there a cycle in `G` that includes each directed and undirected edge at least once,
traversing directed edges only in the specified direction, and that has total length no
more than `B`?

The vertices are `0, ..., n - 1`. A directed edge is a triple `(u, v, l)` (from `u` to `v`,
length `l`), an undirected edge a triple `(u, v, l)` (joining `u` and `v`); neither list has
loops or repeated edges. A cycle is a closed walk, given as a list of steps: `(true, j, _)`
traverses directed edge `j` from its tail to its head, `(false, j, true)` traverses
undirected edge `j = (u, v, l)` from `u` to `v`, and `(false, j, false)` from `v` to `u`.
Consecutive steps meet, the last step ends where the first begins, and edges may be
traversed several times; its length is the sum of the lengths of its steps.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, directed edges `(u, v, l)`, undirected edges `(u, v, l)`,
and the bound `B`. -/
abbrev ChinesePostmanMixedGraphsInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ

/-- A step of a walk: whether it uses a directed edge, the index of the edge, and (for an
undirected edge) whether it is traversed from its first to its second endpoint. -/
abbrev Step := Bool × ℕ × Bool

/-- The start and end vertex of a step. -/
def stepEnds (i : ChinesePostmanMixedGraphsInstance) (s : Step) : ℕ × ℕ :=
  if s.1 then ((i.2.1.getD s.2.1 (0, 0, 0)).1, (i.2.1.getD s.2.1 (0, 0, 0)).2.1)
  else if s.2.2 then ((i.2.2.1.getD s.2.1 (0, 0, 0)).1, (i.2.2.1.getD s.2.1 (0, 0, 0)).2.1)
  else ((i.2.2.1.getD s.2.1 (0, 0, 0)).2.1, (i.2.2.1.getD s.2.1 (0, 0, 0)).1)

/-- The length of the edge a step traverses. -/
def stepLength (i : ChinesePostmanMixedGraphsInstance) (s : Step) : ℕ :=
  if s.1 then (i.2.1.getD s.2.1 (0, 0, 0)).2.2 else (i.2.2.1.getD s.2.1 (0, 0, 0)).2.2

/-- Well-formedness of an instance: every directed edge joins two distinct vertices below `n`
and no directed edge is repeated; every undirected edge joins two distinct vertices below `n`
and none is repeated in either orientation; and `B` is positive. -/
def WellFormed (i : ChinesePostmanMixedGraphsInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1) ∧
    (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.2.1.map fun e => (e.1, e.2.1)) ∧
    (i.2.2.1.map fun e => (e.1, e.2.1)).Nodup ∧ 0 < i.2.2.2

/-- Some closed walk traverses every directed edge (in its direction) and every undirected
edge at least once and has total length at most `B`. -/
def ChinesePostmanMixedGraphsFeasible (i : ChinesePostmanMixedGraphsInstance) : Prop :=
  ∃ walk : List Step,
    (∀ s ∈ walk, s.2.1 < if s.1 then i.2.1.length else i.2.2.1.length) ∧
    walk.IsChain (fun s t => (stepEnds i s).2 = (stepEnds i t).1) ∧
    walk.getLast?.map (fun s => (stepEnds i s).2) = walk.head?.map (fun s => (stepEnds i s).1) ∧
    (∀ j < i.2.1.length, ∃ s ∈ walk, s.1 = true ∧ s.2.1 = j) ∧
    (∀ j < i.2.2.1.length, ∃ s ∈ walk, s.1 = false ∧ s.2.1 = j) ∧
    (walk.map (stepLength i)).sum ≤ i.2.2.2

open Classical in
/-- CHINESE POSTMAN FOR MIXED GRAPHS as a decision problem over bitstrings. -/
noncomputable def chinesePostmanMixedGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChinesePostmanMixedGraphsInstance) x with
  | some i => decide (WellFormed i ∧ ChinesePostmanMixedGraphsFeasible i)
  | none => false

/-- **CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete.** Source: Garey and Johnson
(1979), [ND25]; Papadimitriou (1976). -/
public theorem_wanted chinesePostmanMixedGraphs_npComplete :
    chinesePostmanMixedGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chinesePostmanMixedGraphsDec

end MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphs
