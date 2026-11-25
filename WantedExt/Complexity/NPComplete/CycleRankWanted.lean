/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CYCLE RANK is NP-complete

Source:
H. Gruber, "Digraph complexity measures and applications in formal language theory",
Discrete Mathematics and Theoretical Computer Science 14(2) (2012), 189-204,
doi:10.46298/dmtcs.583, Definition 1 and Theorem 10;
L. C. Eggan, "Transition graphs and the star-height of regular events", Michigan Mathematical
Journal 10(4) (1963), 385-397, doi:10.1307/mmj/1028998975 (definition of cycle rank).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CycleRank

/-!
# CYCLE RANK is NP-complete

INSTANCE: a directed graph `G = (V, E)` and an integer `k ≥ 0`.
QUESTION: is the cycle rank `r(G)` of `G` at most `k`?

Cycle rank (Eggan, 1963; Gruber, Definition 1): if `G` is acyclic, then `r(G) = 0`; if `G` is
strongly connected and `E ≠ ∅`, then `r(G) = 1 + min_{v ∈ V} r(G - v)`; if `G` is not strongly
connected, then `r(G)` is the maximum cycle rank among the strongly connected components of `G`.
Here a strongly connected set `S` is nontrivial when the induced subdigraph `G[S]` has at least
one edge (a single vertex with a loop is nontrivial), and `G` is acyclic when all its strongly
connected components are trivial. Gruber (Theorem 10) proves that deciding `r(G) ≤ k` is
NP-complete, also for strongly connected digraphs.

The definition is unfolded into `RankLE G k S`, "`G[S]` has cycle rank at most `k`", by
recursion on `k`: `RankLE G 0 S` says that every strongly connected component of `G[S]` is
trivial (acyclic), and `RankLE G (k + 1) S` says that every nontrivial strongly connected
component `C` of `G[S]` has a vertex `x` with `RankLE G k (C \ {x})`. By Definition 1, a trivial
component has cycle rank `0` and a nontrivial component `C` has cycle rank
`1 + min_{x ∈ C} r(G[C] - x)`; whether `G[S]` is acyclic, strongly connected or neither, `r(G[S])`
is the maximum of these over its components, so `RankLE G k S ↔ r(G[S]) ≤ k` by induction on
`k`. The strongly connected component of `v` in `G[S]` is the set of `u ∈ S` with directed paths
from `v` to `u` and back inside `S` (`Relation.ReflTransGen` of the arcs of `G[S]`, the relation
CSLibExt's `DirectedAdjacency.Reachable` unfolds to, here on induced subdigraphs).

Digraphs follow Gruber: `E ⊆ V²`, loops allowed. They are given by arc lists without repeated
arcs, read as Mathlib `Digraph`s on `Fin n`. Membership in NP: a directed elimination forest
(Gruber, Definition 2 and Theorem 10) is a certificate; it involves only vertices of nontrivial
components, which are endpoints of arcs, so it stays polynomial although `n` is binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), arc list, and the bound `k`. -/
abbrev CycleRankInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph `G = (V, E)` of the instance: an arc from `u` to `v` when `(u, v)` is
listed (`u = v` is a loop). -/
def Graph (i : CycleRankInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are in
range. -/
def WellFormed (i : CycleRankInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1

/-- `v` is reachable from `u` in the induced subdigraph `G[S]`: a directed path, possibly
empty, whose arcs join vertices of `S`. -/
def ReachIn {n : ℕ} (G : Digraph (Fin n)) (S : Finset (Fin n)) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ G.Adj a b) u v

open Classical in
/-- The strongly connected component of `v` in `G[S]`: the vertices `u ∈ S` with directed
paths from `v` to `u` and from `u` to `v` inside `S`. -/
noncomputable def component {n : ℕ} (G : Digraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  S.filter fun u => ReachIn G S v u ∧ ReachIn G S u v

/-- A vertex set `C` is nontrivial: the induced subdigraph `G[C]` has at least one edge (a loop
counts). -/
def IsNontrivial {n : ℕ} (G : Digraph (Fin n)) (C : Finset (Fin n)) : Prop :=
  ∃ a ∈ C, ∃ b ∈ C, G.Adj a b

/-- `G[S]` has cycle rank at most `k`: for `k = 0`, every strongly connected component of
`G[S]` is trivial; for `k + 1`, every nontrivial strongly connected component `C` of `G[S]` has
a vertex `x` such that `G[C \ {x}]` has cycle rank at most `k`. -/
def RankLE {n : ℕ} (G : Digraph (Fin n)) : ℕ → Finset (Fin n) → Prop
  | 0, S => ∀ v ∈ S, ¬ IsNontrivial G (component G S v)
  | k + 1, S => ∀ v ∈ S, IsNontrivial G (component G S v) →
      ∃ x ∈ component G S v, RankLE G k ((component G S v).erase x)

/-- The cycle rank of `G` is at most `k`. -/
def CycleRankFeasible (i : CycleRankInstance) : Prop :=
  RankLE (Graph i) i.2.2 Finset.univ

open Classical in
/-- CYCLE RANK as a decision problem over bitstrings. -/
noncomputable def cycleRankDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CycleRankInstance) x with
  | some i => decide (WellFormed i ∧ CycleRankFeasible i)
  | none => false

/-- **CYCLE RANK is NP-complete.** Source: Gruber (2012), Theorem 10. -/
public theorem_wanted cycleRank_npComplete :
    cycleRankDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cycleRankDec

end MetaMathlibExt.Complexity.NPComplete.CycleRank
