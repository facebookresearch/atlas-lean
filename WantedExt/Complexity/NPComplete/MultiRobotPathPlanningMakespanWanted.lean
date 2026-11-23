/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-ROBOT PATH PLANNING with bounded makespan is NP-complete

Source:
P. Surynek, "An optimization variant of multi-robot path planning is intractable",
Proceedings of the Twenty-Fourth AAAI Conference on Artificial Intelligence (AAAI 2010),
1261-1263, doi:10.1609/aaai.v24i1.7767.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiRobotPathPlanningMakespan

/-!
# MULTI-ROBOT PATH PLANNING with bounded makespan is NP-complete

Also known as multi-agent path finding with optimal makespan (MAPF). Surynek (2010),
Definition 1: an undirected graph `G = (V, E)`, robots `R = {r₁, ..., r_ν}` with `ν < |V|`, an
initial arrangement `S⁰ : R → V` and a goal arrangement `S⁺ : R → V`, both simple (injective).
A solution of makespan `ζ` is a sequence `S⁰, S¹, ..., S^ζ` of simple arrangements with
(i) `S^ζ = S⁺`; (ii) at each step every robot stays (`S^{k+1}(r) = S^k(r)`) or moves along an
edge (`{S^k(r), S^{k+1}(r)} ∈ E`); (iii) every move is allowed, where allowed moves are defined
transitively: a move into a vertex that no other robot occupies at time `k` is allowed, and a
move into a vertex that another robot leaves at time `k` by an allowed move is allowed (robots
move like a train). QUESTION (the decision version of the optimization variant): given a bound
`T`, is there a solution of makespan at most `T`?

`Allowed` is an inductive predicate, the least set of moves closed under the two clauses of
(iii), so a rotation of robots along a cycle (in particular two robots swapping along an edge)
is not allowed. Since a robot may stay put, a solution of makespan `ζ ≤ T` extends to one of
makespan exactly `T`, so "at most `T`" and the source's "of the makespan `η`" agree. The source
writes condition (ii) for `k = 1, 2, ..., ζ - 1`; we impose it at every step `k < ζ`, starting
from `S⁰`, as its sequence `S⁰, ..., S^ζ` requires.

Vertices are `Fin n` and the graph is `Cslib.Complexity.Karp.edgeGraph n E`; robot `r` is the
`r`-th listed (start, goal) pair.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of vertices `n`, the edge list, the robots as (start, goal) vertex
pairs, and the makespan bound `T`. -/
abbrev MultiRobotPathPlanningMakespanInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MultiRobotPathPlanningMakespanInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The number of robots `ν`. -/
abbrev numRobots (i : MultiRobotPathPlanningMakespanInstance) : ℕ := i.2.2.1.length

/-- The start vertex of robot `r`. -/
def start (i : MultiRobotPathPlanningMakespanInstance) (r : Fin (numRobots i)) : ℕ :=
  (i.2.2.1.get r).1

/-- The goal vertex of robot `r`. -/
def goal (i : MultiRobotPathPlanningMakespanInstance) (r : Fin (numRobots i)) : ℕ :=
  (i.2.2.1.get r).2

/-- Well-formedness of an instance: the edge list is a simple undirected edge list on `Fin n`,
the start and goal vertices are vertices, the initial and goal arrangements are simple (no two
robots share a start, or a goal), and there are fewer robots than vertices. -/
def WellFormed (i : MultiRobotPathPlanningMakespanInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1 ∧ p.2 < i.1) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧ (i.2.2.1.map Prod.snd).Nodup ∧
    numRobots i < i.1

/-- `Allowed S S' r`: the move of robot `r` from arrangement `S` (time `k`) to arrangement `S'`
(time `k + 1`) is allowed, Surynek's condition (iii): either `r` moves into a vertex that no
other robot occupies at time `k`, or `r` moves into the vertex of another robot `s` that itself
moves away by an allowed move. -/
inductive Allowed {ν n : ℕ} (S S' : Fin ν → Fin n) : Fin ν → Prop
  /-- A move into a vertex no other robot occupies at time `k`. -/
  | free (r : Fin ν) : S r ≠ S' r → (∀ s, s ≠ r → S s ≠ S' r) → Allowed S S' r
  /-- A move into the vertex that another robot `s` leaves by an allowed move. -/
  | train (r s : Fin ν) : S r ≠ S' r → s ≠ r → S s = S' r → S s ≠ S' s → Allowed S S' s →
      Allowed S S' r

/-- A solution of makespan at most `T` exists: arrangements `S 0, ..., S ζ` with `ζ ≤ T`, each
injective, starting at the start vertices and ending at the goal vertices, where at each step
every robot stays or moves along an edge, and every move is allowed. -/
def MultiRobotPathPlanningMakespanFeasible (i : MultiRobotPathPlanningMakespanInstance) :
    Prop :=
  ∃ ζ ≤ i.2.2.2, ∃ S : ℕ → Fin (numRobots i) → Fin i.1,
    (∀ r, (S 0 r : ℕ) = start i r) ∧ (∀ r, (S ζ r : ℕ) = goal i r) ∧
    (∀ k ≤ ζ, Function.Injective (S k)) ∧
    ∀ k < ζ, ∀ r,
      (S (k + 1) r = S k r ∨ (Graph i).Adj (S k r) (S (k + 1) r)) ∧
      (S k r ≠ S (k + 1) r → Allowed (S k) (S (k + 1)) r)

open Classical in
/-- MULTI-ROBOT PATH PLANNING with bounded makespan as a decision problem over bitstrings. -/
noncomputable def multiRobotPathPlanningMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiRobotPathPlanningMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiRobotPathPlanningMakespanFeasible i)
  | none => false

/-- **MULTI-ROBOT PATH PLANNING with bounded makespan is NP-complete.** Source: Surynek (2010),
Theorem 1 and the membership argument that follows it. -/
public theorem_wanted multiRobotPathPlanningMakespan_npComplete :
    multiRobotPathPlanningMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiRobotPathPlanningMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiRobotPathPlanningMakespan
