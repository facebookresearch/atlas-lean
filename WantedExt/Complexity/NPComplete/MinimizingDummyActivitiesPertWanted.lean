/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND44] MINIMIZING DUMMY ACTIVITIES IN
PERT NETWORKS, p. 218;
M. S. Krishnamoorthy and N. Deo, "Complexity of the minimum-dummy-activities problem in a PERT
network", Networks 9 (1979), 189-194, doi:10.1002/net.3230090302.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimizingDummyActivitiesPert

/-!
# MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)`, where vertices represent tasks and the arcs
represent precedence constraints, and a positive integer `K ≤ |V|`. QUESTION: is there a PERT
network corresponding to `G` with `K` or fewer dummy activities, i.e., a directed acyclic graph
`G' = (V', A')` where `V' = {vᵢ⁻, vᵢ⁺ : vᵢ ∈ V}` and `{(vᵢ⁻, vᵢ⁺) : vᵢ ∈ V} ⊆ A'`, such that
`|A'| ≤ |V| + K` and such that there is a path from `vᵢ⁺` to `vⱼ⁻` in `G'` if and only if there
is a path from `vᵢ` to `vⱼ` in `G`?

`G` is a Mathlib `Digraph (Fin n)` given by its arc list. In a PERT (activity-on-arc) network
the end of one activity and the start of another may be the same event, so the names `vᵢ⁻`,
`vᵢ⁺` need not denote distinct vertices: `G'` has events `Fin m`, every event is one of the
names (`V' = {vᵢ⁻, vᵢ⁺}`), and task `vᵢ` is the arc from `tail i = vᵢ⁻` to `head i = vᵢ⁺`. The
task arcs are distinct (one activity per arc), the arcs of `A'` other than the task arcs are the
dummy activities, and `|A'| ≤ |V| + K` says there are at most `K` of them. A path in `G'` from
`vᵢ⁺` to `vⱼ⁻` may be empty (when `vᵢ⁺` and `vⱼ⁻` are the same event; `ReflTransGen`), while a
path from `vᵢ` to `vⱼ` in `G` is a nonempty directed path (`TransGen`): for `i = j`, `G` has
no such path (it is acyclic) and neither has `G'`, since `vᵢ⁺ ⇝ vᵢ⁻` would close a cycle with the
task arc.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of tasks (vertices `Fin n`), the arc list of `G`, and the bound
`K`. -/
abbrev MinimizingDummyActivitiesInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The precedence graph `G`: an arc `u → v` for each entry `(u, v)` of the arc list. -/
def Graph (i : MinimizingDummyActivitiesInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are
vertices, `G` is acyclic (no vertex has a nonempty path to itself), and `0 < K ≤ |V|`. -/
def WellFormed (i : MinimizingDummyActivitiesInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- There is a PERT network with at most `K` dummy activities: events `Fin m`, each the start
`tail i` or the end `head i` of some task, an arc set `A'` that contains the distinct task arcs
`(tail i, head i)`, has at most `|V| + K` arcs, is acyclic, and has a (possibly empty) path from
`head u` to `tail v` exactly when `G` has a nonempty path from `u` to `v`. -/
def MinimizingDummyActivitiesFeasible (i : MinimizingDummyActivitiesInstance) : Prop :=
  ∃ m, ∃ tail head : Fin i.1 → Fin m, ∃ A' : Finset (Fin m × Fin m),
    (∀ e, ∃ v, tail v = e ∨ head v = e) ∧ (∀ v, (tail v, head v) ∈ A') ∧
      Function.Injective (fun v => (tail v, head v)) ∧ A'.card ≤ i.1 + i.2.2 ∧
      (∀ x, ¬ Relation.TransGen (fun a b => (a, b) ∈ A') x x) ∧
      ∀ u v, Relation.ReflTransGen (fun a b => (a, b) ∈ A') (head u) (tail v) ↔
        Relation.TransGen (Graph i).Adj u v

open Classical in
/-- MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS as a decision problem over bitstrings. -/
noncomputable def minimizingDummyActivitiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimizingDummyActivitiesInstance) x with
  | some i => decide (WellFormed i ∧ MinimizingDummyActivitiesFeasible i)
  | none => false

/-- **MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS is NP-complete.** Source: Garey and Johnson
(1979), [ND44]; Krishnamoorthy and Deo (1979). -/
public theorem_wanted minimizingDummyActivities_npComplete :
    minimizingDummyActivitiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimizingDummyActivitiesDec

end MetaMathlibExt.Complexity.NPComplete.MinimizingDummyActivitiesPert
