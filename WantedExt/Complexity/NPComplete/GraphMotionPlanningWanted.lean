/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH MOTION PLANNING is NP-complete

Source:
C. H. Papadimitriou, P. Raghavan, M. Sudan and H. Tamaki, "Motion planning on a graph", in
*Proceedings 35th Annual Symposium on Foundations of Computer Science*, IEEE (1994), 511-520,
doi:10.1109/SFCS.1994.365740 (the problem; NP-complete even for planar graphs);
G. Călinescu, A. Dumitrescu and J. Pach, "Reconfigurations in graphs and grids", SIAM Journal
on Discrete Mathematics 22 (2008), 124-138, doi:10.1137/060652063 (Section 1 records the
result: "The problem has been shown to be NP-complete even for planar graphs");
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GRAPH MOTION PLANNING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphMotionPlanning

/-!
# GRAPH MOTION PLANNING is NP-complete

INSTANCE: a connected undirected graph `G = (V, E)`, a start vertex `s ∈ V` where the robot is
initially placed, a goal vertex `t ∈ V`, a set `W ⊆ V \ {s}` of vertices where the obstacles are
initially placed, and a positive integer `K`.
QUESTION: can the robot be moved to `t` in at most `K` steps, where in each step either the
robot or one obstacle is moved from its vertex to an adjacent vertex that is not occupied by the
robot or an obstacle?

This is the decision version of MINIMUM GRAPH MOTION PLANNING in the Crescenzi-Kann
compendium, the problem of Papadimitriou, Raghavan, Sudan and Tamaki: "We are given a
connected, undirected graph G on n vertices. There is a mobile robot on one of the vertices;
this vertex is labeled s. Each of several other vertices contains a single movable obstacle. ...
A vertex may never contain more than one object (robot/obstacle). In one step, we may move
either the robot or one of the obstacles from its current position v to a vacant vertex adjacent
to v. Our goal is to move the robot to a designated vertex t using the smallest number of steps
possible." The full text of their paper was not available; Călinescu, Dumitrescu and Pach record
that they proved the problem NP-complete, even for planar graphs.

A configuration is the robot's vertex and the set of occupied obstacle vertices (obstacles have
no destinations, so they need not be told apart). A motion scheme of `τ ≤ K` steps is a sequence
of configurations `0, ..., τ` that starts at `(s, W)`, ends with the robot at `t`, and in which
each configuration follows from the previous one by one step (`Step`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the start vertex `s`, the
goal vertex `t`, the obstacle vertices `W`, and the bound `K`. -/
abbrev GraphMotionPlanningInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GraphMotionPlanningInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list is a simple undirected edge list on `Fin n`,
the graph is connected, `s` and `t` are vertices, the obstacle vertices are distinct vertices
other than `s`, and `0 < K`. -/
def WellFormed (i : GraphMotionPlanningInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧
    i.2.2.2.2.1.Nodup ∧ (∀ w ∈ i.2.2.2.2.1, w < i.1) ∧ i.2.2.1 ∉ i.2.2.2.2.1 ∧
    0 < i.2.2.2.2.2

/-- One step from the configuration `(r, O)` (robot at `r`, obstacles on `O`) to `(r', O')`:
either the robot moves to an adjacent vertex free of obstacles, or one obstacle moves from
`o ∈ O` to an adjacent vertex `o'` occupied neither by an obstacle nor by the robot. -/
def Step {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) (O : Finset (Fin n)) (r' : Fin n)
    (O' : Finset (Fin n)) : Prop :=
  (G.Adj r r' ∧ r' ∉ O ∧ O' = O) ∨
    (r' = r ∧ ∃ o ∈ O, ∃ o', G.Adj o o' ∧ o' ∉ O ∧ o' ≠ r ∧ O' = insert o' (O.erase o))

/-- Some motion scheme of at most `K` steps moves the robot from `s` to `t`: configurations
`(R k, O k)` for `k ≤ τ`, `τ ≤ K`, starting at `(s, W)`, with `R τ = t`, each obtained from the
previous one by a `Step`. -/
def GraphMotionPlanningFeasible (i : GraphMotionPlanningInstance) : Prop :=
  ∃ τ ≤ i.2.2.2.2.2, ∃ R : ℕ → Fin i.1, ∃ O : ℕ → Finset (Fin i.1),
    (R 0 : ℕ) = i.2.2.1 ∧
      O 0 = Finset.univ.filter (fun v : Fin i.1 => (v : ℕ) ∈ i.2.2.2.2.1) ∧
      (R τ : ℕ) = i.2.2.2.1 ∧ ∀ k < τ, Step (Graph i) (R k) (O k) (R (k + 1)) (O (k + 1))

open Classical in
/-- GRAPH MOTION PLANNING as a decision problem over bitstrings. -/
noncomputable def graphMotionPlanningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphMotionPlanningInstance) x with
  | some i => decide (WellFormed i ∧ GraphMotionPlanningFeasible i)
  | none => false

/-- **GRAPH MOTION PLANNING is NP-complete.** Source: Papadimitriou, Raghavan, Sudan and Tamaki
(1994); Călinescu, Dumitrescu and Pach (2008); Crescenzi and Kann, MINIMUM GRAPH MOTION PLANNING. -/
public theorem_wanted graphMotionPlanning_npComplete :
    graphMotionPlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphMotionPlanningDec

end MetaMathlibExt.Complexity.NPComplete.GraphMotionPlanning
