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
public import CSLibExt.Complexity.NPComplete.GraphMotionPlanningDefs

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

/-- **GRAPH MOTION PLANNING is NP-complete.** Source: Papadimitriou, Raghavan, Sudan and Tamaki
(1994); Călinescu, Dumitrescu and Pach (2008); Crescenzi and Kann, MINIMUM GRAPH MOTION PLANNING. -/
public theorem_wanted graphMotionPlanning_npComplete :
    graphMotionPlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphMotionPlanningDec

end MetaMathlibExt.Complexity.NPComplete.GraphMotionPlanning
