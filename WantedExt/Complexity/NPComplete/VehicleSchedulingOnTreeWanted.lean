/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VEHICLE SCHEDULING ON TREE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM VEHICLE SCHEDULING ON TREE (decision version), citing Y. Karuno,
H. Nagamochi and T. Ibaraki, "Vehicle scheduling on a tree with release and handling times",
Proc. 4th ISAAC, Lecture Notes in Computer Science 762 (1993), 486-495,
doi:10.1007/3-540-57568-5_280 (journal version: Annals of Operations Research 69 (1997),
193-207, doi:10.1023/A:1018928911513);
Y. Karuno, H. Nagamochi and T. Ibaraki, "Vehicle scheduling on a tree to minimize maximum
lateness", Journal of the Operations Research Society of Japan 39(3) (1996), 345-355,
doi:10.15807/jorsj.39.345 (Section 2 states the decision problem TREE-VSP(C) with symmetric
travel times and zero processing times and recalls that it is strongly NP-hard);
H. Nagamochi, K. Mochizuki and T. Ibaraki, "Complexity of the single vehicle scheduling problem
on graphs", INFOR 35(4) (1997), 256-276, doi:10.1080/03155986.1997.11732334 (strongly NP-hard
on trees even if all handling times are zero).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.VehicleSchedulingOnTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VehicleSchedulingOnTree

/-!
# VEHICLE SCHEDULING ON TREE is NP-complete

INSTANCE: a rooted tree `T = (V, E, v₀)`, a forward travel time `f : E → ℕ`, a backward travel
time `b : E → ℕ`, a release time `r : V → ℕ`, a handling time `h : V → ℕ`, and a positive integer
`K`.
QUESTION: is there a vehicle routing schedule that starts from `v₀` at time `0`, visits all
vertices of `T` and processes the task at each of them, starting the processing of each vertex
`v` not before its release time `r(v)`, and returns to `v₀`, with total completion time at most
`K`?

The tree is given by a parent list: vertex `0` is the root `v₀`, and vertex `k + 1` is a child of
the vertex `p_k ≤ k` named by the `k`-th entry `(p_k, f_k, b_k)`, whose edge takes time `f_k` to
traverse away from the root (from `p_k` to `k + 1`) and time `b_k` towards the root. Every
rooted tree has such a numbering (for example breadth-first), and every parent list is a tree,
the graph `Graph` built with `Cslib.Complexity.Karp.edgeGraph`. The travel time `d(u, v)` is the
total time of the darts of the unique path of `T` from `u` to `v` (`pathTime` of a
`SimpleGraph.Walk` with `IsPath`).

A schedule is an order `π` of all vertices (an equivalence `Fin n ≃ Fin n`, `π k` being the
`k`-th vertex processed) together with start times `S`, as in Karuno, Nagamochi and Ibaraki: the
vehicle leaves `v₀` at time `0`, travels along tree paths, may wait at a vertex until its release
time, processes it for `h(v)` time units, and after the last vertex returns to `v₀`. So
`S(π 0) ≥ d(v₀, π 0)`, `S(π (k + 1)) ≥ S(π k) + h(π k) + d(π k, π (k + 1))`, `S(v) ≥ r(v)`, and the
completion time `S(π (n - 1)) + h(π (n - 1)) + d(π (n - 1), v₀)` is at most `K`; the waiting time
at a vertex is the slack in these inequalities. The compendium's printed formula places each
waiting time after the processing of a task, which would forbid waiting before the first task;
the source's model allows it, and is the one stated here.

The problem is NP-hard already when every edge takes the same time in both directions and every
handling time is `0` (TREE-VSP(C) of the sources). All numbers are in binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **VEHICLE SCHEDULING ON TREE is NP-complete.** Source: Crescenzi and Kann, MINIMUM VEHICLE
SCHEDULING ON TREE, citing Karuno, Nagamochi and Ibaraki (1993); strongly NP-hard already with
symmetric travel times and zero handling times, Nagamochi, Mochizuki and Ibaraki (1997). -/
public theorem_wanted vehicleSchedulingOnTree_npComplete :
    vehicleSchedulingOnTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L vehicleSchedulingOnTreeDec

end MetaMathlibExt.Complexity.NPComplete.VehicleSchedulingOnTree
