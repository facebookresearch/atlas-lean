/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING for hierarchic parallel graphs is NP-complete

Source:
E. W. Mayr, "Well structured parallel programs are not easier to schedule", Report
STAN-CS-81-880, Department of Computer Science, Stanford University (1981), Theorem 1;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 189-203,
doi:10.1016/0196-6774(83)90045-7, PRECEDENCE CONSTRAINED SCHEDULING [SS9];
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingHierarchicParallelDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingHierarchicParallel

/-!
# PRECEDENCE CONSTRAINED SCHEDULING for hierarchic parallel graphs is NP-complete

PRECEDENCE CONSTRAINED SCHEDULING [SS9] (unit-length tasks, `m` processors, a partial order on
the tasks, a deadline `D`) restricted to precedence orders whose Hasse diagram is a hierarchic
parallel graph. Mayr's definition: a dag is a hierarchic parallel graph (HPG) if it can be
obtained in a finite number of steps from the axiom `•` (a single node) by the graph grammar
with the rules
(i) any node can be replaced by two nodes joined by an edge;
(ii) any node can be replaced by a diamond: a top node with edges to `n` middle nodes, each with
     an edge to a bottom node, for any `n`;
where all edges entering a replaced node afterwards enter the topmost node of the replacing
graph, and the edges leaving it leave the bottommost node. Mayr's Theorem 1: deciding, for an
HPG `H` and positive integers `m` and `l`, whether the task system of `H` (its nodes, ordered by
the partial order the edges generate) has a schedule on `m` processors of length at most `l` is
NP-complete. Johnson's column records the result as a new NP-complete case of [SS9] with `m`
arbitrary.

The scheduling part reuses `PrecedenceConstrainedScheduling` (instance, `WellFormed` and
feasibility): the tasks are `Fin n`, the instance lists the pairs `t < t'` of the partial order,
and a schedule meeting the deadline `D` gives each task a start time with at most `m` tasks
running at once (Mayr's schedules, onto `{1, …, l}` with between `1` and `m` tasks per step,
exist exactly when these do, by closing up empty steps).

An HPG is described by its derivation. Replacing the nodes of a rule's right-hand side
independently, a derivation is a term: a single node; `series a b`, rule (i) with its two nodes
replaced by the HPGs `a` and `b`; or `diamond a bs c`, rule (ii) with its top node replaced by
`a`, its middle nodes by the HPGs of `bs` and its bottom node by `c`. We take `n ≥ 1` (`bs`
nonempty): with `n = 0` the grammar would produce graphs with several components, which Mayr's
proof treats as not being HPGs. Every HPG has a single topmost and a single bottommost node,
reachable from and reaching every node, so the partial order of a term numbers the nodes of `a`
first (then those of the middle parts, then those of `c`) and puts every node of a part before
every node of a later part; the middle parts of a diamond are mutually unordered. An HPG has no
transitive edges, so it is the Hasse diagram of its partial order, and the order determines it.
`WellFormed` asks for `PrecedenceConstrainedScheduling.WellFormed` and that the listed order is
the partial order of some HPG term, up to renumbering the tasks.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open PrecedenceConstrainedScheduling

/-- **PRECEDENCE CONSTRAINED SCHEDULING for hierarchic parallel graphs is NP-complete.**
Source: Mayr (1981), Theorem 1; Johnson (1983), [SS9]. -/
public theorem_wanted precedenceConstrainedSchedulingHierarchicParallel_npComplete :
    precedenceConstrainedSchedulingHierarchicParallelDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSchedulingHierarchicParallelDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingHierarchicParallel
