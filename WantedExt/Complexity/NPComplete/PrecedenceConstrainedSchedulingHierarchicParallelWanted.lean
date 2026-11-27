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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Fin.Basic
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

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

mutual
/-- A derivation of a hierarchic parallel graph: a node, rule (i) with its two nodes replaced
by HPGs, or rule (ii) with its top, middle and bottom nodes replaced by HPGs. -/
inductive HPG : Type
  | node : HPG
  | series : HPG → HPG → HPG
  | diamond : HPG → Branches → HPG → HPG

/-- The `n ≥ 1` middle parts of a diamond. -/
inductive Branches : Type
  | one : HPG → Branches
  | cons : HPG → Branches → Branches
end

mutual
/-- The number of nodes. -/
def HPG.size : HPG → ℕ
  | .node => 1
  | .series a b => a.size + b.size
  | .diamond a bs c => a.size + bs.size + c.size

/-- The number of nodes of the middle parts. -/
def Branches.size : Branches → ℕ
  | .one a => a.size
  | .cons a bs => a.size + bs.size
end

mutual
/-- The partial order of an HPG on its nodes `0, …, size - 1`: `before t x y` when `x < y` in
the order generated by the edges. -/
def HPG.before : HPG → ℕ → ℕ → Bool
  | .node, _, _ => false
  | .series a b, x, y =>
      (decide (x < a.size) && decide (y < a.size) && a.before x y) ||
      (decide (a.size ≤ x) && decide (a.size ≤ y) && b.before (x - a.size) (y - a.size)) ||
      (decide (x < a.size) && decide (a.size ≤ y) && decide (y < a.size + b.size))
  | .diamond a bs c, x, y =>
      (decide (x < a.size) && decide (y < a.size) && a.before x y) ||
      (decide (a.size ≤ x) && decide (a.size ≤ y) && bs.before (x - a.size) (y - a.size)) ||
      (decide (a.size + bs.size ≤ x) && decide (a.size + bs.size ≤ y) &&
        c.before (x - (a.size + bs.size)) (y - (a.size + bs.size))) ||
      (decide (x < a.size) && decide (a.size ≤ y) &&
        decide (y < a.size + bs.size + c.size)) ||
      (decide (a.size ≤ x) && decide (x < a.size + bs.size) &&
        decide (a.size + bs.size ≤ y) && decide (y < a.size + bs.size + c.size))

/-- The partial order of the middle parts: each part ordered as itself, different parts
unordered. -/
def Branches.before : Branches → ℕ → ℕ → Bool
  | .one a, x, y => a.before x y
  | .cons a bs, x, y =>
      (decide (x < a.size) && decide (y < a.size) && a.before x y) ||
      (decide (a.size ≤ x) && decide (a.size ≤ y) && bs.before (x - a.size) (y - a.size))
end

/-- The listed precedence order is the partial order of an HPG, up to renumbering the tasks. -/
def IsHierarchicParallel (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  ∃ t : HPG, ∃ e : Task i ≃ Fin t.size, ∀ a b, Prec i a b ↔ t.before (e a) (e b) = true

/-- Well-formedness: a well-formed `PRECEDENCE CONSTRAINED SCHEDULING` instance whose order
is the partial order of a hierarchic parallel graph. -/
def WellFormed (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i ∧ IsHierarchicParallel i

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING for hierarchic parallel graphs as a decision problem over
bitstrings. -/
noncomputable def precedenceConstrainedSchedulingHierarchicParallelDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingFeasible i)
  | none => false

/-- **PRECEDENCE CONSTRAINED SCHEDULING for hierarchic parallel graphs is NP-complete.**
Source: Mayr (1981), Theorem 1; Johnson (1983), [SS9]. -/
public theorem_wanted precedenceConstrainedSchedulingHierarchicParallel_npComplete :
    precedenceConstrainedSchedulingHierarchicParallelDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSchedulingHierarchicParallelDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingHierarchicParallel
