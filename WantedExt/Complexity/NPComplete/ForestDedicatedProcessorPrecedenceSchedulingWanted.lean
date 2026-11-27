/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING on dedicated processors for forests is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING, p. 239 (comment: "If each task `t` can only be executed by a specified processor
`p(t)`, the problem is NP-complete for `m = 2` and `<` arbitrary, and for `m` arbitrary and `<` a
forest, but can be solved in polynomial time for `m` arbitrary if `<` is a 'cyclic forest'
[Goyal, 1976]"), citing D. K. Goyal, "Scheduling processor bound systems", Technical Report,
Computer Science Department, Washington State University (1976) (not available to this
formalization).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForestsWanted
public import WantedExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ForestDedicatedProcessorPrecedenceScheduling

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task)
open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForests
  (ImmediatePredecessor)
open MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling
  (DedicatedProcessorsInstance DedicatedWellFormed DedicatedProcessorsFeasible)

/-!
# PRECEDENCE CONSTRAINED SCHEDULING on dedicated processors for forests is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors, a
partial order `<` on `T` that is a forest, a deadline `D ∈ ℤ⁺`, and for each task `t ∈ T` a
specified processor `p(t)`.
QUESTION: is there an `m`-processor schedule `σ` for `T` that meets the overall deadline `D`,
obeys the precedence constraints, i.e., `t < t'` implies `σ(t') ≥ σ(t) + l(t) = σ(t) + 1`, and
executes each task `t` only on its processor `p(t)`?

This is the second case of the dedicated-processor comment of [SS9]: `m` arbitrary and `<` a
forest. The instance type, `DedicatedWellFormed` (unit lengths, `m > 0`, the listed pairs name
tasks and form a strict partial order, `D > 0`, one processor `p(t) < m` per task) and the
question `DedicatedProcessorsFeasible` are those of
`TwoDedicatedProcessorPrecedenceSchedulingWanted` (the case `m = 2`, `<` arbitrary),
reused unchanged; `WellFormed` adds that `<` is a forest.

A partial order is a forest when its Hasse diagram, taken as an undirected graph, is a forest:
the simple graph joining `t` and `t'` when one is an immediate predecessor of the other
(`PrecedenceConstrainedSchedulingOpposingForests.ImmediatePredecessor`: `t < t'` with no `c` such
that `t < c < t'`) is acyclic (Mathlib's `SimpleGraph.IsAcyclic`). This class contains the
in-forests (no task with two immediate successors) and the out-forests (no task with two
immediate predecessors), so a hardness proof for either orientation applies to it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The partial order is a forest: its Hasse diagram, the undirected graph of the immediate
predecessor relation, is acyclic. -/
def IsForest (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  (SimpleGraph.fromRel (ImmediatePredecessor i)).IsAcyclic

/-- Well-formedness of an instance: `DedicatedWellFormed` (any number `m` of processors) and the
partial order is a forest. -/
def WellFormed (i : DedicatedProcessorsInstance) : Prop :=
  DedicatedWellFormed i ∧ IsForest i.1

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING on dedicated processors for forests as a decision problem
over bitstrings. -/
noncomputable def forestDedicatedProcessorPrecedenceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DedicatedProcessorsInstance) x with
  | some i => decide (WellFormed i ∧ DedicatedProcessorsFeasible i)
  | none => false

/-- **PRECEDENCE CONSTRAINED SCHEDULING is NP-complete on dedicated processors for forests.**
Source: Garey and Johnson (1979), [SS9], comment (Goyal, 1976). -/
public theorem_wanted forestDedicatedProcessorPrecedenceScheduling_npComplete :
    forestDedicatedProcessorPrecedenceSchedulingDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            forestDedicatedProcessorPrecedenceSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ForestDedicatedProcessorPrecedenceScheduling
