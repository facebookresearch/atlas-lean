/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING on dedicated processors for forests: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForestsDefs
public import CSLibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ForestDedicatedProcessorPrecedenceScheduling

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task)
open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForests
  (ImmediatePredecessor)
open MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling
  (DedicatedProcessorsInstance DedicatedWellFormed DedicatedProcessorsFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.ForestDedicatedProcessorPrecedenceScheduling
