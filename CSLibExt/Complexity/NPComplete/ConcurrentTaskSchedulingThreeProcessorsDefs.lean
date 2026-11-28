/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONCURRENT TASK SCHEDULING ON THREE PROCESSORS: definitions

Source:
E. L. Lloyd, "Concurrent task systems", Operations Research 29 (1981), 189-201,
doi:10.1287/opre.29.1.189 (abstract: a concurrent task system "consists of: m identical
processors, tasks T₁, …, Tₙ, and a partial order on those tasks which represents precedence
constraints. Associated with each task Tᵢ is a positive integral execution time τᵢ and a degree
of concurrency qᵢ ∈ 𝒞 where 𝒞 ⊆ {1, …, m}. Task Tᵢ must execute for τᵢ steps and for each of
those τᵢ steps it requires qᵢ processors. ... we show that scheduling concurrent UET task
systems is NP-complete even if there are only three processors and each task has a degree of
concurrency of either 1 or 2"; the full text was not available to us);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problems [SS9] PRECEDENCE CONSTRAINED SCHEDULING (every
degree `1`) and [SS10] RESOURCE CONSTRAINED SCHEDULING (the model with precedence used here).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBoundDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConcurrentTaskSchedulingThreeProcessors

open ResourceConstrainedScheduling (Task req bound)
open ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance PrecedenceWellFormed PrecedenceFeasible)

/-- Well-formedness of an instance: it is well-formed for RESOURCE CONSTRAINED SCHEDULING with a
partial order (unit tasks, a strict partial order, a positive deadline), with `m = 3`
processors, `r = 1` resource of bound `B_1 = 3` (the processors), and every task's degree of
concurrency `R_1(t)` equal to `1` or `2`. -/
def WellFormed (i : PrecedenceResourceSchedulingInstance) : Prop :=
  PrecedenceWellFormed i ∧ i.1.1 = 3 ∧ i.1.2.1 = 1 ∧ bound i.1 0 = 3 ∧
    ∀ t : Task i.1, req i.1 t 0 = 1 ∨ req i.1 t 0 = 2

open Classical in
/-- CONCURRENT TASK SCHEDULING ON THREE PROCESSORS as a decision problem over bitstrings. -/
noncomputable def concurrentTaskSchedulingThreeProcessorsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceResourceSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConcurrentTaskSchedulingThreeProcessors
