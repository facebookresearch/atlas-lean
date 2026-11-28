/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Relation

/-!
# SIMPLE ASSEMBLY LINE BALANCING (SALBP-1): definitions

INSTANCE: tasks `0, …, n - 1` with integer task times `t_j ∈ ℤ₀⁺`, precedence constraints
given by a directed acyclic graph on the tasks, a cycle time `c` and a number `K` of stations.
QUESTION: can the tasks be assigned to the `K` stations `0, …, K - 1` of a line so that the total
task time at every station is at most `c` and every task is at a station no earlier than the
stations of its predecessors?

This is the decision version of SALBP-1 (minimize the number of stations for a given cycle
time). An arc `(i, j)` says that task `i` precedes task `j`; the assignment condition on the
arcs implies it for the partial order they generate. Acyclicity is stated with Mathlib's
`Relation.TransGen`: no task precedes itself. Without arcs the problem is BIN PACKING ([SR1];
`BinPackingWanted`), so it is NP-complete in the strong sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR1] BIN PACKING (the special case
without precedence constraints);
M. Ritt and A. M. Costa, "Improved integer programming models for simple assembly line balancing
and related problems", International Transactions in Operational Research 25 (2018), 1345-1359,
doi:10.1111/itor.12206 (the decision version of SALBP-1 is NP-complete, since without precedence
constraints it is bin packing);
T. S. Wee and M. J. Magazine, "Assembly line balancing as generalized bin packing", Operations
Research Letters 1 (1982), 56-58, doi:10.1016/0167-6377(82)90046-3.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleAssemblyLineBalancing

/-- An instance: the task times, the precedence arcs `(i, j)` (task `i` precedes task `j`),
the cycle time `c` and the number `K` of stations. -/
abbrev SimpleAssemblyLineBalancingInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every arc joins two tasks, and the precedence graph is
acyclic. -/
def WellFormed (i : SimpleAssemblyLineBalancingInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length) ∧
    ∀ v, ¬ Relation.TransGen (fun a b => (a, b) ∈ i.2.1) v v

/-- There is an assignment `f` of the tasks to the stations `0, …, K - 1` such that
`f i ≤ f j` for every arc `(i, j)` and the task times at every station sum to at most `c`. -/
def SimpleAssemblyLineBalancingFeasible (i : SimpleAssemblyLineBalancingInstance) : Prop :=
  ∃ f : Fin i.1.length → Fin i.2.2.2,
    (∀ a b : Fin i.1.length, ((a : ℕ), (b : ℕ)) ∈ i.2.1 → f a ≤ f b) ∧
    ∀ k, ∑ j ∈ Finset.univ.filter (fun j => f j = k), i.1.get j ≤ i.2.2.1

open Classical in
/-- SIMPLE ASSEMBLY LINE BALANCING as a decision problem over bitstrings. -/
noncomputable def simpleAssemblyLineBalancingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimpleAssemblyLineBalancingInstance) x with
  | some i => decide (WellFormed i ∧ SimpleAssemblyLineBalancingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleAssemblyLineBalancing
