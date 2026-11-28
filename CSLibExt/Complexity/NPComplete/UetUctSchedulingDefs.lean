/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UET-UCT SCHEDULING (UNIT COMMUNICATION DELAYS): definitions

Source:
V. J. Rayward-Smith, "UET scheduling with unit interprocessor communication delays", Discrete
Applied Mathematics 18 (1987), 55-71, doi:10.1016/0166-218X(87)90042-4;
J. A. Hoogeveen, J. K. Lenstra, and B. Veltman, "Three, four, five, six, or the complexity of
scheduling with communication delays", Operations Research Letters 16 (1994), 129-137,
doi:10.1016/0167-6377(94)90024-8, Theorem 2 (NP-complete already for the bound `4`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (the problem without communication delays).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UetUctScheduling

/-- An instance: the number `m` of processors, the processing times `[p_1, …, p_n]` of the
tasks (all `1`), the arcs `(j, k)` of the precedence graph (`k` needs data from `j`), and the
bound `d`. -/
abbrev UetUctSchedulingInstance := ℕ × List ℕ × List (ℕ × ℕ) × ℕ

/-- The arc relation of the precedence graph: `j → k` when the pair `(j, k)` is listed. -/
def Arc (i : UetUctSchedulingInstance) (j k : Fin i.2.1.length) : Prop :=
  ((j : ℕ), (k : ℕ)) ∈ i.2.2.1

/-- Well-formedness of an instance: `0 < m`, every processing time is `1`, every arc names two
tasks, and the precedence graph is acyclic (the transitive closure `Relation.TransGen` of the arc
relation is irreflexive). -/
def WellFormed (i : UetUctSchedulingInstance) : Prop :=
  0 < i.1 ∧ (∀ p ∈ i.2.1, p = 1) ∧ (∀ a ∈ i.2.2.1, a.1 < i.2.1.length ∧ a.2 < i.2.1.length) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- Some schedule, a start time `S j` (task `j` occupies `[S j, S j + 1)`) and a processor
`P j` for every task, runs at most one task at a time on each processor, respects every arc
`j → k` (`S j + 1 ≤ S k` on a common processor, `S j + 1 + 1 ≤ S k` on different
processors), and completes every task by `d`. -/
def UetUctSchedulingFeasible (i : UetUctSchedulingInstance) : Prop :=
  ∃ (S : Fin i.2.1.length → ℕ) (P : Fin i.2.1.length → Fin i.1),
    (∀ j k, j ≠ k → P j = P k → S j ≠ S k) ∧
    (∀ j k, Arc i j k → P j = P k → S j + 1 ≤ S k) ∧
    (∀ j k, Arc i j k → P j ≠ P k → S j + 1 + 1 ≤ S k) ∧
    ∀ j, S j + 1 ≤ i.2.2.2

open Classical in
/-- UET-UCT SCHEDULING as a decision problem over bitstrings. -/
noncomputable def uetUctSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UetUctSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ UetUctSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UetUctScheduling
