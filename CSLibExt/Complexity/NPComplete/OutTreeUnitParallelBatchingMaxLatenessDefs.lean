/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|outtree;p_i=1;p-batch;b<n|L_max`: definitions

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275 (`P|outtree;p_i=1|L_max`);
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Parallel batching
problems" (`1|outtree;p_i=1;p-batch;b<n|L_max`, minimal NP-hard in the strong sense, by
reduction from the parallel machine problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OutTreeUnitParallelBatchingMaxLateness

open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open UnitFlowShopOutTreeMaxLateness (toInt)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-- An instance: the batch capacity `b`, the precedence arcs `(i, k)`, the due dates
`d_0, …, d_{n-1}` (jobs `Fin n`), and the bound `K`; due dates and bound as pairs `(a, b)`
standing for `a - b`. -/
abbrev OutTreeUnitParallelBatchingMaxLatenessInstance :=
  ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: `0 < b < n`, the arcs name jobs and form an acyclic digraph,
and every job has at most one immediate predecessor (an out-tree). -/
def WellFormed (i : OutTreeUnitParallelBatchingMaxLatenessInstance) : Prop :=
  0 < i.1 ∧ i.1 < i.2.2.1.length ∧ PrecWellFormed i.2.2.1.length i.2.1 ∧
    ∀ k a b : Fin i.2.2.1.length, ImmediatePredecessor i.2.1 a k →
      ImmediatePredecessor i.2.1 b k → a = b

/-- Some batch schedule `σ` (batch start time of each job) puts at most `b` jobs in each batch,
obeys the precedence arcs, and has maximum lateness at most `K`:
`(σ(t) + 1) - d_t ≤ K` for every job `t`. -/
def OutTreeUnitParallelBatchingMaxLatenessFeasible
    (i : OutTreeUnitParallelBatchingMaxLatenessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ i.1) ∧
    (∀ t t', Prec i.2.1 t t' → σ t + 1 ≤ σ t') ∧
    ∀ t, ((σ t + 1 : ℕ) : ℤ) - toInt (i.2.2.1.get t) ≤ toInt i.2.2.2

open Classical in
/-- `1|outtree;p_i=1;p-batch;b<n|L_max` as a decision problem over bitstrings. -/
noncomputable def outTreeUnitParallelBatchingMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OutTreeUnitParallelBatchingMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ OutTreeUnitParallelBatchingMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OutTreeUnitParallelBatchingMaxLateness
