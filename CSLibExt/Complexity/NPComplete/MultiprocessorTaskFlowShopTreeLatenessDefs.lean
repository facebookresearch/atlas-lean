/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP WITH TREE PRECEDENCE AND UNIT TIMES (FMPT|tree; p_ij = 1|L_max): definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|tree; p_ij = 1|L_max` as minimal NP-hard in the strong sense with the
attribution to Brucker and Knust (1999);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT flow-shop
model) and Section 1.3 (precedence relations).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed UnitJobs)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-- `i` is an immediate predecessor of `k` (and `k` an immediate successor of `i`) in the
precedence relation of the listed arcs: `k` is reachable from `i` along arcs, and no job `c` has
`k` reachable from `c` and `c` reachable from `i`. -/
def ImmediatePredecessor (prs : List (ℕ × ℕ)) {n : ℕ} (i k : Fin n) : Prop :=
  Relation.TransGen (Prec prs) i k ∧
    ∀ c, ¬ (Relation.TransGen (Prec prs) i c ∧ Relation.TransGen (Prec prs) c k)

/-- Every job has at most one immediate successor, or every job has at most one immediate
predecessor, in the precedence relation of the listed arcs on `n` jobs (the intree and outtree
conditions). On its own this is not a tree test: acyclicity is checked separately
(`PrecWellFormed`), connectivity is not required, and a self-loop gives a job no immediate
predecessor or successor. -/
def IsTreePrecedence (n : ℕ) (prs : List (ℕ × ℕ)) : Prop :=
  (∀ j a b : Fin n, ImmediatePredecessor prs j a → ImmediatePredecessor prs j b → a = b) ∨
    ∀ j a b : Fin n, ImmediatePredecessor prs a j → ImmediatePredecessor prs b j → a = b

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the jobs
(job `i` listed by its processing times `(p_i1, …, p_ir)` and its due date `d_i` as a
`(positive part, negative part)` pair), the arcs `(i, k)` with `i → k`, and the bound `K` as a
`(positive part, negative part)` pair. -/
abbrev MultiprocessorTaskFlowShopTreeLatenessInstance :=
  ℕ × List (List ℕ) × List (List ℕ × (ℕ × ℕ)) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The due date `d_j ∈ ℤ` of job `j`. -/
def dueDate (i : MultiprocessorTaskFlowShopTreeLatenessInstance) (j : Fin i.2.2.1.length) : ℤ :=
  ((i.2.2.1.get j).2.1 : ℤ) - ((i.2.2.1.get j).2.2 : ℤ)

/-- The bound `K ∈ ℤ` on the maximum lateness. -/
def bound (i : MultiprocessorTaskFlowShopTreeLatenessInstance) : ℤ :=
  (i.2.2.2.2.1 : ℤ) - (i.2.2.2.2.2 : ℤ)

/-- Well-formedness of an instance: there is at least one job, the machine environment is well
formed (`StagesWellFormed`), every stage needs at least one processor (each stage's processor
list is nonempty), every job has `r` unit processing times (`UnitJobs`), the listed arcs
describe an acyclic precedence digraph on the jobs (`PrecWellFormed`), and its
precedence relation is an in-forest or an out-forest, not necessarily connected
(`IsTreePrecedence`). -/
def WellFormed (i : MultiprocessorTaskFlowShopTreeLatenessInstance) : Prop :=
  i.2.2.1 ≠ [] ∧ StagesWellFormed i.1 i.2.1 ∧ (∀ M ∈ i.2.1, M ≠ []) ∧
    UnitJobs i.2.1.length (i.2.2.1.map Prod.fst) ∧
    PrecWellFormed i.2.2.1.length i.2.2.2.1 ∧ IsTreePrecedence i.2.2.1.length i.2.2.2.1

/-- Some MPT flow-shop schedule of the unit-time jobs obeys the precedence constraints and has
maximum lateness at most `K`: `C_j - d_j ≤ K` for every job `j`. -/
def MultiprocessorTaskFlowShopTreeLatenessFeasible
    (i : MultiprocessorTaskFlowShopTreeLatenessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∀ j, (completionTime (fun _ _ => 1) σ j : ℤ) - dueDate i j ≤ bound i

open Classical in
/-- `FMPT|tree; p_ij = 1|L_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskFlowShopTreeLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopTreeLatenessInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskFlowShopTreeLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLateness
