/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP WITH PRECEDENCE AND UNIT TIMES (FMPT|prec; p_ij = 1|C_max): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT flow-shop model) and Section 1.3 (precedence relations);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|prec; p_ij = 1|C_max` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (2003).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed UnitJobs)

/-- `σ` (start times) is an MPT flow-shop schedule of `n` jobs with processing times `p i s`
and stage machine sets `μ`: operation `(i, s + 1)` starts no earlier than operation `(i, s)` is
completed, and two different operations whose machine sets share a machine occupy disjoint time
intervals `[σ i s, σ i s + p i s)`. -/
def IsMPTFlowShopSchedule {n : ℕ} (μ : List (List ℕ)) (p σ : Fin n → Fin μ.length → ℕ) :
    Prop :=
  (∀ i (s : Fin μ.length) (hs : s.1 + 1 < μ.length), σ i s + p i s ≤ σ i ⟨s.1 + 1, hs⟩) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → (∃ k, k ∈ μ.get s ∧ k ∈ μ.get s') →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- `σ` is an MPT flow-shop schedule of `n` unit-time jobs (`p_ij = 1`) with stage machine sets
`μ` that obeys the precedence constraints of the listed arcs: if `i → k`, then no operation of
`k` starts before `C_i`. -/
def IsMPTPrecedenceSchedule {n : ℕ} (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) : Prop :=
  IsMPTFlowShopSchedule μ (fun _ _ => 1) σ ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the jobs
(job `i` listed by its processing times `(p_i1, …, p_ir)`), the arcs `(i, k)` with `i → k`, and
the bound `K`. -/
abbrev MultiprocessorTaskFlowShopPrecedenceMakespanInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the machine environment is well formed
(`StagesWellFormed`), every job has `r` unit processing times (`UnitJobs`), and the listed arcs
describe an acyclic precedence digraph on the jobs (`PrecWellFormed`). -/
def WellFormed (i : MultiprocessorTaskFlowShopPrecedenceMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ UnitJobs i.2.1.length i.2.2.1 ∧
    PrecWellFormed i.2.2.1.length i.2.2.2.1

/-- Some MPT flow-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultiprocessorTaskFlowShopPrecedenceMakespanFeasible
    (i : MultiprocessorTaskFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `FMPT|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskFlowShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskFlowShopPrecedenceMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespan
