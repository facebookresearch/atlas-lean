/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(`J2|chains, pᵢⱼ = 1|∑ Cⱼ` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Job-shop problems without preemption" (`J2|chains; pᵢⱼ = 1|∑ Cᵢ`, minimal NP-hard,
credited to Timkovsky 1998);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChainsCompletionTime

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1` and with a processor
`p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])`, a precedence relation on `J` consisting of
disjoint chains (each job has at most one immediate predecessor and at most one immediate
successor), and a bound `K ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` in which,
whenever `j` precedes `j'`, the first task of `j'` starts no earlier than the last task of `j`
finishes, and whose total completion time `∑_{j ∈ J} C_j` is at most `K`, `C_j` being the time
the last task of `j` finishes?

This is `J2|chains; pᵢⱼ = 1|∑ Cᵢ`: JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingDefs`) with `m =
2`, unit task lengths, chain precedence constraints between jobs, and the deadline replaced by a
bound `K` on the total completion time. Timkovsky (1998) proves it NP-hard in the strong sense with
his job-shopping theorem, which reduces preemptive identical parallel machines to unit-time job
shops. The instance type `JobShopScheduling.JobShopSchedulingInstance`,
`JobShopScheduling.WellFormed` (which includes `n_j ≥ 1`), the tasks and their lengths and
processors are the parent's; the last component of the instance is the bound `K ∈ ℤ⁺` in place of
the deadline `D ∈ ℤ⁺`. The schedule conditions are the parent's (one-to-one start times on each
processor, one task at a time on each processor, the tasks of a job in order), with the parent's
deadline condition replaced by the bound on `∑ C_j`, where `C j` is pinned to the finishing time of
the last task of `j` (every job has a task, `n_j ≥ 1`). Unit lengths are a well-formedness
condition.

The chains are given by the list of their arcs `(j, j')`, `j` the immediate predecessor of
`j'`. `WellFormed` requires every arc to name two jobs, no two arcs with the same tail or the
same head, and no cycle (the transitive closure `Relation.TransGen` of the arc relation is
irreflexive); the precedence relation is that transitive closure. The constraint is imposed
on the arcs; on the rest of the transitive closure it follows, since every job starts its
first task before it finishes its last. Task positions are numbered from `0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the [SS18] instance of `JobShopSchedulingDefs` (the number of processors,
the jobs as lists of `(l(t), p(t))` pairs, and, in the place of the deadline, the bound `K`),
and the arcs `(j, j')` of the chains, `j` the immediate predecessor of `j'`. -/
abbrev TwoProcessorUnitJobShopChainsCompletionTimeInstance :=
  JobShopSchedulingInstance × List (ℕ × ℕ)

/-- The arc relation of the chains: `j` is the immediate predecessor of `j'` when the pair
`(j, j')` is listed. -/
def Arc (i : TwoProcessorUnitJobShopChainsCompletionTimeInstance)
    (j j' : Fin i.1.2.1.length) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the [SS18] instance is well-formed (`0 < m`, `1 ≤ n_j`,
processors in `{1, …, m}`, consecutive tasks of a job on different processors, `0 < K`),
`m = 2`, every task has length `1`, every arc names two jobs, no two distinct arcs share their
tail (at most one immediate successor) or their head (at most one immediate predecessor), and
the arcs have no cycle. -/
def WellFormed (i : TwoProcessorUnitJobShopChainsCompletionTimeInstance) : Prop :=
  JobShopScheduling.WellFormed i.1 ∧ i.1.1 = 2 ∧ (∀ job ∈ i.1.2.1, ∀ t ∈ job, t.1 = 1) ∧
    (∀ a ∈ i.2, a.1 < i.1.2.1.length ∧ a.2 < i.1.2.1.length) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.1 = b.1 → a = b) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.2 = b.2 → a = b) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- There is a job-shop schedule meeting the chains with total completion time at most
`K`: start times `σ` that are one-to-one on the tasks of each processor, such that a task of a
processor starting after another task `t'` of that processor starts no earlier than `t'`
finishes, each task of a job starts no earlier than the previous task of that job finishes, the
first task of a job starts no earlier than the last task of its immediate predecessor finishes,
and the completion times `C j` (the finishing times of the last tasks) sum to at most `K`. -/
def TwoProcessorUnitJobShopChainsCompletionTimeFeasible
    (i : TwoProcessorUnitJobShopChainsCompletionTimeInstance) : Prop :=
  ∃ σ : JobShopScheduling.Task i.1 → ℕ,
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t' < σ t →
      σ t' + taskLength i.1 t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.1.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    (∀ j j', Arc i j j' → ∀ (k : Fin (i.1.2.1.get j).length)
      (k' : Fin (i.1.2.1.get j').length), k.1 + 1 = (i.1.2.1.get j).length → k'.1 = 0 →
        σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j', k'⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩) ∧
      ∑ j, C j ≤ i.1.2.2

open Classical in
/-- TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS as a decision
problem over bitstrings. -/
noncomputable def twoProcessorUnitJobShopChainsCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitJobShopChainsCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitJobShopChainsCompletionTimeFeasible i)
  | none => false

/-- **TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS is
NP-complete.** Source: Timkovsky (1998); Brucker and Knust's classification
(`J2|chains; pᵢⱼ = 1|∑ Cᵢ`). -/
public theorem_wanted twoProcessorUnitJobShopChainsCompletionTime_npComplete :
    twoProcessorUnitJobShopChainsCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitJobShopChainsCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChainsCompletionTime
