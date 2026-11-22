/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(`J2|chains, pᵢⱼ = 1, no-wait|C_max` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Job-shop problems with no-wait" (`J2|chains; pᵢⱼ = 1; no-wait|C_max`, minimal NP-hard,
credited to Timkovsky 1998);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChains

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1` and with a processor
`p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])`, a precedence relation on `J` consisting of
disjoint chains (each job has at most one immediate predecessor and at most one immediate
successor), and a deadline `D ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` that meets
the overall deadline (makespan `C_max ≤ D`), in which every task of a job starts exactly when
the previous task of that job finishes (no wait), and in which, whenever `j` precedes `j'`,
the first task of `j'` starts no earlier than the last task of `j` finishes?

This is `J2|chains; pᵢⱼ = 1; no-wait|C_max`: JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingWanted`)
with `m = 2`, unit task lengths, the no-wait condition and chain precedence constraints between
jobs. Timkovsky (1998) proves it NP-hard in the strong sense with his job-shopping theorem, a
reduction of nonpreemptive identical parallel machines to no-wait unit-time job shops. The instance
type `JobShopScheduling.JobShopSchedulingInstance`, `JobShopScheduling.WellFormed` (which includes
`n_j ≥ 1`), the tasks and their lengths and processors are the parent's, and so are the schedule
conditions (one-to-one start times on each processor, one task at a time on each processor, every
job finished by `D`), except that the parent's job-order condition `σ(t_{k+1}[j]) ≥ σ(t_k[j]) +
l(t_k[j])` is strengthened to equality (no wait). Unit lengths are a well-formedness condition.

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

/-- An instance: the [SS18] instance of `JobShopSchedulingWanted` (the number of processors,
the jobs as lists of `(l(t), p(t))` pairs, and the deadline `D`), and the arcs `(j, j')` of the
chains, `j` the immediate predecessor of `j'`. -/
abbrev TwoProcessorUnitNoWaitJobShopChainsInstance := JobShopSchedulingInstance × List (ℕ × ℕ)

/-- The arc relation of the chains: `j` is the immediate predecessor of `j'` when the pair
`(j, j')` is listed. -/
def Arc (i : TwoProcessorUnitNoWaitJobShopChainsInstance) (j j' : Fin i.1.2.1.length) :
    Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the [SS18] instance is well-formed (`0 < m`, `1 ≤ n_j`,
processors in `{1, …, m}`, consecutive tasks of a job on different processors, `0 < D`),
`m = 2`, every task has length `1`, every arc names two jobs, no two distinct arcs share their
tail (at most one immediate successor) or their head (at most one immediate predecessor), and
the arcs have no cycle. -/
def WellFormed (i : TwoProcessorUnitNoWaitJobShopChainsInstance) : Prop :=
  JobShopScheduling.WellFormed i.1 ∧ i.1.1 = 2 ∧ (∀ job ∈ i.1.2.1, ∀ t ∈ job, t.1 = 1) ∧
    (∀ a ∈ i.2, a.1 < i.1.2.1.length ∧ a.2 < i.1.2.1.length) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.1 = b.1 → a = b) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.2 = b.2 → a = b) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- There is a no-wait job-shop schedule meeting the deadline and the chains: start times `σ`
that are one-to-one on the tasks of each processor, such that a task of a processor starting
after another task `t'` of that processor starts no earlier than `t'` finishes, each task of a
job starts exactly when the previous task of that job finishes, the last task of every job
finishes by `D`, and the first task of a job starts no earlier than the last task of its
immediate predecessor finishes. -/
def TwoProcessorUnitNoWaitJobShopChainsFeasible
    (i : TwoProcessorUnitNoWaitJobShopChainsInstance) : Prop :=
  ∃ σ : JobShopScheduling.Task i.1 → ℕ,
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t' < σ t →
      σ t' + taskLength i.1 t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.1.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k'⟩ = σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩) ∧
    (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
      σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ i.1.2.2) ∧
    ∀ j j', Arc i j j' → ∀ (k : Fin (i.1.2.1.get j).length) (k' : Fin (i.1.2.1.get j').length),
      k.1 + 1 = (i.1.2.1.get j).length → k'.1 = 0 →
        σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j', k'⟩

open Classical in
/-- TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS as a decision problem over
bitstrings. -/
noncomputable def twoProcessorUnitNoWaitJobShopChainsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitNoWaitJobShopChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitNoWaitJobShopChainsFeasible i)
  | none => false

/-- **TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS is NP-complete.** Source:
Timkovsky (1998); Brucker and Knust's classification (`J2|chains; pᵢⱼ = 1; no-wait|C_max`). -/
public theorem_wanted twoProcessorUnitNoWaitJobShopChains_npComplete :
    twoProcessorUnitNoWaitJobShopChainsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitNoWaitJobShopChainsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChains
