/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB SHOP J2|chains;p_ij=1|Cmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Job-shop problems without preemption" (`J2|chains; pᵢⱼ = 1|C_max`, minimal NP-hard in the
strong sense, credited to V. G. Timkovsky, "On the complexity of scheduling an arbitrary system",
Soviet Journal of Computer and Systems Sciences 23(5) (1985), 46-52; that paper was not
available);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted
public import WantedExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChainsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChains

open JobShopScheduling (taskLength taskProcessor)

/-!
# JOB SHOP J2|chains;p_ij=1|Cmax is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1` and with a processor
`p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])`, a precedence relation on `J` consisting of
disjoint chains (each job has at most one immediate predecessor and at most one immediate
successor), and a deadline `D ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` that meets
the overall deadline (makespan `C_max ≤ D`) in which, whenever `j` precedes `j'`, the first task
of `j'` starts no earlier than the last task of `j` finishes?

This is Brucker and Knust's `J2|chains; pᵢⱼ = 1|C_max`, which they classify as NP-hard in the
strong sense, citing Timkovsky (1985). It is JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingWanted`)
with `m = 2`, unit task lengths and chain precedence constraints between jobs, and it is the
no-wait problem `J2|chains; pᵢⱼ = 1; no-wait|C_max` (`TwoProcessorUnitNoWaitJobShopChainsWanted`)
without the no-wait condition. The instance type (the [SS18] instance and the chain arcs `(j, j')`,
`j` the immediate predecessor of `j'`), the arc relation `Arc` and the well-formedness (the [SS18]
instance well-formed, which includes `n_j ≥ 1`, `m = 2`, unit lengths, every arc naming two jobs,
no two arcs with the same tail or the same head, no cycle) are that module's; no-wait is a
schedule condition, not instance data, and they are exposed here under this problem's names. The
schedule conditions are the parent's (one-to-one start times on each processor, one task at a
time on each processor, each task of a job starting no earlier than the previous task of that job
finishes, the last task of every job finishing by `D`), plus the chain condition on every arc;
on the rest of the transitive closure of the arcs it follows, since every job starts its first
task before it finishes its last. Task positions are numbered from `0`. Membership in NP is the
certificate argument: the start times, each below `D`, are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the [SS18] instance of `JobShopSchedulingWanted` (the number of processors, the
jobs as lists of `(l(t), p(t))` pairs, and the deadline `D`), and the arcs `(j, j')` of the
chains, `j` the immediate predecessor of `j'` (the instance type of
`TwoProcessorUnitNoWaitJobShopChainsWanted`). -/
abbrev TwoProcessorUnitJobShopChainsInstance :=
  TwoProcessorUnitNoWaitJobShopChains.TwoProcessorUnitNoWaitJobShopChainsInstance

/-- The arc relation of the chains: `j` is the immediate predecessor of `j'` when the pair
`(j, j')` is listed (`TwoProcessorUnitNoWaitJobShopChains.Arc`). -/
abbrev Arc (i : TwoProcessorUnitJobShopChainsInstance) (j j' : Fin i.1.2.1.length) : Prop :=
  TwoProcessorUnitNoWaitJobShopChains.Arc i j j'

/-- Well-formedness of an instance (`TwoProcessorUnitNoWaitJobShopChains.WellFormed`): the [SS18]
instance is well-formed (`0 < m`, `1 ≤ n_j`, processors in `{1, …, m}`, consecutive tasks of a job
on different processors, `0 < D`), `m = 2`, every task has length `1`, every arc names two jobs,
no two distinct arcs share their tail or their head, and the arcs have no cycle. -/
abbrev WellFormed (i : TwoProcessorUnitJobShopChainsInstance) : Prop :=
  TwoProcessorUnitNoWaitJobShopChains.WellFormed i

/-- There is a job-shop schedule meeting the deadline and the chains: start times `σ` that are
one-to-one on the tasks of each processor, such that a task of a processor starting after another
task `t'` of that processor starts no earlier than `t'` finishes, each task of a job starts no
earlier than the previous task of that job finishes, the last task of every job finishes by `D`,
and the first task of a job starts no earlier than the last task of its immediate predecessor
finishes. -/
def TwoProcessorUnitJobShopChainsFeasible (i : TwoProcessorUnitJobShopChainsInstance) :
    Prop :=
  ∃ σ : JobShopScheduling.Task i.1 → ℕ,
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t' < σ t →
      σ t' + taskLength i.1 t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.1.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
      σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ i.1.2.2) ∧
    ∀ j j', Arc i j j' → ∀ (k : Fin (i.1.2.1.get j).length) (k' : Fin (i.1.2.1.get j').length),
      k.1 + 1 = (i.1.2.1.get j).length → k'.1 = 0 →
        σ ⟨j, k⟩ + taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j', k'⟩

open Classical in
/-- JOB SHOP J2|chains;p_ij=1|Cmax as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitJobShopChainsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitJobShopChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitJobShopChainsFeasible i)
  | none => false

/-- **JOB SHOP J2|chains;p_ij=1|Cmax is NP-complete.** Source: Brucker and Knust's
classification (`J2|chains; pᵢⱼ = 1|C_max`, strongly NP-hard), citing Timkovsky (1985). -/
public theorem_wanted twoProcessorUnitJobShopChains_npComplete :
    twoProcessorUnitJobShopChainsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitJobShopChainsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChains
