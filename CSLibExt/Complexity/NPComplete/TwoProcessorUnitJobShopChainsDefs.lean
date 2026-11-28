/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB SHOP J2|chains;p_ij=1|Cmax: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChainsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChains

open JobShopScheduling (taskLength taskProcessor)

/-- An instance: the [SS18] instance of `JobShopSchedulingDefs` (the number of processors, the
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

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChains
