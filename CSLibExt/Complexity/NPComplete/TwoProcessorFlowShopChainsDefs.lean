/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS: definitions

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 4(h) in the preprint, Mathematisch Centrum report BW 43/75 (1975),
https://ir.cwi.nl/pub/9725 (KNAPSACK reduces to `n|2|F,tree|Cmax`; the constructed instance has
the single precedence pair `J_{n-1} < J_n`, so it is a chain instance: `F2|chains|Cmax`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems without preemption" (`F2|chains|Cmax`, minimal NP-hard, credited to
Lenstra, Rinnooy Kan, and Brucker 1977);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING, p. 241
(the parent problem; solvable in polynomial time for `m = 2` without precedence constraints).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopChains

/-- An instance: the [SS15] instance of `FlowShopSchedulingWanted` (the number of processors
`m`, one list of task lengths per job, and the deadline `D`), and the arcs `(j, k)` of the
chains, `j` the immediate predecessor of `k`. -/
abbrev TwoProcessorFlowShopChainsInstance :=
  FlowShopScheduling.FlowShopSchedulingInstance × List (ℕ × ℕ)

/-- The arc relation of the chains: `j` is the immediate predecessor of `k` when the pair
`(j, k)` is listed. -/
def Arc (i : TwoProcessorFlowShopChainsInstance) (j k : Fin i.1.2.1.length) : Prop :=
  ((j : ℕ), (k : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the [SS15] instance is well-formed (`0 < m`, every job has
`m` tasks, `0 < D`), `m = 2`, every arc names two jobs, no two distinct arcs share their tail
(at most one immediate successor) or their head (at most one immediate predecessor), and the
arcs have no cycle. -/
def WellFormed (i : TwoProcessorFlowShopChainsInstance) : Prop :=
  FlowShopScheduling.WellFormed i.1 ∧ i.1.1 = 2 ∧
    (∀ a ∈ i.2, a.1 < i.1.2.1.length ∧ a.2 < i.1.2.1.length) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.1 = b.1 → a = b) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.2 = b.2 → a = b) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- Some schedule `σ p j` (start of job `j`'s task on processor `p`) ends every task by `D`,
runs one task at a time on each processor, runs each job's tasks in processor order, and starts
job `k` (its task on the first processor) no earlier than the completion of its immediate
predecessor `j` (of `j`'s task on the last processor). -/
def TwoProcessorFlowShopChainsFeasible (i : TwoProcessorFlowShopChainsInstance) : Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ,
    (∀ p j, σ p j + FlowShopScheduling.len i.1 p j ≤ i.1.2.2) ∧
    (∀ p j k, j ≠ k →
      σ p j + FlowShopScheduling.len i.1 p j ≤ σ p k ∨
        σ p k + FlowShopScheduling.len i.1 p k ≤ σ p j) ∧
    (∀ (p : Fin i.1.1) (hp : p.1 + 1 < i.1.1) j,
      σ p j + FlowShopScheduling.len i.1 p j ≤ σ ⟨p.1 + 1, hp⟩ j) ∧
    ∀ j k, Arc i j k → ∀ p q : Fin i.1.1, p.1 + 1 = i.1.1 → q.1 = 0 →
      σ p j + FlowShopScheduling.len i.1 p j ≤ σ q k

open Classical in
/-- TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS as a decision problem
over bitstrings. -/
noncomputable def twoProcessorFlowShopChainsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFlowShopChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFlowShopChainsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopChains
