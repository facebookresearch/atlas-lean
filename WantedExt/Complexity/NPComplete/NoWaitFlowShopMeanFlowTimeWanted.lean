/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT FLOW-SHOP MEAN FLOW TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: with a bound `K` on the sum of the completion times in place of the deadline,
the problem is NP-complete in the strong sense for `m` arbitrary);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine
scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.NoWaitFlowShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopMeanFlowTime

/-!
# NO-WAIT FLOW-SHOP MEAN FLOW TIME is NP-complete

INSTANCE: a number `m ∈ ℤ⁺` of processors, a set `J` of jobs, each job `j ∈ J` consisting of
`m` tasks `t₁[j], …, tₘ[j]` (with `tᵢ[j]` to be executed by processor `i`), a length
`l(t) ∈ ℤ₀⁺` for each such task `t`, and a bound `K ∈ ℤ⁺`. QUESTION: is there a flow-shop
schedule for `J` with the property that, for each `j ∈ J` and `1 ≤ i < m`,
`σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`, such that the sum, over all `j ∈ J`, of `σₘ(j) + l(tₘ[j])` is at
most `K`?

This is NO-WAIT FLOW-SHOP SCHEDULING ([SS16], `NoWaitFlowShopSchedulingWanted`) with the goal
of meeting the overall deadline replaced by a bound `K` on the sum of the jobs' completion
times (Garey and Johnson's comment to [SS16]; the mean flow time is that sum divided by `|J|`).
The instance type, `NoWaitFlowShopScheduling.WellFormed`, `NoWaitFlowShopScheduling.taskLength`
and the flow-shop schedule `NoWaitFlowShopScheduling.IsFlowShopSchedule` are the parent's; the
last component of the instance is the bound `K ∈ ℤ⁺` in place of the deadline `D ∈ ℤ⁺`. The
parent's schedule predicate carries the deadline condition `σ p j + l(t_p[j]) ≤ K` for every
task; with the no-wait condition every task of job `j` finishes by `σₘ(j) + l(tₘ[j])`, which is
at most the sum over all jobs, so under the sum bound this condition is implied and the question
is the source's. The last processor `p` is the one with `p + 1 = m`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- There is a no-wait flow-shop schedule (each job's task on processor `p + 1` starts exactly
when its task on processor `p` finishes) whose sum over all jobs of the completion times on
the last processor is at most `K`. -/
def NoWaitFlowShopMeanFlowTimeFeasible
    (i : NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, NoWaitFlowShopScheduling.IsFlowShopSchedule i σ ∧
    (∀ j p q, q.1 = p.1 + 1 → σ q j = σ p j + NoWaitFlowShopScheduling.taskLength i p j) ∧
    ∀ p : Fin i.1, p.1 + 1 = i.1 →
      ∑ j, (σ p j + NoWaitFlowShopScheduling.taskLength i p j) ≤ i.2.2

open Classical in
/-- NO-WAIT FLOW-SHOP MEAN FLOW TIME as a decision problem over bitstrings. -/
noncomputable def noWaitFlowShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (NoWaitFlowShopScheduling.WellFormed i ∧
      NoWaitFlowShopMeanFlowTimeFeasible i)
  | none => false

/-- **NO-WAIT FLOW-SHOP MEAN FLOW TIME is NP-complete.** Source: Garey and Johnson (1979),
[SS16], comment; Lenstra, Rinnooy Kan, and Brucker (1977). -/
public theorem_wanted noWaitFlowShopMeanFlowTime_npComplete :
    noWaitFlowShopMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L noWaitFlowShopMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopMeanFlowTime
