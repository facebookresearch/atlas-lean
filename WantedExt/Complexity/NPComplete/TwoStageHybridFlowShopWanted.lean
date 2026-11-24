/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-STAGE HYBRID FLOW SHOP is NP-complete

Source:
J. N. D. Gupta, "Two-stage, hybrid flowshop scheduling problem", Journal of the Operational
Research Society 39 (1988), 359-364, doi:10.1057/jors.1988.63 (the model; NP-completeness of the
two-stage problem with identical parallel machines at each stage);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP12] PARTITION (NP-hardness of the restriction
stated here, by the reduction in the module docstring).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoStageHybridFlowShop

/-!
# TWO-STAGE HYBRID FLOW SHOP is NP-complete

INSTANCE: two stages in series, stage 1 with two identical parallel machines and stage 2 with
one machine; jobs `1, …, n`, job `j` with stage-1 processing time `a_j ∈ ℤ⁺` and stage-2
processing time `b_j ∈ ℤ⁺`; and a bound `K`.
QUESTION: is there a nonpreemptive schedule, in which each job is processed at stage 1 on one of
the two machines and then at stage 2, whose makespan is at most `K`?

In the notation of the hybrid flow-shop literature this is `F2(P2, P1)||C_max`. A schedule assigns
each job a stage-1 machine `μ_j ∈ {0, 1}` and start times `s₁_j` (stage 1) and `s₂_j` (stage 2)
in `ℤ₀⁺`; each machine processes one job at a time, so two distinct jobs on the same stage-1
machine occupy disjoint intervals `[s₁, s₁ + a)`, and two distinct jobs occupy disjoint intervals
`[s₂, s₂ + b)` on the stage-2 machine; a job starts stage 2 no earlier than it finishes stage 1;
and every job finishes stage 2 by `K`.

Gupta proves NP-completeness for two-stage hybrid flow shops with identical parallel machines at
each stage. For the restriction stated here (two machines at stage 1, one at stage 2, positive
times), NP-hardness follows from PARTITION ([SP12]): for positive `x_1, …, x_n` with sum `2B`,
take `M = 2n + 1`, jobs `(a_j, b_j) = (M x_j, 1)` and `K = MB + 2`. A partition gives each
stage-1 machine load `MB`; the stage-1 completions are multiples of `M`, at most two per instant,
so the stage-2 machine finishes each arrival before the next one and is done by `MB + 2`.
Conversely, every job finishes stage 1 by `K - 1 = MB + 1`, so each stage-1 load is a multiple
of `M` that is at most `MB + 1`; both loads equal `MB`, which is a partition. Times are written in
binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs, job `j` given as `(a_j, b_j)` (stage-1 and stage-2 processing
times), and the bound `K` on the makespan. -/
abbrev TwoStageHybridFlowShopInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: all processing times are positive. -/
def WellFormed (i : TwoStageHybridFlowShopInstance) : Prop :=
  ∀ job ∈ i.1, 0 < job.1 ∧ 0 < job.2

/-- There is a nonpreemptive schedule with makespan at most `K`: a stage-1 machine `μ j` for
every job and start times `s₁ j`, `s₂ j` such that distinct jobs on the same stage-1 machine
and distinct jobs at stage 2 occupy disjoint intervals, each job starts stage 2 after finishing
stage 1, and every job finishes stage 2 by `K`. -/
def TwoStageHybridFlowShopFeasible (i : TwoStageHybridFlowShopInstance) : Prop :=
  ∃ (μ : Fin i.1.length → Fin 2) (s₁ s₂ : Fin i.1.length → ℕ),
    (∀ j k, j ≠ k → μ j = μ k →
      s₁ j + (i.1.get j).1 ≤ s₁ k ∨ s₁ k + (i.1.get k).1 ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + (i.1.get j).2 ≤ s₂ k ∨ s₂ k + (i.1.get k).2 ≤ s₂ j) ∧
    (∀ j, s₁ j + (i.1.get j).1 ≤ s₂ j) ∧
    ∀ j, s₂ j + (i.1.get j).2 ≤ i.2

open Classical in
/-- TWO-STAGE HYBRID FLOW SHOP as a decision problem over bitstrings. -/
noncomputable def twoStageHybridFlowShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoStageHybridFlowShopInstance) x with
  | some i => decide (WellFormed i ∧ TwoStageHybridFlowShopFeasible i)
  | none => false

/-- **TWO-STAGE HYBRID FLOW SHOP is NP-complete.** Source: Gupta (1988) (model); Garey and
Johnson (1979), [SP12] (reduction in the module docstring). -/
public theorem_wanted twoStageHybridFlowShop_npComplete :
    twoStageHybridFlowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoStageHybridFlowShopDec

end MetaMathlibExt.Complexity.NPComplete.TwoStageHybridFlowShop
