/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES, UNIT CHAINS, NUMBER OF LATE JOBS `P2|chains;p_i=1|ΣU_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pqr_nop` (parallel machine
problems without preemption), entry `P2|chains;p_i=1|ΣU_i, ΣT_i` (minimal NP-hard in the strong
sense, justified by the single-machine problem);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (`1|chains, p_j = 1|ΣU_j`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TardyTasksUnitChainsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsLateJobs

open TardyTasksUnitChains (TardyTasksUnitChainsInstance Task deadline Prec ImmediatePredecessor)

/-!
# TWO PARALLEL MACHINES, UNIT CHAINS, NUMBER OF LATE JOBS `P2|chains;p_i=1|ΣU_i` is NP-complete

INSTANCE: two identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, each with processing time `p_i = 1` and a due date `d_i ∈ ℤ₀⁺`; a precedence relation
`→` on the jobs that is chain-like (each job has at most one immediate predecessor and at most
one immediate successor), where `i → j` means that `j` cannot start before `i` is completed; and
a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule in which at most `K` jobs are late
(`C_i > d_i` for the completion time `C_i` of job `i`)?

Brucker and Knust record `P2|chains;p_i=1|ΣU_i` as minimal NP-hard in the strong sense,
justified by the single-machine problem `1|chains;p_i=1|ΣU_i`, which Lenstra and Rinnooy Kan
prove NP-hard in the strong sense (Theorem 1).

Encoding. The jobs, due dates, precedence relation and bound are an instance of
`1|chains;p_j=1|ΣU_j` (`TardyTasksUnitChainsWanted`, Garey and Johnson's [SS2] with unit lengths and
chains): due dates listed one per job, and the pairs `(t, t')` with `t → t'`, which name jobs and
form a strict partial order whose every job has at most one immediate predecessor and at most one
immediate successor (`ImmediatePredecessor`). That module's well-formedness also asks for positive
due dates and `0 < K ≤ n` (from [SS2]), which this problem does not, so its remaining conditions are
stated here. The schedule gives each job a start time `σ(t)`, so `C_t = σ(t) + 1`; at every time at
most two jobs start (two identical machines; with unit jobs this is exactly when machines can be
assigned), and `t → t'` implies `σ(t) + 1 ≤ σ(t')`. Integer start times lose no generality for unit
jobs without release dates. Membership in NP is the certificate argument: moving every job that
starts after an idle time slot one unit earlier keeps the constraints and makes no job late that was
not, so start times below `n` suffice and are checked in polynomial time. Binary encoding of all
numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every listed pair names two jobs, the listed pairs form a
strict partial order, and the order consists of chains (every job has at most one immediate
predecessor and at most one immediate successor). Due dates and `K` are arbitrary natural
numbers. -/
def WellFormed (i : TardyTasksUnitChainsInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧ IsStrictOrder (Task i) (Prec i) ∧
    (∀ t a b, ImmediatePredecessor i a t → ImmediatePredecessor i b t → a = b) ∧
    ∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b

/-- Some two-machine schedule of the unit jobs (at most two start at each time `u`) obeys the
precedence constraints and has at most `K` late jobs, those with `σ(t) + 1 > d(t)`. -/
def TwoProcessorUnitChainsLateJobsFeasible (i : TardyTasksUnitChainsInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ 2) ∧
    (∀ t t', Prec i t t' → σ t + 1 ≤ σ t') ∧
    (Finset.univ.filter fun t => deadline i t < σ t + 1).card ≤ i.2.2

open Classical in
/-- `P2|chains;p_i=1|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TardyTasksUnitChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitChainsLateJobsFeasible i)
  | none => false

/-- **TWO PARALLEL MACHINES, UNIT CHAINS, NUMBER OF LATE JOBS `P2|chains;p_i=1|ΣU_i` is
NP-complete.** Source: Brucker and Knust, *Complexity results for scheduling problems*; Lenstra
and Rinnooy Kan (1980), Theorem 1, for `1|chains, p_j = 1|ΣU_j`. -/
public theorem_wanted twoProcessorUnitChainsLateJobs_npComplete :
    twoProcessorUnitChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsLateJobs
