/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES, UNIT CHAINS, TOTAL TARDINESS `P2|chains;p_i=1|ΣT_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pqr_nop` (parallel machine
problems without preemption), entry `P2|chains;p_i=1|ΣU_i, ΣT_i` (minimal NP-hard in the strong
sense, justified by the single-machine problem);
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, p_j = 1|ΣT_j` is NP-hard in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ChainsUnitTaskTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsTotalTardiness

open PrecedenceUnitTaskTardiness (PrecedenceUnitTaskTardinessInstance Prec)
open SequencingToMinimizeWeightedTardiness (Task taskLength weight deadline)
open ChainsUnitTaskTardiness (IsChainLike)

/-!
# TWO PARALLEL MACHINES, UNIT CHAINS, TOTAL TARDINESS `P2|chains;p_i=1|ΣT_i` is NP-complete

INSTANCE: two identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, each with processing time `p_i = 1` and a due date `d_i ∈ ℤ₀⁺`; a precedence relation
`→` on the jobs that is chain-like (each job has at most one immediate predecessor and at most
one immediate successor), where `i → j` means that `j` cannot start before `i` is completed; and
a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule with total tardiness `∑_i T_i ≤ K`, where
`T_i = max(0, C_i - d_i)` for the completion time `C_i` of job `i`?

Brucker and Knust record `P2|chains;p_i=1|ΣT_i` as minimal NP-hard in the strong sense,
justified by the single-machine problem `1|chains;p_i=1|ΣT_i`, which Leung and Young prove
NP-hard in the strong sense.

Encoding. The jobs, due dates, precedence relation and bound are an instance of
`1|chains;p_j=1|ΣT_j` (`ChainsUnitTaskTardinessWanted`): jobs are listed one per entry as
`(l, w, d)` triples with length and weight `1`, and the pairs `(t, t')` with `t → t'` name jobs and
form a strict partial order that is chain-like (`IsChainLike`). That module's well-formedness also
asks for positive due dates and `0 < K` (from Garey and Johnson's [SS5]), which this problem does
not, so its remaining conditions are stated here. Its tardiness sum (over the late jobs,
`(σ(t) + l(t) - d(t)) · w(t)`) is reused as well. The schedule gives each job a start time `σ(t)`;
at every time at most two jobs are in process (two identical machines; with unit jobs this is
exactly when machines can be assigned), and `t → t'` implies `σ(t) + 1 ≤ σ(t')`. Integer start times
lose no generality for unit jobs without release dates. Membership in NP is the certificate
argument: moving every job that starts after an idle time slot one unit earlier keeps the
constraints and increases no completion time, so start times below `n` suffice and are checked in
polynomial time. Binary encoding of all numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every job has length and weight `1`, every listed pair names
two jobs, the listed pairs form a strict partial order, and the order is chain-like. Due dates
and `K` are arbitrary natural numbers. -/
def WellFormed (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  (∀ x ∈ i.1.1, x.1 = 1 ∧ x.2.1 = 1) ∧
    (∀ p ∈ i.2, p.1 < i.1.1.length ∧ p.2 < i.1.1.length) ∧
    IsStrictOrder (Task i.1) (Prec i) ∧ IsChainLike i

/-- Some two-machine schedule (at every time `u` at most two jobs with `σ(t) ≤ u < σ(t) + l(t)`)
obeys the precedence constraints and has total tardiness at most `K`: the sum, over the jobs with
`σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is at most `K`. -/
def TwoProcessorUnitChainsTotalTardinessFeasible (i : PrecedenceUnitTaskTardinessInstance) :
    Prop :=
  ∃ σ : Task i.1 → ℕ,
    (∀ u, (Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + taskLength i.1 t).card ≤ 2) ∧
    (∀ t t', Prec i t t' → σ t + taskLength i.1 t ≤ σ t') ∧
    ∑ t ∈ Finset.univ.filter (fun t => deadline i.1 t < σ t + taskLength i.1 t),
      (σ t + taskLength i.1 t - deadline i.1 t) * weight i.1 t ≤ i.1.2

open Classical in
/-- `P2|chains;p_i=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitChainsTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitTaskTardinessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitChainsTotalTardinessFeasible i)
  | none => false

/-- **TWO PARALLEL MACHINES, UNIT CHAINS, TOTAL TARDINESS `P2|chains;p_i=1|ΣT_i` is
NP-complete.** Source: Brucker and Knust, *Complexity results for scheduling problems*; Leung
and Young (1990) for `1|chains, p_j = 1|ΣT_j`. -/
public theorem_wanted twoProcessorUnitChainsTotalTardiness_npComplete :
    twoProcessorUnitChainsTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitChainsTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsTotalTardiness
