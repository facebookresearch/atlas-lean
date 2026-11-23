/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING with total completion time (`P|prec;p_i=1|ΣC_i`) is
NP-complete

Source:
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
R. L. Graham, E. L. Lawler, J. K. Lenstra and A. H. G. Rinnooy Kan, "Optimization and
approximation in deterministic sequencing and scheduling: a survey", Annals of Discrete
Mathematics 5 (1979), 287-326, doi:10.1016/S0167-5060(08)70356-X, Section 4.2.2 ("`P|prec,
p_j=1|ΣC_j` is NP-hard [Lenstra & Rinnooy Kan]");
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
classes "Parallel machine problems" (`P|prec;p_i=1|ΣC_i`, minimal NP-hard in the strong sense,
citing Lenstra and Rinnooy Kan 1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task taskLength Prec running WellFormed)

/-!
# PRECEDENCE CONSTRAINED SCHEDULING with total completion time is NP-complete

INSTANCE: `m` identical parallel machines (`m` part of the input), each processing at most one
job at a time; jobs `1, …, n`, each with unit processing time `p_i = 1`; a precedence relation
on the jobs (a partial order: if `i` precedes `j`, then `j` cannot start before `i` is
completed); and an integer bound `K`. QUESTION: is there a feasible schedule whose total
completion time `Σ_i C_i` is at most `K`, where `C_i` is the completion time of job `i`?

This is `P|prec;p_i=1|ΣC_i` in the three-field notation. The instance data are those of
PRECEDENCE CONSTRAINED SCHEDULING ([SS9], `PrecedenceConstrainedSchedulingWanted`, the same
machines, unit jobs and precedence relation with a common deadline in place of the bound on
`Σ_i C_i`), reused unchanged: the job lengths (all `1`), `m`, the listed pairs `(t, t')` with
`t` preceding `t'`, and a last number, here the bound `K`. Its well-formedness is reused as
well: unit lengths, `m > 0`, the listed pairs name jobs and form a strict partial order, and
`K > 0`. A schedule gives each job `t` a start time `σ(t)`; at most `m` jobs run at any time
(identical machines, one job per machine at a time), precedence means `σ(t) + 1 ≤ σ(t')`, and
`C_t = σ(t) + 1`. Integral start times lose no generality for unit jobs. Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some schedule on `m` identical machines that obeys the precedence constraints has total
completion time `Σ_t (σ(t) + l(t))` at most `K`. -/
def PrecedenceConstrainedSchedulingTotalCompletionFeasible
    (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running i σ u).card ≤ i.2.1) ∧
    (∀ t t', Prec i t t' → σ t + taskLength i t ≤ σ t') ∧
    (∑ t, (σ t + taskLength i t)) ≤ i.2.2.2

open Classical in
/-- `P|prec;p_i=1|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def precedenceConstrainedSchedulingTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingTotalCompletionFeasible i)
  | none => false

/-- **PRECEDENCE CONSTRAINED SCHEDULING with total completion time (`P|prec;p_i=1|ΣC_i`) is
NP-complete.** Source: Lenstra and Rinnooy Kan (1978); Graham, Lawler, Lenstra and Rinnooy Kan
(1979), Section 4.2.2. -/
public theorem_wanted precedenceConstrainedSchedulingTotalCompletion_npComplete :
    precedenceConstrainedSchedulingTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSchedulingTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletion
