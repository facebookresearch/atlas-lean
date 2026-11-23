/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUAL-PROCESSING-TIME WEIGHTED TARDINESS WITH RELEASE DATES (1|p_i=p;r_i|Σw_iT_i) is NP-complete

Source:
Z.-L. Chen and N. G. Hall, "Strong NP-hardness and approximation algorithm for weighted tardiness
with release dates and identical processing times", arXiv:2609.28751 (2026), Section 3 and
Theorem 1 (preprint);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `ein_ma` (single
machine problems), entry `1|p_i=p;r_i|Σw_iT_i` (listed as open).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EqualProcessingTimeReleaseWeightedTardiness

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# EQUAL-PROCESSING-TIME WEIGHTED TARDINESS WITH RELEASE DATES (1|p_i=p;r_i|Σw_iT_i) is NP-complete

INSTANCE: a common processing time `p ∈ ℤ⁺`; jobs `1, …, N`, each with a release date `r_j` and a
due date `d_j` (nonnegative integers) and a weight `w_j ∈ ℤ⁺`; and a nonnegative integer `K`.
QUESTION: is there a nonpreemptive schedule on one machine, job `j` processed during
`[s_j, s_j + p)` with `s_j ≥ r_j` and these intervals pairwise disjoint, whose total weighted
tardiness `∑_j w_j max{0, C_j - d_j}`, where `C_j = s_j + p`, is at most `K`?

This is the decision version of `1|r_j, p_j = p|∑ w_j T_j` as Chen and Hall (2026) state it in
their Section 3: `p` and the weights are positive integers, the release and due dates are
nonnegative integers, the common processing time is part of the instance, and the bound `K` is a
nonnegative integer. Their Theorem 1 proves it strongly NP-complete, by a reduction from MAX-CUT,
even when `d_j ≥ r_j + p` for every job. Brucker and Knust's classification (class `ein_ma`, last
updated 2006) lists the problem as open; the result is from a preprint.

Chen and Hall allow real start times and show (their left-shifting argument, equation (1)) that
every feasible schedule can be replaced by one with integral start times and no greater cost;
start times here are natural numbers. Since `p > 0`, pairwise disjoint intervals
`[s_j, s_j + p)` are Garey and Johnson's one-processor schedule ([SS1]: `σ` one-to-one, and
`σ(t) > σ(t')` implies `σ(t) ≥ σ(t') + l(t')`) with every length `l(t) = p`; the predicate
`IsOneProcessorSchedule` is reused from `SequencingToMinimizeWeightedTardinessWanted`.
Natural-number subtraction truncates at `0`, so `s_j + p - d_j` is the tardiness
`max{0, C_j - d_j}`. The jobs are `Fin N`, one per listed triple `(r_j, d_j, w_j)`. Binary
encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the common processing time `p`, the jobs, job `j` being the `j`-th triple
`(r_j, d_j, w_j)` of release date, due date and weight, and the bound `K`. -/
abbrev EqualProcessingTimeReleaseWeightedTardinessInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin N` for `N` listed triples. -/
abbrev Job (i : EqualProcessingTimeReleaseWeightedTardinessInstance) : Type :=
  Fin i.2.1.length

/-- The release date `r_j` of job `j`. -/
def release (i : EqualProcessingTimeReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.get j).1

/-- The due date `d_j` of job `j`. -/
def dueDate (i : EqualProcessingTimeReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.get j).2.1

/-- The weight `w_j` of job `j`. -/
def weight (i : EqualProcessingTimeReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.get j).2.2

/-- Well-formedness of an instance: the common processing time `p` and every weight are
positive. -/
def WellFormed (i : EqualProcessingTimeReleaseWeightedTardinessInstance) : Prop :=
  0 < i.1 ∧ ∀ x ∈ i.2.1, 0 < x.2.2

/-- Some one-processor schedule with every processing time equal to `p` starts every job no
earlier than its release date and has total weighted tardiness
`∑_j w_j (s_j + p - d_j)` (truncated subtraction) at most `K`. -/
def EqualProcessingTimeReleaseWeightedTardinessFeasible
    (i : EqualProcessingTimeReleaseWeightedTardinessInstance) : Prop :=
  ∃ s : Job i → ℕ, IsOneProcessorSchedule (fun _ => i.1) s ∧
    (∀ j, release i j ≤ s j) ∧
    ∑ j, weight i j * (s j + i.1 - dueDate i j) ≤ i.2.2

open Classical in
/-- EQUAL-PROCESSING-TIME WEIGHTED TARDINESS WITH RELEASE DATES as a decision problem over
bitstrings. -/
noncomputable def equalProcessingTimeReleaseWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EqualProcessingTimeReleaseWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ EqualProcessingTimeReleaseWeightedTardinessFeasible i)
  | none => false

/-- **EQUAL-PROCESSING-TIME WEIGHTED TARDINESS WITH RELEASE DATES (`1|p_i=p;r_i|Σw_iT_i`) is
NP-complete.** Source: Chen and Hall (2026), Theorem 1 (preprint). -/
public theorem_wanted equalProcessingTimeReleaseWeightedTardiness_npComplete :
    equalProcessingTimeReleaseWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equalProcessingTimeReleaseWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.EqualProcessingTimeReleaseWeightedTardiness
