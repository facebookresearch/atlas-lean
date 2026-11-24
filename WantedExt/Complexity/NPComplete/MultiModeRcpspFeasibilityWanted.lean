/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-MODE RCPSP FEASIBILITY (NONRENEWABLE RESOURCES) is NP-complete

Source:
R. Kolisch and A. Drexl, "Local search for nonpreemptive multi-mode resource-constrained
project scheduling", IIE Transactions 29 (1997), 987-999, doi:10.1080/07408179708966417;
S. Hartmann, "Project scheduling with multiple modes: a genetic algorithm", Annals of
Operations Research 102 (2001), 111-135, doi:10.1023/A:1010902015091, Sections 2 and 3.3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiModeRcpspFeasibility

/-!
# MULTI-MODE RCPSP FEASIBILITY (NONRENEWABLE RESOURCES) is NP-complete

INSTANCE: `K ≥ 2` nonrenewable resources with availabilities `R_1, …, R_K`, and activities
`1, …, J`, each with a nonempty finite set of execution modes; mode `m` of activity `j`
consumes `r_{jmk}` units of resource `k`.
QUESTION: is there a mode assignment `μ` (one mode `μ(j)` per activity) whose total
consumption `∑_j r_{j μ(j) k}` of every resource `k` is at most `R_k`?

This is the mode-assignment problem of the multi-mode resource-constrained project scheduling
problem (MRCPSP); Kolisch and Drexl prove it NP-complete when there are at least two
nonrenewable resources (as recorded by Hartmann, Section 3.3). The MRCPSP assumes without loss
of generality that every mode's renewable requests are within the per-period availabilities
(Hartmann, Section 2), so every mode assignment meeting the nonrenewable availabilities extends
to a feasible schedule; mode durations, precedence relations and renewable resources therefore
do not enter the question and are omitted. With a single nonrenewable
resource the problem is polynomial (choose the cheapest mode of every activity), so `K ≥ 2`
is part of the instance class. Resources and modes are numbered from `0` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `K` of nonrenewable resources, the activities, each a list of
modes, each mode the list `[r_{jm0}, …, r_{jm(K-1)}]` of its consumptions, and the list
`[R_0, …, R_{K-1}]` of availabilities. -/
abbrev MultiModeRcpspFeasibilityInstance := ℕ × List (List (List ℕ)) × List ℕ

/-- Well-formedness of an instance: `K ≥ 2`, there are `K` availabilities, every activity has
at least one mode, and every mode lists `K` consumptions. -/
def WellFormed (i : MultiModeRcpspFeasibilityInstance) : Prop :=
  2 ≤ i.1 ∧ i.2.2.length = i.1 ∧ ∀ act ∈ i.2.1, act ≠ [] ∧ ∀ m ∈ act, m.length = i.1

/-- There is a mode assignment `μ`, `μ j` a mode of activity `j`, whose total consumption of
every resource `k` is at most its availability `R_k`. -/
def MultiModeRcpspFeasibilityFeasible (i : MultiModeRcpspFeasibilityInstance) : Prop :=
  ∃ μ : Fin i.2.1.length → ℕ, (∀ j, μ j < (i.2.1.get j).length) ∧
    ∀ k < i.1, ∑ j, ((i.2.1.get j).getD (μ j) []).getD k 0 ≤ i.2.2.getD k 0

open Classical in
/-- MULTI-MODE RCPSP FEASIBILITY (NONRENEWABLE RESOURCES) as a decision problem over
bitstrings. -/
noncomputable def multiModeRcpspFeasibilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiModeRcpspFeasibilityInstance) x with
  | some i => decide (WellFormed i ∧ MultiModeRcpspFeasibilityFeasible i)
  | none => false

/-- **MULTI-MODE RCPSP FEASIBILITY (NONRENEWABLE RESOURCES) is NP-complete.** Source: Kolisch
and Drexl (1997); Hartmann (2001). -/
public theorem_wanted multiModeRcpspFeasibility_npComplete :
    multiModeRcpspFeasibilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiModeRcpspFeasibilityDec

end MetaMathlibExt.Complexity.NPComplete.MultiModeRcpspFeasibility
