/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-MODE RCPSP FEASIBILITY (NONRENEWABLE RESOURCES): definitions

Source:
R. Kolisch and A. Drexl, "Local search for nonpreemptive multi-mode resource-constrained
project scheduling", IIE Transactions 29 (1997), 987-999, doi:10.1080/07408179708966417;
S. Hartmann, "Project scheduling with multiple modes: a genetic algorithm", Annals of
Operations Research 102 (2001), 111-135, doi:10.1023/A:1010902015091, Sections 2 and 3.3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiModeRcpspFeasibility

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

end MetaMathlibExt.Complexity.NPComplete.MultiModeRcpspFeasibility
