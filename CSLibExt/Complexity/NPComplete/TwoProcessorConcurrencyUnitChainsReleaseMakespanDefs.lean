/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UET CONCURRENT TASK SCHEDULING WITH CHAINS AND RELEASE DATES: definitions

Source:
P. Brucker, S. Knust, D. Roper and Y. Zinder, "Scheduling UET task systems with concurrency on
two parallel identical processors", Mathematical Methods of Operations Research 52 (2000),
369-387, doi:10.1007/s001860000089 (the full text was not available to us);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 11.5
(`MPT2|chains; rᵢ; pᵢ = 1; sizeᵢ|C_max`, NP-hard in the strong sense, Brucker et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResourceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorConcurrencyUnitChainsReleaseMakespan

open ResourceConstrainedScheduling (Task req bound running)
open ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance PrecedenceWellFormed Prec)
open ResourceConstrainedSchedulingChainsUnitResource (IsChains)

/-- An instance: a RESOURCE CONSTRAINED SCHEDULING instance with a partial order (the numbers
`m` and `r`, the bounds, one requirement row per task, the deadline `D`, and the precedence
pairs) and the list of release dates, the `i`-th for task `i`. -/
abbrev TwoProcessorConcurrencyUnitChainsReleaseMakespanInstance :=
  PrecedenceResourceSchedulingInstance × List ℕ

/-- The release date `rᵢ` of task `i`. -/
def releaseDate (i : TwoProcessorConcurrencyUnitChainsReleaseMakespanInstance)
    (t : Task i.1.1) : ℕ :=
  i.2.getD t 0

/-- Well-formedness of an instance: it is well-formed for RESOURCE CONSTRAINED SCHEDULING with a
partial order, `m = 2`, `r = 1`, the resource (the processors) has bound `B₁ = 2`, every task's
size `R₁(i)` is `1` or `2`, the order is a set of chains, there is at least one task, and there
is one release date per task. -/
def WellFormed (i : TwoProcessorConcurrencyUnitChainsReleaseMakespanInstance) : Prop :=
  PrecedenceWellFormed i.1 ∧ i.1.1.1 = 2 ∧ i.1.1.2.1 = 1 ∧ bound i.1.1 0 = 2 ∧
    (∀ t : Task i.1.1, req i.1.1 t 0 = 1 ∨ req i.1.1 t 0 = 2) ∧ IsChains i.1 ∧
    i.1.1.2.2.2.1 ≠ [] ∧ i.2.length = i.1.1.2.2.2.1.length

/-- Some schedule of the unit-time tasks starts every task no earlier than its release date,
meets the deadline `D = K`, runs at most `m` tasks at a time, obeys the precedence constraints,
and at every time keeps the total size of the running tasks within the bound. -/
def TwoProcessorConcurrencyUnitChainsReleaseMakespanFeasible
    (i : TwoProcessorConcurrencyUnitChainsReleaseMakespanInstance) : Prop :=
  ∃ σ : Task i.1.1 → ℕ, (∀ t, releaseDate i t ≤ σ t) ∧ (∀ t, σ t + 1 ≤ i.1.1.2.2.2.2) ∧
    (∀ u, (running i.1.1 σ u).card ≤ i.1.1.1) ∧
    (∀ t t', Prec i.1 t t' → σ t + 1 ≤ σ t') ∧
    ∀ u, ∀ k < i.1.1.2.1, ∑ t ∈ running i.1.1 σ u, req i.1.1 t k ≤ bound i.1.1 k

open Classical in
/-- `P2|chains; rᵢ; pᵢ = 1; sizeᵢ|C_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorConcurrencyUnitChainsReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorConcurrencyUnitChainsReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorConcurrencyUnitChainsReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorConcurrencyUnitChainsReleaseMakespan
