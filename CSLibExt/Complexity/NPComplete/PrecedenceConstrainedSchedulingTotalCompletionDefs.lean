/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING with total completion time (`P|prec;p_i=1|ΣC_i`) is: definitions
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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task taskLength Prec running WellFormed)

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

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletion
