/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM K-SATISFIABILITY is NP-complete for every fixed k ≥ 2: definitions

Source:
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1
(MAXIMUM 2-SATISFIABILITY);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO5] MAXIMUM 2-SATISFIABILITY;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MAXIMUM K-SATISFIABILITY.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumKSatisfiability

open MaxSat (MaxSatInstance MaxSatFeasible)

/-- Well-formedness of an instance for the constant `k`: a well-formed MAXIMUM SATISFIABILITY
instance (variables below the variable count) in which every clause has at most `k` literals,
and `0 < K`. -/
def WellFormed (k : ℕ) (i : MaxSatInstance) : Prop :=
  MaxSat.WellFormed i ∧ (∀ clause ∈ i.2.1, clause.length ≤ k) ∧ 0 < i.2.2

open Classical in
/-- MAXIMUM K-SATISFIABILITY for the constant `k` as a decision problem over bitstrings. -/
noncomputable def maximumKSatisfiabilityDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxSatInstance) x with
  | some i => decide (WellFormed k i ∧ MaxSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumKSatisfiability
