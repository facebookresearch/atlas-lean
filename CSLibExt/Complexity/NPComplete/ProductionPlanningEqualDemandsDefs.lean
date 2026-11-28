/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRODUCTION PLANNING with equal demands, equal set-up costs and no inventory costs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 243, problem [SS21] PRODUCTION
PLANNING, comment: "remains NP-complete even if all demands are equal, all set-up costs are
equal, and all inventory costs are 0";
M. Florian, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Deterministic production
planning: algorithms and complexity", Management Science 26 (1980), 669-679,
doi:10.1287/mnsc.26.7.669 (cited by Garey and Johnson as [Lenstra, Rinnooy Kan, and Florian,
1978]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ProductionPlanningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProductionPlanningEqualDemands

open MetaMathlibExt.Complexity.NPComplete.ProductionPlanning

/-- Well-formedness of an instance of the restriction: the instance is a well-formed PRODUCTION
PLANNING instance, all periods have the same demand and the same set-up cost, and every
inventory cost coefficient is `0`. -/
def RestrictedWellFormed (i : ProductionPlanningInstance) : Prop :=
  WellFormed i ∧ (∀ p ∈ i.2.1, ∀ q ∈ i.2.1, p.1 = q.1 ∧ p.2.2.1 = q.2.2.1) ∧
    ∀ p ∈ i.2.1, p.2.2.2.2 = 0

open Classical in
/-- PRODUCTION PLANNING with equal demands, equal set-up costs and no inventory costs, as a decision
problem over bitstrings. -/
noncomputable def productionPlanningEqualDemandsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProductionPlanningInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ ProductionPlanningFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ProductionPlanningEqualDemands
