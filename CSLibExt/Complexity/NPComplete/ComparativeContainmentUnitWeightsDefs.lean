/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE CONTAINMENT with unit weights: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP10] COMPARATIVE CONTAINMENT,
p. 223, comment: "Remains NP-complete even if all subsets in R and S have weight 1 [Garey and
Johnson, ——]" (unpublished; the result and its attribution are those recorded by Garey and
Johnson).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ComparativeContainmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeContainmentUnitWeights

open MetaMathlibExt.Complexity.NPComplete.ComparativeContainment
  (ComparativeContainmentInstance ComparativeContainmentFeasible)

/-- An instance: the size `n` of `X = Fin n` and the collections `R` and `S` as lists of
(subset, weight) pairs; this is the COMPARATIVE CONTAINMENT instance type. -/
abbrev ComparativeContainmentUnitWeightsInstance := ComparativeContainmentInstance

/-- Well-formedness of an instance: a well-formed COMPARATIVE CONTAINMENT instance (every member
of `R` and `S` lists distinct elements of `X`) in which every member of `R` and of `S` has
weight 1. -/
def WellFormed (i : ComparativeContainmentUnitWeightsInstance) : Prop :=
  ComparativeContainment.WellFormed i ∧ (∀ T ∈ i.2.1, T.2 = 1) ∧ ∀ T ∈ i.2.2, T.2 = 1

/-- Some `Y ⊆ X` is contained in at least as many members of `R` as of `S`, counted with their
(unit) weights (the COMPARATIVE CONTAINMENT question). -/
def ComparativeContainmentUnitWeightsFeasible
    (i : ComparativeContainmentUnitWeightsInstance) : Prop :=
  ComparativeContainmentFeasible i

open Classical in
/-- COMPARATIVE CONTAINMENT with unit weights as a decision problem over bitstrings. -/
noncomputable def comparativeContainmentUnitWeightsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparativeContainmentUnitWeightsInstance) x with
  | some i => decide (WellFormed i ∧ ComparativeContainmentUnitWeightsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ComparativeContainmentUnitWeights
