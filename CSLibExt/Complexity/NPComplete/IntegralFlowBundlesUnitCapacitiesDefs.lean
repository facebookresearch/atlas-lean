/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH BUNDLES with unit capacities and two-arc bundles: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND36] INTEGRAL FLOW WITH
BUNDLES, p. 216, comment ("Remains NP-complete if all capacities are 1 and all bundles have two
arcs");
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021 (Problem N(iv), Theorem 2.2).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntegralFlowBundlesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundlesUnitCapacities

open IntegralFlowBundles (IntegralFlowBundlesInstance IntegralFlowBundlesFeasible)

/-- Well-formedness of an instance: a well-formed INTEGRAL FLOW WITH BUNDLES instance in which
every bundle has capacity `1` and consists of exactly two distinct arcs. -/
def WellFormed (i : IntegralFlowBundlesInstance) : Prop :=
  IntegralFlowBundles.WellFormed i ∧ ∀ b ∈ i.2.2.2.2.1, b.2 = 1 ∧ b.1.toFinset.card = 2

open Classical in
/-- INTEGRAL FLOW WITH BUNDLES with unit capacities and two-arc bundles as a decision problem
over bitstrings. -/
noncomputable def integralFlowBundlesUnitCapacitiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegralFlowBundlesInstance) x with
  | some i => decide (WellFormed i ∧ IntegralFlowBundlesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundlesUnitCapacities
