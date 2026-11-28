/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND19] STRONG CONNECTIVITY
AUGMENTATION, comment on p. 211 ("Remains NP-complete if all weights are either 1 or 2 and A is
empty");
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.StrongConnectivityAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwo

open MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentation
  (StrongConnectivityAugmentationInstance weight StrongConnectivityAugmentationFeasible)

/-- Well-formedness of an instance: a well-formed STRONG CONNECTIVITY AUGMENTATION instance
with no arcs in `G` and every weight equal to `1` or `2`. -/
def WellFormed (i : StrongConnectivityAugmentationInstance) : Prop :=
  StrongConnectivityAugmentation.WellFormed i ∧ i.2.1 = [] ∧
    ∀ u < i.1, ∀ v < i.1, weight i.2.2.1 u v = 1 ∨ weight i.2.2.1 u v = 2

open Classical in
/-- STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs as a decision problem over
bitstrings. -/
noncomputable def strongConnectivityAugmentationWeightsOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StrongConnectivityAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ StrongConnectivityAugmentationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwo
