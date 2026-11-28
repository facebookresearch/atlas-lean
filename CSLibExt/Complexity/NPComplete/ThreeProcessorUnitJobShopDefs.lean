/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR UNIT-TIME JOB-SHOP SCHEDULING (J3|p_ij=1|Cmax): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment: "If in the nonpreemptive case all tasks have the same length, the problem
is NP-complete for `m = 3`";
J. K. Lenstra and A. H. G. Rinnooy Kan, "Computational complexity of discrete optimization
problems", Annals of Discrete Mathematics 4 (1979), 121-140,
doi:10.1016/S0167-5060(08)70821-5 (cited by Garey and Johnson as [Lenstra and Rinnooy Kan,
1978b]);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop`, entry
`J3|p_ij=1|C_max` (minimal NP-hard in the strong sense, citing Lenstra and Rinnooy Kan 1979).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeProcessorEqualLengthJobShopDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitJobShop

open MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-- Well-formedness of an instance of the restriction: the instance is a well-formed
THREE-PROCESSOR JOB-SHOP SCHEDULING instance with equal task lengths (a well-formed JOB-SHOP
SCHEDULING instance with `m = 3` whose tasks all have one length), and every task has length
`1`. -/
def RestrictedWellFormed (i : JobShopSchedulingInstance) : Prop :=
  ThreeProcessorEqualLengthJobShop.RestrictedWellFormed i ∧ ∀ job ∈ i.2.1, ∀ t ∈ job, t.1 = 1

open Classical in
/-- THREE-PROCESSOR UNIT-TIME JOB-SHOP SCHEDULING, as a decision problem over bitstrings. -/
noncomputable def threeProcessorUnitJobShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitJobShop
