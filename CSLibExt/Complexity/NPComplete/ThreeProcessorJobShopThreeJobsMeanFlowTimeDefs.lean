/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR JOB-SHOP MEAN FLOW TIME with three jobs (J3|n=3|ΣC_i): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop`, entry `J3|n=3|ΣC_i`
(minimal NP-hard in the ordinary sense, citing Sotskov and Shakhlevich 1995).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.TwoProcessorJobShopMeanFlowTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobsMeanFlowTime

open JobShopScheduling (JobShopSchedulingInstance)

open Classical in
/-- THREE-PROCESSOR JOB-SHOP MEAN FLOW TIME with three jobs, as a decision problem over
bitstrings. -/
noncomputable def threeProcessorJobShopThreeJobsMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (ThreeProcessorJobShopThreeJobs.RestrictedWellFormed i ∧
      TwoProcessorJobShopMeanFlowTime.TwoProcessorJobShopMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobsMeanFlowTime
