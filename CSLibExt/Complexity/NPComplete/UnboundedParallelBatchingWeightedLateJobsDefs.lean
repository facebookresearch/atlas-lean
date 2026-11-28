/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED PARALLEL-BATCHING WEIGHTED NUMBER OF LATE JOBS (1|p-batch|Σw_iU_i): definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch|Σw_jU_j` NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch|Σw_iU_i`: minimal NP-hard in the ordinary sense.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedLateJobsDefs
public import CSLibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedLateJobs

open UnboundedParallelBatchingReleaseWeightedTardiness
  (UnboundedParallelBatchingReleaseWeightedTardinessInstance)
open UnboundedParallelBatchingReleaseWeightedLateJobs
  (UnboundedParallelBatchingReleaseWeightedLateJobsFeasible)
open UnboundedParallelBatchingWeightedTardiness (WellFormed)

open Classical in
/-- UNBOUNDED PARALLEL-BATCHING WEIGHTED NUMBER OF LATE JOBS as a decision problem over
bitstrings. -/
noncomputable def unboundedParallelBatchingWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedParallelBatchingReleaseWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnboundedParallelBatchingReleaseWeightedLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedLateJobs
