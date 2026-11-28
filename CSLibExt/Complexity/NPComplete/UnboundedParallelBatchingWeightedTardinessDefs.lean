/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS (1|p-batch|Σw_iT_i): definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch|Σw_jT_j` NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch|Σw_iT_i`: minimal NP-hard in the ordinary sense.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedTardiness

open UnboundedParallelBatchingReleaseWeightedTardiness
  (UnboundedParallelBatchingReleaseWeightedTardinessInstance
    UnboundedParallelBatchingReleaseWeightedTardinessFeasible)

/-- Well-formedness of an instance: well-formed for `1|p-batch;r_i|Σw_iT_i` (positive processing
times), and every release date is `0`. -/
def WellFormed (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) : Prop :=
  UnboundedParallelBatchingReleaseWeightedTardiness.WellFormed i ∧ ∀ x ∈ i.1, x.2.1 = 0

open Classical in
/-- UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS as a decision problem over bitstrings. -/
noncomputable def unboundedParallelBatchingWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedParallelBatchingReleaseWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnboundedParallelBatchingReleaseWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedTardiness
