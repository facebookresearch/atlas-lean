/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|intree;p_i=1;p-batch;r_i;b<n|C_max`: definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|intree;p_i=1;p-batch;r_i;b<n|C_max`, minimal NP-hard in the strong sense,
by reduction from the parallel machine problem `P|intree;r_i;p_i=1|C_max`);
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275 (via `P|intree;r_i;p_i=1|C_max`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InTreeUnitParallelBatchingReleaseMakespan

open MetaMathlibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespan
  (ParallelMachinesInTreeReleaseMakespanInstance ParallelMachinesInTreeReleaseMakespanFeasible)

/-- Well-formedness of an instance: it is well-formed for `P|intree;r_i;p_i=1|C_max` (unit
lengths, `b > 0`, a strict partial order that is an in-tree, `K > 0`, one release date per job),
and the batch capacity is bounded: `b < n`. -/
def WellFormed (i : ParallelMachinesInTreeReleaseMakespanInstance) : Prop :=
  ParallelMachinesInTreeReleaseMakespan.WellFormed i ∧ i.1.2.1 < i.1.1.length

open Classical in
/-- `1|intree;p_i=1;p-batch;r_i;b<n|C_max` as a decision problem over bitstrings. -/
noncomputable def inTreeUnitParallelBatchingReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ParallelMachinesInTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ ParallelMachinesInTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InTreeUnitParallelBatchingReleaseMakespan
