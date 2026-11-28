/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK RECOVERY with a single resource type: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4(3)
(1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem [3] DEADLOCK RECOVERY, comment
("NP-complete but solvable in time pseudo-polynomial in K if m = 1", credited there to
J. Y.-T. Leung, "Complexity of optimal deadlock recovery", manuscript (1983), which was not
available), with the question as corrected in the column of Journal of Algorithms 5(1) (1984),
147-160, doi:10.1016/0196-6774(84)90045-2 (which says the results of that manuscript and of
Leung and Lai concern the sequential version);
J. Y.-T. Leung and E. K. Lai, "On minimum cost recovery from system deadlock", IEEE Transactions
on Computers C-28(9) (1979), 671-677, doi:10.1109/TC.1979.1675435.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DeadlockRecoveryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockRecoveryOneResource

open MetaMathlibExt.Complexity.NPComplete.DeadlockRecovery
  (DeadlockRecoveryInstance numResources DeadlockRecoveryFeasible)

/-- Well-formedness of an instance: a well-formed DEADLOCK RECOVERY instance with exactly one
resource type (`m = 1`). -/
def WellFormed (i : DeadlockRecoveryInstance) : Prop :=
  DeadlockRecovery.WellFormed i ∧ numResources i = 1

open Classical in
/-- DEADLOCK RECOVERY with a single resource type as a decision problem over bitstrings. -/
noncomputable def deadlockRecoveryOneResourceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DeadlockRecoveryInstance) x with
  | some i => decide (WellFormed i ∧ DeadlockRecoveryFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DeadlockRecoveryOneResource
