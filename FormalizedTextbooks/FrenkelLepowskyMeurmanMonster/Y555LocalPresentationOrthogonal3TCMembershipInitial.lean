/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact initial and late-index finite membership certificates for source root-set transports. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipEval
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- The exact source matrix and all 31 finite root membership tests are checked in the kernel.
/-- The first declared source matrix has exactly its literal finite root membership fingerprint. -/
theorem y322Orthogonal3TCMembership_initial_zero :
    y322Orthogonal3TCMembershipEval
      (y322Orthogonal3TCCacheMatrix (y322Orthogonal3TCRepresentativeCache 0)) =
        y322Orthogonal3TCMembershipValue 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- This certificate checks the next source matrix and its complete 31-point fingerprint.
/-- The second declared source matrix has exactly its literal finite root membership fingerprint. -/
theorem y322Orthogonal3TCMembership_initial_one :
    y322Orthogonal3TCMembershipEval
      (y322Orthogonal3TCCacheMatrix (y322Orthogonal3TCRepresentativeCache 1)) =
        y322Orthogonal3TCMembershipValue 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- A late source index checks finite selector behavior as well as all 31 root membership tests.
/-- The source matrix at 3072 has its literal finite root membership fingerprint. -/
theorem y322Orthogonal3TCMembership_initial_late :
    y322Orthogonal3TCMembershipEval
      (y322Orthogonal3TCCacheMatrix (y322Orthogonal3TCRepresentativeCache 3072)) =
        y322Orthogonal3TCMembershipValue 3072 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
