/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact initial source root-set integer witness certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCOrbitDigestData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootDigestNat

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- The exact finite matrix action and full 126-column integer sum are checked by the kernel.
/-- The first source representative has exactly its literal finite root-set integer digest. -/
theorem y322Orthogonal3TCOrbitDigest_initial_zero :
    y322Orthogonal3MatrixRootDigest
      (y322Orthogonal3TCCacheInverse (y322Orthogonal3TCRepresentativeCache 0)) =
        y322Orthogonal3IntegerDigits (y322Orthogonal3TCOrbitDigestBlock00Digits 0) := by
  rw [← y322Orthogonal3MatrixRootDigestNat_eq]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- This certificate includes the next original source word, not just the identity matrix case.
/-- The second source representative has exactly its literal finite root-set integer digest. -/
theorem y322Orthogonal3TCOrbitDigest_initial_one :
    y322Orthogonal3MatrixRootDigest
      (y322Orthogonal3TCCacheInverse (y322Orthogonal3TCRepresentativeCache 1)) =
        y322Orthogonal3IntegerDigits (y322Orthogonal3TCOrbitDigestBlock00Digits 1) := by
  rw [← y322Orthogonal3MatrixRootDigestNat_eq]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
