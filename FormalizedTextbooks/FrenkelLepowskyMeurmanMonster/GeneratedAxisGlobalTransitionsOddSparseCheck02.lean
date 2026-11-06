/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseSources

/-! Complete original finite certificates for sparse coordinate lookup 2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- Every stored key is precisely the original preferred coordinate of its source unit. -/
theorem generatedAxisGlobalOddSparseCheck02_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun p => generatedAxisGlobalShortNumber (generatedAxisGlobalOddSparseLabel 2 p))
      (generatedAxisGlobalOddSparseTree 2) := by
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- All 552 genuine source units round trip through the exact sparse coordinate lookup. -/
theorem generatedAxisGlobalOddSparseCheck02_roundtrip
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    generatedAxisGlobalOddSparseSource 2 (generatedAxisGlobalOddSparseLabel 2 p) = some p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
