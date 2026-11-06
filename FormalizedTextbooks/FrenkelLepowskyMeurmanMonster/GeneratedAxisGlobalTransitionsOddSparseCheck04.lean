/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseSources

/-! Complete original finite certificates for sparse coordinate lookup 4. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- Every stored key is precisely the original preferred coordinate of its source unit. -/
theorem generatedAxisGlobalOddSparseCheck04_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun p => generatedAxisGlobalShortNumber (generatedAxisGlobalOddSparseLabel 4 p))
      (generatedAxisGlobalOddSparseTree 4) := by
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- All 552 genuine source units round trip through the exact sparse coordinate lookup. -/
theorem generatedAxisGlobalOddSparseCheck04_roundtrip
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    generatedAxisGlobalOddSparseSource 4 (generatedAxisGlobalOddSparseLabel 4 p) = some p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
