/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseSources

/-! Complete original source-key validity and all552 exact source round trips. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 40000000

/-- Every stored index has its literal original source coordinate key. -/
theorem generatedAxisGlobalOddOtherSparseCheck04_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun p => generatedAxisGlobalShortNumber (generatedAxisGlobalOddOtherSparseLabel 2 p))
      (generatedAxisGlobalOddOtherSparseTree 2) := by
  decide +kernel

/-- Every complete original preferred source index is found under its exact coordinate. -/
theorem generatedAxisGlobalOddOtherSparseCheck04_roundtrip
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    generatedAxisGlobalOddOtherSparseSource 2 (generatedAxisGlobalOddOtherSparseLabel 2 p) = some p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
