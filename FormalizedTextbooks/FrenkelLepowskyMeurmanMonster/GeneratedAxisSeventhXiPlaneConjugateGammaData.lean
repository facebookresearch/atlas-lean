/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinBitSignsData

/-! Compact conjugated-Gaussian signs, with a complete bitwise lookup certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Negative rows of the original Gaussian after the actual inverse compact code relabeling. -/
def generatedSeventhXiPlaneConjugateGammaRows : Fin 64 → ℕ :=
  ![
    0x55cc6655009933,
    0x66cc550033990055,
    0xaacc99aa006633,
    0x99ccaa00336600aa,
    0xcc66005599335500,
    0x550066cc00553399,
    0xcc9900aa6633aa00,
    0xaa0099cc00aa3366,
    0x553399550066cc,
    0x99335500cc660055,
    0xaa3366aa0099cc,
    0x6633aa00cc9900aa,
    0x3399005566cc5500,
    0x550099330055cc66,
    0x336600aa99ccaa00,
    0xaa00663300aacc99,
    0xaacc99aa006633,
    0x99ccaa00336600aa,
    0x55cc6655009933,
    0x66cc550033990055,
    0xcc9900aa6633aa00,
    0xaa0099cc00aa3366,
    0xcc66005599335500,
    0x550066cc00553399,
    0xaa3366aa0099cc,
    0x6633aa00cc9900aa,
    0x553399550066cc,
    0x99335500cc660055,
    0x336600aa99ccaa00,
    0xaa00663300aacc99,
    0x3399005566cc5500,
    0x550099330055cc66,
    0x3c69f05a96c35af0,
    0xa50f96c30fa53c69,
    0x3c96f0a569c3a5f0,
    0x5a0f69c30f5a3c96,
    0xf05a3c695af096c3,
    0x96c3a50f3c690fa5,
    0xf0a53c96a5f069c3,
    0x69c35a0f3c960f5a,
    0x3c690fa596c3a50f,
    0x5af096c3f05a3c69,
    0x3c960f5a69c35a0f,
    0xa5f069c3f0a53c96,
    0xfa53c69a50f96c3,
    0x96c35af03c69f05a,
    0xf5a3c965a0f69c3,
    0x69c3a5f03c96f0a5,
    0xc3690f5a963c5a0f,
    0xa5f0963cf0a5c369,
    0xc3960fa5693ca50f,
    0x5af0693cf05ac396,
    0xf5ac3695a0f963c,
    0x963ca5f0c369f0a5,
    0xfa5c396a50f693c,
    0x693c5af0c396f05a,
    0xc369f0a5963ca5f0,
    0x5a0f963c0f5ac369,
    0xc396f05a693c5af0,
    0xa50f693c0fa5c396,
    0xf0a5c369a5f0963c,
    0x963c5a0fc3690f5a,
    0xf05ac3965af0693c,
    0x693ca50fc3960fa5
  ]

/-- The conjugated diagonal coefficient evaluated by one verified bit lookup. -/
def generatedSeventhXiPlaneConjugateGammaBit (d : Fin 4096) : ℤ :=
  if (generatedSeventhXiPlaneConjugateGammaRows ⟨d.val / 64, by omega⟩).testBit (d.val % 64)
    then -1 else 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check all 4096 signs against the already source-bound inverse label and diagonal tables.
/-- Every lookup is exactly the bitwise inverse relabeling of the original diagonal. -/
theorem generatedSeventhXiPlaneConjugateGammaBit_lookup : ∀ d : Fin 4096,
    generatedSeventhXiPlaneConjugateGammaBit d =
      generatedSeventhXiPlaneBitGamma (generatedSeventhXiPlaneBitCodeLabel 1 d) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
