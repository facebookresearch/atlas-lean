/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianBitAction

/-! Packed evaluations retain every original Gaussian shift and central phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All original twelve-bit Pauli translation labels. -/
def generatedSeventhXiGaussianPackedTranslationBits : ℕ :=
  0xb2787d3b9070ab499e85ab9315720d9c9a000c432a7ee427ee3db967d5b4f70c +
    (0x3baa16e28064458df49c137d741eedad5ad9ee574937c9c0dfc45006ee22a1e3 <<< 256) +
    (0xf0c34ffd539663da7e6e4aa744380049a8d9d72131dab1e8349f0a390fd3a786 <<< 512)

/-- All original twelve-bit Pauli modulation labels. -/
def generatedSeventhXiGaussianPackedModulationBits : ℕ :=
  0x77a93ef54177d1d359133f1037ad3eb5457791d720b4a56990374712df0e364d +
    (0x733b5956490e72db47503369d4a120f20f4a169d0334752db0e764959533b10 <<< 256) +
    (0x64d0e32df4710376994a520b1d77795453eb7ad10333f5911d377d5413ef7a91 <<< 512)

/-- All original central bits of the actual corrected Pauli elements. -/
def generatedSeventhXiGaussianPackedCentralBits : ℕ :=
  0xa36f90a3c509f6c5

/-- Every negative phase of the actual source-conjugated diagonal Gaussian. -/
def generatedSeventhXiGaussianPackedGammaBits : ℕ :=
  0x99ccaa00336600aa00aacc99aa00663366cc5500339900550055cc6655009933 +
    (0xaa0099cc00aa3366cc9900aa6633aa00550066cc00553399cc66005599335500 <<< 256) +
    (0x6633aa00cc9900aa00aa3366aa0099cc99335500cc66005500553399550066cc <<< 512) +
    (0xaa00663300aacc99336600aa99ccaa00550099330055cc663399005566cc5500 <<< 768) +
    (0x66cc5500339900550055cc665500993399ccaa00336600aa00aacc99aa006633 <<< 1024) +
    (0x550066cc00553399cc66005599335500aa0099cc00aa3366cc9900aa6633aa00 <<< 1280) +
    (0x99335500cc66005500553399550066cc6633aa00cc9900aa00aa3366aa0099cc <<< 1536) +
    (0x550099330055cc663399005566cc5500aa00663300aacc99336600aa99ccaa00 <<< 1792) +
    (0x5a0f69c30f5a3c963c96f0a569c3a5f0a50f96c30fa53c693c69f05a96c35af0 <<< 2048) +
    (0x69c35a0f3c960f5af0a53c96a5f069c396c3a50f3c690fa5f05a3c695af096c3 <<< 2304) +
    (0xa5f069c3f0a53c963c960f5a69c35a0f5af096c3f05a3c693c690fa596c3a50f <<< 2560) +
    (0x69c3a5f03c96f0a50f5a3c965a0f69c396c35af03c69f05a0fa53c69a50f96c3 <<< 2816) +
    (0x5af0693cf05ac396c3960fa5693ca50fa5f0963cf0a5c369c3690f5a963c5a0f <<< 3072) +
    (0x693c5af0c396f05a0fa5c396a50f693c963ca5f0c369f0a50f5ac3695a0f963c <<< 3328) +
    (0xa50f693c0fa5c396c396f05a693c5af05a0f963c0f5ac369c369f0a5963ca5f0 <<< 3584) +
    (0x693ca50fc3960fa5f05ac3965af0693c963c5a0fc3690f5af0a5c369a5f0963c <<< 3840)

/-- Each packed shift is reconstructed as the complete actual source spin label. -/
def generatedSeventhXiGaussianPackedShift (a : Fin 64) : Fin 4096 :=
  ⟨(generatedSeventhXiGaussianPackedTranslationBits >>> (12 * a.val)) % 4096,
    Nat.mod_lt _ (by decide)⟩

/-- The original modulation bit mask of each Gaussian summand. -/
def generatedSeventhXiGaussianPackedModulation (a : Fin 64) : ℕ :=
  (generatedSeventhXiGaussianPackedModulationBits >>> (12 * a.val)) % 4096

/-- Every original central sign remains explicit in this compact evaluator. -/
def generatedSeventhXiGaussianPackedCentral (a : Fin 64) : ℤ :=
  if generatedSeventhXiGaussianPackedCentralBits.testBit a.val then -1 else 1

/-- The complete actual Pauli phase uses both its original modulation and central coefficient. -/
def generatedSeventhXiGaussianPackedPhase (a : Fin 64) (d : Fin 4096) : ℤ :=
  generatedSeventhXiGaussianPackedCentral a *
    (if monsterNortonBitParity (generatedSeventhXiGaussianPackedModulation a &&& d.val)
      then -1 else 1)

/-- The full actual conjugated Gaussian sign at a source spin label. -/
def generatedSeventhXiGaussianPackedGamma (d : Fin 4096) : ℤ :=
  if generatedSeventhXiGaussianPackedGammaBits.testBit d.val then -1 else 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
