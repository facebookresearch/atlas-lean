/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOddCoordinates

/-! Exact displayed-owner checks cover every original nonzero odd-short coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Packed nine-bit owners used only with the original signed spin-sum certificates. -/
def generatedSixthMonomialOddOwnerMask : ℕ :=
  (
    (0x78381a0c058281208038180a04018080200 <<< 0) +
    (0x6832180b8582a140984822100000000000000000 <<< 800) +
    (0xf8783a1c0d8 <<< 960) +
    (0x4220000000000000000000000000000000000000 <<< 1440) +
    (0x178b85a2c158a85228138984a2411888 <<< 1600) +
    (0xa34198c862300000000000000000000000000000 <<< 1760) +
    (0x1f8f87a3c1d8e872381b8d86 <<< 1920) +
    (0x279389a4c259289248239188a442190882400000 <<< 2720) +
    (0xa250000000000000000000000000000000000000 <<< 2880) +
    (0x2f978ba5c2d968b2582b958aa5429948 <<< 3040) +
    (0x998ca6431988c260000000000000000000000000 <<< 3360) +
    (0x379b8da6c359a8d26833 <<< 3520) +
    (0x3f9f8fa7c3d9e8f2783b9d8ea74399c8e270 <<< 4320) +
    (0xa8441a0902800000000000000000000000000000 <<< 4640) +
    (0x47a391a8c45a29128843a190 <<< 4800) +
    (0x4fa793a9c4da6932984ba592a9449a4922900000 <<< 5600) +
    (0x1a8942a000000000000000000000000000000000 <<< 5920) +
    (0x57ab95aac55aa952a853a994aa45 <<< 6080) +
    (0xad96ab459ac962b0000000000000000000000000 <<< 6240) +
    (0x5faf97abc5dae972b85b <<< 6400) +
    (0x67b399acc65b2992c863b198ac461b0982c0 <<< 7200) +
    (0x9b49a2d000000000000000000000000000000000 <<< 7360) +
    (0x6fb79badc6db69b2d86bb59aad46 <<< 7520) +
    (0xc75ba9d2e873b99cae471b89c2e0000000000000 <<< 8160) +
    (0x77bb9dae <<< 8320) +
    (0xaf479bc9e2f00000000000000000000000000000 <<< 8960) +
    (0x7fbf9fafc7dbe9f2f87bbd9e <<< 9120) +
    (0x2a130883c1a0b0481c0a03000000000000000000 <<< 9440) +
    (0x87c3a1b0c85c <<< 9600) +
    (0xa3b1c8dc6a33188bc5a2b1489c4a231000000000 <<< 9760) +
    (0x8fc7 <<< 9920) +
    (0xb2491c8a43200000000000000000000000000000 <<< 10400) +
    (0x97cba5b2c95caa532893c9a4 <<< 10560) +
    (0x9fcfa7b3c9dcea73389bcda6b3499cca63300000 <<< 11360) +
    (0x8340000000000000000000000000000000000000 <<< 11520) +
    (0xa7d3a9b4ca5d2a9348a3d1a8b44a1d0a <<< 11680) +
    (0xcadd6ab358abd5aab54a9d4aa350000000000000 <<< 12480) +
    (0xafd7abb5 <<< 12640) +
    (0xb7dbadb6cb5daad368b3d9acb64b1d8ac360 <<< 12960) +
    (0x9dcae37000000000000000000000000000000000 <<< 13120) +
    (0xbfdfafb7cbddeaf378bbddaeb74b <<< 13280) +
    (0xc7e3b1b8cc5e2b1388c3e1b0b84c1e0b03800000 <<< 14240) +
    (0x2390000000000000000000000000000000000000 <<< 14400) +
    (0xcfe7b3b9ccde6b3398cbe5b2b94c9e4b <<< 14560) +
    (0xe9b4ba4d1e8b43a0000000000000000000000000 <<< 14880) +
    (0xd7ebb5bacd5eab53a8d3 <<< 15040) +
    (0xdfefb7bbcddeeb73b8dbedb6bb4d9ecb63b0 <<< 15840) +
    (0x1f0b83c000000000000000000000000000000000 <<< 16000) +
    (0xe7f3b9bcce5f2b93c8e3f1b8bc4e <<< 16160) +
    (0xbbbdcedf6bb3d8ebf5babd4e9f4ba3d000000000 <<< 16960) +
    (0xeff7 <<< 17120) +
    (0xbe4f1f8bc3e00000000000000000000000000000 <<< 17600) +
    (0xf7fbbdbecf5fabd3e8f3f9bc <<< 17760) +
    (0xf8fbfdbebf4f9fcbe3f000000000000000000000 <<< 17920) +
    (0xffffbfbfcfdfebf3 <<< 18080)
  )

/-- A bounded displayed family index for each possible original odd code address. -/
def generatedSixthMonomialOddOwner (d : Fin 2048) : Fin 512 :=
  Fin.ofNat 512 (generatedSixthMonomialOddOwnerMask >>> (9 * d.val))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
