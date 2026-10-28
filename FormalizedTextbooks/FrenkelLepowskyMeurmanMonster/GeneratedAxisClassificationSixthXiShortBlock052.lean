/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortNumbering
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedScalar
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressMaskEight

/-! Original sparse masks and full signed phases certify a bounded part of actual short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Candidate sparse outputs are checked against the original full binary and phase action. -/
def generatedSixthXiShortBlock052Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (85, 61)),
    Sum.inr (Sum.inl (199, 34)),
    Sum.inr (Sum.inl (98, 1)),
    Sum.inr (Sum.inl (183, 4)),
    Sum.inr (Sum.inl (85, 44)),
    Sum.inr (Sum.inl (199, 38)),
    Sum.inr (Sum.inl (98, 58)),
    Sum.inr (Sum.inl (183, 38)),
    Sum.inr (Sum.inl (98, 18)),
    Sum.inr (Sum.inl (183, 24)),
    Sum.inr (Sum.inl (85, 8)),
    Sum.inr (Sum.inl (199, 24)),
    Sum.inr (Sum.inl (98, 41)),
    Sum.inr (Sum.inl (183, 58)),
    Sum.inr (Sum.inl (85, 25)),
    Sum.inr (Sum.inl (199, 28)),
    Sum.inr (Sum.inl (59, 24)),
    Sum.inr (Sum.inl (62, 40)),
    Sum.inr (Sum.inl (135, 8)),
    Sum.inr (Sum.inl (219, 16)),
    Sum.inr (Sum.inl (59, 25)),
    Sum.inr (Sum.inl (62, 56)),
    Sum.inr (Sum.inl (135, 51)),
    Sum.inr (Sum.inl (219, 50)),
    Sum.inr (Sum.inl (85, 10)),
    Sum.inr (Sum.inl (199, 10)),
    Sum.inr (Sum.inl (98, 17)),
    Sum.inr (Sum.inl (183, 20)),
    Sum.inr (Sum.inl (85, 27)),
    Sum.inr (Sum.inl (199, 14)),
    Sum.inr (Sum.inl (98, 42)),
    Sum.inr (Sum.inl (183, 54)),
    Sum.inr (Sum.inl (135, 10)),
    Sum.inr (Sum.inl (219, 24)),
    Sum.inr (Sum.inl (59, 20)),
    Sum.inr (Sum.inl (62, 36)),
    Sum.inr (Sum.inl (135, 49)),
    Sum.inr (Sum.inl (219, 58)),
    Sum.inr (Sum.inl (59, 21)),
    Sum.inr (Sum.inl (62, 52)),
    Sum.inr (Sum.inl (101, 10)),
    Sum.inr (Sum.inl (101, 46)),
    Sum.inr (Sum.inl (76, 21)),
    Sum.inr (Sum.inl (76, 40)),
    Sum.inr (Sum.inl (120, 37)),
    Sum.inr (Sum.inl (120, 24)),
    Sum.inr (Sum.inl (82, 8)),
    Sum.inr (Sum.inl (82, 23)),
    Sum.inr (Sum.inl (120, 41)),
    Sum.inr (Sum.inl (120, 20)),
    Sum.inr (Sum.inl (82, 4)),
    Sum.inr (Sum.inl (82, 27)),
    Sum.inr (Sum.inl (101, 8)),
    Sum.inr (Sum.inl (101, 44)),
    Sum.inr (Sum.inl (76, 29)),
    Sum.inr (Sum.inl (76, 32)),
    Sum.inr (Sum.inl (182, 60)),
    Sum.inr (Sum.inl (182, 61)),
    Sum.inr (Sum.inl (224, 61)),
    Sum.inr (Sum.inl (224, 13)),
    Sum.inr (Sum.inl (45, 61)),
    Sum.inr (Sum.inl (45, 21)),
    Sum.inr (Sum.inl (200, 54)),
    Sum.inr (Sum.inl (200, 55)),
    Sum.inr (Sum.inl (45, 62)),
    Sum.inr (Sum.inl (45, 22)),
    Sum.inr (Sum.inl (200, 58)),
    Sum.inr (Sum.inl (200, 59)),
    Sum.inr (Sum.inl (182, 46)),
    Sum.inr (Sum.inl (182, 47)),
    Sum.inr (Sum.inl (224, 63)),
    Sum.inr (Sum.inl (224, 15)),
    Sum.inr (Sum.inl (76, 1)),
    Sum.inr (Sum.inl (76, 60)),
    Sum.inr (Sum.inl (101, 37)),
    Sum.inr (Sum.inl (101, 1)),
    Sum.inr (Sum.inl (82, 26)),
    Sum.inr (Sum.inl (82, 5)),
    Sum.inr (Sum.inl (120, 5)),
    Sum.inr (Sum.inl (120, 56)),
    Sum.inr (Sum.inl (82, 22)),
    Sum.inr (Sum.inl (82, 9)),
    Sum.inr (Sum.inl (120, 9)),
    Sum.inr (Sum.inl (120, 52)),
    Sum.inr (Sum.inl (76, 9)),
    Sum.inr (Sum.inl (76, 52)),
    Sum.inr (Sum.inl (101, 39)),
    Sum.inr (Sum.inl (101, 3)),
    Sum.inr (Sum.inl (224, 52)),
    Sum.inr (Sum.inl (224, 4)),
    Sum.inr (Sum.inl (182, 20)),
    Sum.inr (Sum.inl (182, 21)),
    Sum.inr (Sum.inl (200, 20)),
    Sum.inr (Sum.inl (200, 21)),
    Sum.inr (Sum.inl (45, 45)),
    Sum.inr (Sum.inl (45, 5)),
    Sum.inr (Sum.inl (200, 24)),
    Sum.inr (Sum.inl (200, 25)),
    Sum.inr (Sum.inl (45, 46)),
    Sum.inr (Sum.inl (45, 6)),
    Sum.inr (Sum.inl (224, 54)),
    Sum.inr (Sum.inl (224, 6)),
    Sum.inr (Sum.inl (182, 6)),
    Sum.inr (Sum.inl (182, 7)),
    Sum.inr (Sum.inl (115, 18)),
    Sum.inr (Sum.inl (217, 61)),
    Sum.inr (Sum.inl (90, 34)),
    Sum.inr (Sum.inl (164, 55)),
    Sum.inr (Sum.inl (130, 27)),
    Sum.inr (Sum.inl (43, 37)),
    Sum.inr (Sum.inl (75, 53)),
    Sum.inr (Sum.inl (201, 19)),
    Sum.inr (Sum.inl (115, 17)),
    Sum.inr (Sum.inl (217, 47)),
    Sum.inr (Sum.inl (90, 32)),
    Sum.inr (Sum.inl (164, 59)),
    Sum.inr (Sum.inl (130, 25)),
    Sum.inr (Sum.inl (43, 41)),
    Sum.inr (Sum.inl (75, 57)),
    Sum.inr (Sum.inl (201, 27)),
    Sum.inr (Sum.inl (90, 43)),
    Sum.inr (Sum.inl (164, 37)),
    Sum.inr (Sum.inl (115, 13)),
    Sum.inr (Sum.inl (217, 53)),
    Sum.inr (Sum.inl (75, 20)),
    Sum.inr (Sum.inl (201, 1)),
    Sum.inr (Sum.inl (130, 4)),
    Sum.inr (Sum.inl (43, 5)),
    Sum.inr (Sum.inl (90, 41)),
    Sum.inr (Sum.inl (164, 41)),
    Sum.inr (Sum.inl (115, 14)),
    Sum.inr (Sum.inl (217, 39)),
    Sum.inr (Sum.inl (75, 24)),
    Sum.inr (Sum.inl (201, 9)),
    Sum.inr (Sum.inl (130, 6)),
    Sum.inr (Sum.inl (43, 9)),
    Sum.inr (Sum.inl (130, 18)),
    Sum.inr (Sum.inl (43, 55)),
    Sum.inr (Sum.inl (75, 55)),
    Sum.inr (Sum.inl (201, 55)),
    Sum.inr (Sum.inl (115, 26)),
    Sum.inr (Sum.inl (217, 25)),
    Sum.inr (Sum.inl (90, 13)),
    Sum.inr (Sum.inl (164, 23)),
    Sum.inr (Sum.inl (130, 16)),
    Sum.inr (Sum.inl (43, 59)),
    Sum.inr (Sum.inl (75, 59)),
    Sum.inr (Sum.inl (201, 63)),
    Sum.inr (Sum.inl (115, 25)),
    Sum.inr (Sum.inl (217, 11)),
    Sum.inr (Sum.inl (90, 15)),
    Sum.inr (Sum.inl (164, 27)),
    Sum.inr (Sum.inl (75, 22)),
    Sum.inr (Sum.inl (201, 37)),
    Sum.inr (Sum.inl (130, 13)),
    Sum.inr (Sum.inl (43, 23)),
    Sum.inr (Sum.inl (90, 4)),
    Sum.inr (Sum.inl (164, 5)),
    Sum.inr (Sum.inl (115, 5)),
    Sum.inr (Sum.inl (217, 17)),
    Sum.inr (Sum.inl (75, 26)),
    Sum.inr (Sum.inl (201, 45)),
    Sum.inr (Sum.inl (130, 15)),
    Sum.inr (Sum.inl (43, 27)),
    Sum.inr (Sum.inl (90, 6)),
    Sum.inr (Sum.inl (164, 9)),
    Sum.inr (Sum.inl (115, 6)),
    Sum.inr (Sum.inl (217, 3)),
    Sum.inr (Sum.inl (56, 62)),
    Sum.inr (Sum.inl (116, 36)),
    Sum.inr (Sum.inl (222, 55)),
    Sum.inr (Sum.inl (163, 36)),
    Sum.inr (Sum.inl (105, 59)),
    Sum.inr (Sum.inl (129, 34)),
    Sum.inr (Sum.inl (60, 61)),
    Sum.inr (Sum.inl (202, 31)),
    Sum.inr (Sum.inl (105, 56)),
    Sum.inr (Sum.inl (129, 46)),
    Sum.inr (Sum.inl (60, 49)),
    Sum.inr (Sum.inl (202, 19)),
    Sum.inr (Sum.inl (56, 44)),
    Sum.inr (Sum.inl (116, 38)),
    Sum.inr (Sum.inl (222, 53)),
    Sum.inr (Sum.inl (163, 44)),
    Sum.inr (Sum.inl (222, 50)),
    Sum.inr (Sum.inl (163, 54)),
    Sum.inr (Sum.inl (56, 54)),
    Sum.inr (Sum.inl (116, 11)),
    Sum.inr (Sum.inl (60, 44)),
    Sum.inr (Sum.inl (202, 13)),
    Sum.inr (Sum.inl (105, 27)),
    Sum.inr (Sum.inl (129, 13)),
    Sum.inr (Sum.inl (60, 32)),
    Sum.inr (Sum.inl (202, 1)),
    Sum.inr (Sum.inl (105, 24)),
    Sum.inr (Sum.inl (129, 1)),
    Sum.inr (Sum.inl (222, 48)),
    Sum.inr (Sum.inl (163, 62)),
    Sum.inr (Sum.inl (56, 36)),
    Sum.inr (Sum.inl (116, 9)),
    Sum.inr (Sum.inl (56, 31)),
    Sum.inr (Sum.inl (116, 40)),
    Sum.inr (Sum.inl (222, 31)),
    Sum.inr (Sum.inl (163, 31)),
    Sum.inr (Sum.inl (105, 47)),
    Sum.inr (Sum.inl (129, 32)),
    Sum.inr (Sum.inl (60, 63)),
    Sum.inr (Sum.inl (202, 63)),
    Sum.inr (Sum.inl (105, 44)),
    Sum.inr (Sum.inl (129, 44)),
    Sum.inr (Sum.inl (60, 51)),
    Sum.inr (Sum.inl (202, 51)),
    Sum.inr (Sum.inl (56, 13)),
    Sum.inr (Sum.inl (116, 42)),
    Sum.inr (Sum.inl (222, 29)),
    Sum.inr (Sum.inl (163, 23)),
    Sum.inr (Sum.inl (222, 26)),
    Sum.inr (Sum.inl (163, 13)),
    Sum.inr (Sum.inl (56, 23)),
    Sum.inr (Sum.inl (116, 7)),
    Sum.inr (Sum.inl (60, 46)),
    Sum.inr (Sum.inl (202, 45)),
    Sum.inr (Sum.inl (105, 15)),
    Sum.inr (Sum.inl (129, 15)),
    Sum.inr (Sum.inl (60, 34)),
    Sum.inr (Sum.inl (202, 33)),
    Sum.inr (Sum.inl (105, 12)),
    Sum.inr (Sum.inl (129, 3)),
    Sum.inr (Sum.inl (222, 24)),
    Sum.inr (Sum.inl (163, 5)),
    Sum.inr (Sum.inl (56, 5)),
    Sum.inr (Sum.inl (116, 5)),
    Sum.inr (Sum.inl (203, 16)),
    Sum.inl 42,
    Sum.inr (Sum.inl (203, 56)),
    Sum.inl 1,
    Sum.inl 338,
    Sum.inr (Sum.inl (203, 63)),
    Sum.inl 59,
    Sum.inr (Sum.inl (203, 23)),
    Sum.inr (Sum.inl (203, 50)),
    Sum.inl 21,
    Sum.inr (Sum.inl (203, 48)),
    Sum.inl 28,
    Sum.inl 317,
    Sum.inr (Sum.inl (203, 29)),
    Sum.inl 324,
    Sum.inr (Sum.inl (203, 31)),
    Sum.inl 459,
    Sum.inr (Sum.inl (203, 43)),
    Sum.inl 68,
    Sum.inr (Sum.inl (203, 3)),
    Sum.inr (Sum.inl (203, 46)),
    Sum.inl 551,
    Sum.inr (Sum.inl (203, 6)),
    Sum.inl 88]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock052Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨13312 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock052InputMaskData : ℕ :=
  sixthHex% [
    "6d993140e93120e9310d91310009312d71314d713160013144a93169d931",
    "09d93124a1312939310441316441314931316a39314741312741310a3131",
    "07a1312ad1314ad13167a93173ebfd533bfd633bfd43e3fd73cbfd5313fd",
    "6313fd43c3fd3fcbfd1f13fd2f13fd0fc3fd3fe3fd1f33fd2f33fd0febfd",
    "31dbfd1103fd2103fd01d3fd31f3fd1123fd2123fd01fbfd7df3fd5d23fd",
    "6d23fd4dfbfd7dd3fd5d0bfd6d0bfd4ddbfd32dbfd1203fd2203fd02d3fd",
    "32f3fd1223fd2223fd02fbfd7ef3fd5e23fd6e23fd4efbfd7ed3fd5e0bfd",
    "6e0bfd4edbfd70e3fd5033fd6033fd40ebfd70c3fd501bfd601bfd40cbfd",
    "3cc3fd1c1bfd2c1bfd0ccbfd3cebfd1c3bfd2c3bfd0ce3fd0ae51d33551d",
    "63551d5aed1d43551d7aed1d2aed1d135d1d73a51d4a1d1d1a1d1d23ad1d",
    "3a1d1d03ad1d53ad1d6a151d31b51d080d1d580d1d61bd1d780d1d41bd1d",
    "11bd1d28051d48fd1d714d1d214d1d18f51d014d1d38f51d68f51d51451d",
    "73851d4a3d1d1a3d1d238d1d3a3d1d038d1d538d1d6a351d0acd1d337d1d",
    "637d1d5ac51d437d1d7ac51d2ac51d13751d48dd1d716d1d216d1d18d51d",
    "016d1d38d51d68d51d51651d319d1d08251d58251d61951d78251d41951d",
    "11951d282d1d067b9e4b0b9e7b0b9e36739e6bfb9e26839e16839e5bf39e",
    "2ffb9e62839e52839e1ff39e42739e0f039e3f039e727b9e6beb9e26939e",
    "16939e5be39e06639e4b139e7b139e366b9e42639e0f139e3f139e726b9e",
    "2fe39e629b9e529b9e1feb9e29eb9e64939e54939e19e39e44639e09139e",
    "39139e746b9e00639e4d139e7d139e306b9e6de39e209b9e109b9e5deb9e",
    "44739e09039e39039e747b9e29f39e648b9e548b9e19fb9e6df39e208b9e",
    "108b9e5dfb9e007b9e4d0b9e7d0b9e30739e082d155e5d157ead1528d515",
    "3cbd156ac5154a35151c45157e8d1528f5150805155e75154a15151c6515",
    "3c95156aed1507ed1551951571651527151533751565051545f515138d15",
    "71451527351507c51551bd1545d51513ad15335d15652d157e2d15285515",
    "08a5155ed5154ab5151cc5153c35156a4d15"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock052InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock052InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock052OutputMaskData : ℕ :=
  sixthHex% [
    "7b70004741313608007b793107a1314ad0003b993107a8004301317f3000",
    "0e79314308003fd00072a13103e8003fd9316d993120e80051a1316d9000",
    "6008005c39312d700060013114eda206efb8207c98433e8228dac74b98dd",
    "6d0bfd7f09e764d2c70790dd2103fd3301e729a5a23ba7b81d34987e7682",
    "72949811d6823745a22547b83fe3fd2de1e70b72c76830dd73ebfd61e9e7",
    "477ac72438dd4fdc982c9e820a0da2180fb855dda2369fb8100c98020e82",
    "18aac70aa8dd2c3bfd4f79e754a2c746a0dd6033fd0371e76895a20bd7b8",
    "2d44983f468242e49850e6827675a21537b87ed3fd1d91e73b02c72900dd",
    "32dbfd5199e7770ac76508dd7fac986dae824b3da2287fb82d04270b3869",
    "5ce2780b9e3658ab420fd70c580d1d7e315354442703386954e27872de36",
    "50ab4276970c214d1d7631530e0a785976360eac272890690ae51d2cd953",
    "7b03422c7f0c060a7820363677ec2720906973a51d24d953730342553f0c",
    "6873423f0f0c68d51d4ee9536c9c274aa0691d7a784a0636607342464f0c",
    "11951d46e95315dc2742a069157a783346363a3d1d1c01534bdb421ca70c",
    "4f927818ee364f3427690869437d1d14015343db4265e70c47927861ae36",
    "36742761086940f5c10d8dc12b1ee11726e123b8be1f80be39139e746b9e",
    "67b8be5b80be7d139e306b9e75b5c138cdc11e5ee12266e13c24f0001cf0",
    "268fd06bf7d02e298f63518f45c2af79faaf6a298f27518f01c2af3dfaaf",
    "0964f0355cf013cfd05eb7d079f6e145cee1635dc12e25c16bfb9e26839e",
    "0010be3c28be2ffb9e62839e4410be7828be4cb6e1708ee1561dc11b65c1",
    "7467d0391fd01f8cf023b4f0172aaf2b12af0d818f40f98f532aaf6f12af",
    "49818f04f98f4127d00c5fd02accf016f4f06ae2702a015004342f35970f",
    "5e7a706fd95041ec2f010f0f38034a09a06a2795156776357ddb4a3d386a",
    "130d1522ae357d742f4cd70f62e27022015038ac2f784f0f567a7067d950",
    "5ed5151e363530034a01a06a6a4d155bee3575db4a35386a38a34a09006a",
    "27351567d6357d7b4a3d986a13ad15220e35"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock052OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock052OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock052InputNumeratorData : ℕ :=
  sixthHex% [
    "86185f7e18617df7e185f7df7e18617df7e185f8617df85f8617e185f861",
    "8617e185f8617e17df8617e17df85f7e17df85f8617df85f85f8617df85f",
    "8617e185f86185f8617df85f7df85f7e17df8617e185f86185f8617df85f",
    "8617e185f86185f8617df85f7e17df8617e18617e185f86185f8617df85f",
    "7df85f7e17df8617e185f86185f8617df85f8617e185f86185f8617df85f",
    "7e17df8617e18617e185f86185f7df86185f86185f7e186186185f7e1861",
    "7e18617df7e186185f7e1861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock052InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock052InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock052OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617e17e17df7df85f85f86185f8618617e186185f85f7df85f7df7df7e1",
    "7e186186185f86185f85f7df7e186186185f86185f85f7df7df7e17e1861",
    "7e186186185f86185f85f7df7e186186185f7e186186185f7df7e17e1861",
    "85f7df7df7e186185f85f7df86185f85f7df7e186186185f8617e185f861",
    "85f8617df85f7e17df8617e18617e185f86185f8617df85f7df85f7e17df",
    "8617e185f86185f8617df85f85f7df7df7e186185f85f7df86185f85f7df",
    "7e186186185f86185f85f7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock052OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock052OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block052_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock052Input a) =
      generatedSixthXiShortBlock052InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock052Output a) =
      generatedSixthXiShortBlock052OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock052Input a) =
      generatedSixthXiShortBlock052InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock052Output a) =
      generatedSixthXiShortBlock052OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block052_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock052InputMask a) =
      generatedSixthXiShortBlock052OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock052InputMask a)) *
      generatedSixthXiShortBlock052InputNumerator a =
        generatedSixthXiShortBlock052OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block052_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock052Input a
    let y := generatedSixthXiShortBlock052Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block052_cache a
  have hs := generatedSixth_xi_short_block052_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block052_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock052Input a
    let y := generatedSixthXiShortBlock052Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block052_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block052_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock052Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block052_certificate a).1
    (generatedSixth_xi_short_block052_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
