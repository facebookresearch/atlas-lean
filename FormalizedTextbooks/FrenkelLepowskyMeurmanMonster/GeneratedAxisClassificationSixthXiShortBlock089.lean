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
def generatedSixthXiShortBlock089Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (104, 61)),
    Sum.inr (Sum.inl (97, 37)),
    Sum.inr (Sum.inl (99, 8)),
    Sum.inr (Sum.inl (103, 55)),
    Sum.inr (Sum.inl (99, 10)),
    Sum.inr (Sum.inl (104, 25)),
    Sum.inr (Sum.inl (97, 10)),
    Sum.inr (Sum.inl (103, 10)),
    Sum.inr (Sum.inl (4, 18)),
    Sum.inr (Sum.inl (4, 34)),
    Sum.inr (Sum.inl (24, 10)),
    Sum.inr (Sum.inl (4, 2)),
    Sum.inr (Sum.inl (99, 24)),
    Sum.inr (Sum.inl (97, 24)),
    Sum.inr (Sum.inl (103, 21)),
    Sum.inr (Sum.inl (104, 6)),
    Sum.inr (Sum.inl (179, 23)),
    Sum.inr (Sum.inl (178, 45)),
    Sum.inr (Sum.inl (142, 42)),
    Sum.inr (Sum.inl (165, 55)),
    Sum.inr (Sum.inl (30, 23)),
    Sum.inr (Sum.inl (10, 5)),
    Sum.inr (Sum.inl (30, 29)),
    Sum.inr (Sum.inl (30, 31)),
    Sum.inr (Sum.inl (179, 56)),
    Sum.inr (Sum.inl (142, 8)),
    Sum.inr (Sum.inl (165, 21)),
    Sum.inr (Sum.inl (178, 50)),
    Sum.inr (Sum.inl (165, 53)),
    Sum.inr (Sum.inl (179, 6)),
    Sum.inr (Sum.inl (142, 53)),
    Sum.inr (Sum.inl (178, 26)),
    Sum.inr (Sum.inl (10, 37)),
    Sum.inr (Sum.inl (10, 21)),
    Sum.inr (Sum.inl (30, 21)),
    Sum.inr (Sum.inl (10, 53)),
    Sum.inr (Sum.inl (165, 23)),
    Sum.inr (Sum.inl (142, 23)),
    Sum.inr (Sum.inl (178, 5)),
    Sum.inr (Sum.inl (179, 41)),
    Sum.inr (Sum.inr (141, 8)),
    Sum.inr (Sum.inr (204, 1)),
    Sum.inr (Sum.inr (12, 14)),
    Sum.inr (Sum.inr (70, 20)),
    Sum.inr (Sum.inr (403, 6)),
    Sum.inr (Sum.inr (408, 5)),
    Sum.inr (Sum.inr (403, 4)),
    Sum.inr (Sum.inr (403, 18)),
    Sum.inr (Sum.inr (141, 0)),
    Sum.inr (Sum.inr (12, 21)),
    Sum.inr (Sum.inr (70, 12)),
    Sum.inr (Sum.inr (204, 11)),
    Sum.inr (Sum.inr (70, 10)),
    Sum.inr (Sum.inr (141, 23)),
    Sum.inr (Sum.inr (12, 2)),
    Sum.inr (Sum.inr (204, 15)),
    Sum.inr (Sum.inr (408, 16)),
    Sum.inr (Sum.inr (408, 17)),
    Sum.inr (Sum.inr (403, 7)),
    Sum.inr (Sum.inr (408, 19)),
    Sum.inr (Sum.inr (70, 3)),
    Sum.inr (Sum.inr (12, 9)),
    Sum.inr (Sum.inr (204, 22)),
    Sum.inr (Sum.inr (141, 13)),
    Sum.inr (Sum.inr (205, 0)),
    Sum.inr (Sum.inr (140, 11)),
    Sum.inr (Sum.inr (76, 21)),
    Sum.inr (Sum.inr (6, 12)),
    Sum.inr (Sum.inr (467, 6)),
    Sum.inr (Sum.inr (472, 5)),
    Sum.inr (Sum.inr (467, 4)),
    Sum.inr (Sum.inr (467, 18)),
    Sum.inr (Sum.inr (205, 8)),
    Sum.inr (Sum.inr (76, 14)),
    Sum.inr (Sum.inr (6, 20)),
    Sum.inr (Sum.inr (140, 1)),
    Sum.inr (Sum.inr (6, 3)),
    Sum.inr (Sum.inr (205, 13)),
    Sum.inr (Sum.inr (76, 9)),
    Sum.inr (Sum.inr (140, 22)),
    Sum.inr (Sum.inr (472, 16)),
    Sum.inr (Sum.inr (472, 17)),
    Sum.inr (Sum.inr (467, 7)),
    Sum.inr (Sum.inr (472, 19)),
    Sum.inr (Sum.inr (6, 10)),
    Sum.inr (Sum.inr (76, 2)),
    Sum.inr (Sum.inr (140, 15)),
    Sum.inr (Sum.inr (205, 23)),
    Sum.inr (Sum.inr (79, 23)),
    Sum.inr (Sum.inr (14, 15)),
    Sum.inr (Sum.inr (206, 2)),
    Sum.inr (Sum.inr (132, 10)),
    Sum.inr (Sum.inr (337, 6)),
    Sum.inr (Sum.inr (346, 5)),
    Sum.inr (Sum.inr (337, 4)),
    Sum.inr (Sum.inr (337, 18)),
    Sum.inr (Sum.inr (79, 13)),
    Sum.inr (Sum.inr (206, 9)),
    Sum.inr (Sum.inr (132, 3)),
    Sum.inr (Sum.inr (14, 22)),
    Sum.inr (Sum.inr (132, 20)),
    Sum.inr (Sum.inr (79, 8)),
    Sum.inr (Sum.inr (206, 14)),
    Sum.inr (Sum.inr (14, 1)),
    Sum.inr (Sum.inr (346, 16)),
    Sum.inr (Sum.inr (346, 17)),
    Sum.inr (Sum.inr (337, 7)),
    Sum.inr (Sum.inr (346, 19)),
    Sum.inr (Sum.inr (132, 12)),
    Sum.inr (Sum.inr (206, 21)),
    Sum.inr (Sum.inr (14, 11)),
    Sum.inr (Sum.inr (79, 0)),
    Sum.inr (Sum.inr (4, 13)),
    Sum.inr (Sum.inr (69, 22)),
    Sum.inr (Sum.inr (133, 9)),
    Sum.inr (Sum.inr (207, 3)),
    Sum.inr (Sum.inr (282, 6)),
    Sum.inr (Sum.inr (273, 5)),
    Sum.inr (Sum.inr (282, 4)),
    Sum.inr (Sum.inr (282, 18)),
    Sum.inr (Sum.inr (4, 23)),
    Sum.inr (Sum.inr (133, 2)),
    Sum.inr (Sum.inr (207, 10)),
    Sum.inr (Sum.inr (69, 15)),
    Sum.inr (Sum.inr (207, 12)),
    Sum.inr (Sum.inr (4, 0)),
    Sum.inr (Sum.inr (133, 21)),
    Sum.inr (Sum.inr (69, 11)),
    Sum.inr (Sum.inr (273, 16)),
    Sum.inr (Sum.inr (273, 17)),
    Sum.inr (Sum.inr (282, 7)),
    Sum.inr (Sum.inr (273, 19)),
    Sum.inr (Sum.inr (207, 20)),
    Sum.inr (Sum.inr (133, 14)),
    Sum.inr (Sum.inr (69, 1)),
    Sum.inr (Sum.inr (4, 8)),
    Sum.inr (Sum.inl (179, 27)),
    Sum.inr (Sum.inl (178, 46)),
    Sum.inr (Sum.inl (142, 38)),
    Sum.inr (Sum.inl (165, 59)),
    Sum.inr (Sum.inl (30, 25)),
    Sum.inr (Sum.inl (10, 55)),
    Sum.inr (Sum.inl (30, 19)),
    Sum.inr (Sum.inl (30, 17)),
    Sum.inr (Sum.inl (179, 52)),
    Sum.inr (Sum.inl (142, 4)),
    Sum.inr (Sum.inl (165, 25)),
    Sum.inr (Sum.inl (178, 49)),
    Sum.inr (Sum.inl (165, 57)),
    Sum.inr (Sum.inl (179, 10)),
    Sum.inr (Sum.inl (142, 57)),
    Sum.inr (Sum.inl (178, 25)),
    Sum.inr (Sum.inl (10, 23)),
    Sum.inr (Sum.inl (10, 39)),
    Sum.inr (Sum.inl (30, 27)),
    Sum.inr (Sum.inl (10, 7)),
    Sum.inr (Sum.inl (165, 27)),
    Sum.inr (Sum.inl (142, 27)),
    Sum.inr (Sum.inl (178, 6)),
    Sum.inr (Sum.inl (179, 37)),
    Sum.inr (Sum.inl (104, 33)),
    Sum.inr (Sum.inl (103, 36)),
    Sum.inr (Sum.inl (97, 59)),
    Sum.inr (Sum.inl (99, 22)),
    Sum.inr (Sum.inl (24, 6)),
    Sum.inr (Sum.inl (4, 0)),
    Sum.inr (Sum.inl (24, 12)),
    Sum.inr (Sum.inl (24, 14)),
    Sum.inr (Sum.inl (104, 62)),
    Sum.inr (Sum.inl (97, 41)),
    Sum.inr (Sum.inl (99, 4)),
    Sum.inr (Sum.inl (103, 59)),
    Sum.inr (Sum.inl (99, 6)),
    Sum.inr (Sum.inl (104, 26)),
    Sum.inr (Sum.inl (97, 6)),
    Sum.inr (Sum.inl (103, 6)),
    Sum.inr (Sum.inl (4, 32)),
    Sum.inr (Sum.inl (4, 16)),
    Sum.inr (Sum.inl (24, 4)),
    Sum.inr (Sum.inl (4, 48)),
    Sum.inr (Sum.inl (99, 20)),
    Sum.inr (Sum.inl (97, 20)),
    Sum.inr (Sum.inl (103, 25)),
    Sum.inr (Sum.inl (104, 5)),
    Sum.inr (Sum.inl (215, 7)),
    Sum.inr (Sum.inl (209, 25)),
    Sum.inr (Sum.inl (152, 46)),
    Sum.inr (Sum.inl (175, 40)),
    Sum.inr (Sum.inl (40, 56)),
    Sum.inr (Sum.inl (20, 62)),
    Sum.inr (Sum.inl (40, 50)),
    Sum.inr (Sum.inl (40, 48)),
    Sum.inr (Sum.inl (215, 22)),
    Sum.inr (Sum.inl (152, 62)),
    Sum.inr (Sum.inl (175, 56)),
    Sum.inr (Sum.inl (209, 56)),
    Sum.inr (Sum.inl (175, 58)),
    Sum.inr (Sum.inl (215, 6)),
    Sum.inr (Sum.inl (152, 42)),
    Sum.inr (Sum.inl (209, 57)),
    Sum.inr (Sum.inl (20, 30)),
    Sum.inr (Sum.inl (20, 46)),
    Sum.inr (Sum.inl (40, 58)),
    Sum.inr (Sum.inl (20, 14)),
    Sum.inr (Sum.inl (175, 42)),
    Sum.inr (Sum.inl (152, 58)),
    Sum.inr (Sum.inl (209, 24)),
    Sum.inr (Sum.inl (215, 23)),
    Sum.inr (Sum.inl (71, 41)),
    Sum.inr (Sum.inl (70, 7)),
    Sum.inr (Sum.inl (64, 23)),
    Sum.inr (Sum.inl (66, 33)),
    Sum.inr (Sum.inl (22, 39)),
    Sum.inr (Sum.inl (2, 9)),
    Sum.inr (Sum.inl (22, 45)),
    Sum.inr (Sum.inl (22, 47)),
    Sum.inr (Sum.inl (71, 56)),
    Sum.inr (Sum.inl (64, 55)),
    Sum.inr (Sum.inl (66, 49)),
    Sum.inr (Sum.inl (70, 38)),
    Sum.inr (Sum.inl (66, 41)),
    Sum.inr (Sum.inl (71, 6)),
    Sum.inr (Sum.inl (64, 54)),
    Sum.inr (Sum.inl (70, 57)),
    Sum.inr (Sum.inl (2, 41)),
    Sum.inr (Sum.inl (2, 25)),
    Sum.inr (Sum.inl (22, 37)),
    Sum.inr (Sum.inl (2, 57)),
    Sum.inr (Sum.inl (66, 57)),
    Sum.inr (Sum.inl (64, 22)),
    Sum.inr (Sum.inl (70, 24)),
    Sum.inr (Sum.inl (71, 23)),
    Sum.inr (Sum.inl (133, 31)),
    Sum.inr (Sum.inl (132, 62)),
    Sum.inr (Sum.inl (126, 63)),
    Sum.inr (Sum.inl (128, 56)),
    Sum.inr (Sum.inl (26, 40)),
    Sum.inr (Sum.inl (6, 56)),
    Sum.inr (Sum.inl (26, 32)),
    Sum.inr (Sum.inl (26, 44)),
    Sum.inr (Sum.inl (133, 48)),
    Sum.inr (Sum.inl (126, 30)),
    Sum.inr (Sum.inl (128, 40)),
    Sum.inr (Sum.inl (132, 31)),
    Sum.inr (Sum.inl (128, 48)),
    Sum.inr (Sum.inl (133, 14)),
    Sum.inr (Sum.inl (126, 62)),
    Sum.inr (Sum.inl (132, 33)),
    Sum.inr (Sum.inl (6, 24)),
    Sum.inr (Sum.inl (6, 40)),
    Sum.inr (Sum.inl (26, 36)),
    Sum.inr (Sum.inl (6, 8)),
    Sum.inr (Sum.inl (128, 32)),
    Sum.inr (Sum.inl (126, 31)),
    Sum.inr (Sum.inl (132, 0)),
    Sum.inr (Sum.inl (133, 33))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock089Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨22784 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock089InputMaskData : ℕ :=
  sixthHex% [
    "f35d10c55510de5510a85510cf9510d19d10f69510a89510d7fd10fdfd10",
    "c2fd10a8f510ebc510e9c510eacd10a8c510e4dd10ecdd10e0dd10a8d510",
    "982d10b82d10882510e82d10a7acff91acff8aa4fffcacff9b6cff8564ff",
    "a26cfffc6cff8304ffa904ff9604fffc0cffbf34ffbd3cffbe3cfffc3cff",
    "b02cffb824ffb424fffc24ffccd4ffecd4ffdcd4ffbcdcffe4a4fed2a4fe",
    "c9acfebfa4fed864fec66cfee164febf64fec00cfeea0cfed50cfebf04fe",
    "fc34fefe3cfefd3cfebf3cfef324fefb2cfef72cfebf2cfe8fd4feafd4fe",
    "9fd4feffdcfee7acfdd1acfdcaa4fdbcacfddb6cfdc564fde26cfdbc6cfd",
    "c30cfde90cfdd60cfdbc04fdff34fdfd3cfdfe3cfdbc3cfdf02cfdf824fd",
    "f424fdbc24fd8cdcfdacdcfd9cdcfdfcd4fde4acfcd2acfcc9a4fcbfacfc",
    "d86cfcc664fce16cfcbf6cfcc00cfcea0cfcd50cfcbf04fcfc3cfcfe34fc",
    "fd34fcbf34fcf32cfcfb24fcf724fcbf24fc8fd4fcafd4fc9fd4fcffdcfc",
    "dea4fbe8a4fbf3acfb85a4fbe26cfbfc64fbdb6cfb856cfbfa0cfbd00cfb",
    "ef0cfb8504fbc63cfbc434fbc734fb8534fbc924fbc12cfbcd2cfb852cfb",
    "b5d4fb95d4fba5d4fbc5dcfbdda4faeba4faf0acfa86a4fae16cfaff64fa",
    "d86cfa866cfaf90cfad30cfaec0cfa8604fac534fac73cfac43cfa863cfa",
    "ca24fac22cface2cfa862cfab6dcfa96dcfaa6dcfac6d4fadeacf9e8acf9",
    "f3a4f985acf9e264f9fc6cf9db64f98564f9fa0cf9d00cf9ef0cf98504f9",
    "c634f9c43cf9c73cf9853cf9c92cf9c124f9cd24f98524f9b5d4f995d4f9",
    "a5d4f9c5dcf99da4f8aba4f8b0acf8c6a4f8a16cf8bf64f8986cf8c66cf8",
    "b904f89304f8ac04f8c60cf88534f8873cf8843cf8c63cf88a24f8822cf8",
    "8e2cf8c62cf8f6d4f8d6d4f8e6d4f886dcf8d1acf7e7acf7fca4f78aacf7",
    "ed64f7f36cf7d464f78a64f7f50cf7df0cf7e00cf78a04f7c93cf7cb34f7",
    "c834f78a34f7c624f7ce2cf7c22cf78a2cf7bad4f79ad4f7aad4f7cadcf7",
    "d2acf6e4acf6ffa4f689acf6ee64f6f06cf6d764f68964f6f60cf6dc0cf6",
    "e30cf68904f6ca34f6c83cf6cb3cf6893cf6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock089InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock089InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock089OutputMaskData : ℕ :=
  sixthHex% [
    "46734f10727e1de95e4fa864217f0a7b3f01187f0a467f0a739a7e4f095e",
    "77db4f4f08643eea7e0e386458315e6ca34f4e7701467f017f770a733f01",
    "0e90640ad95e5d0a7e5d034f7c9b915bdaa02701800400ba6ad7d43097df",
    "53d7d40dd7d43832a004a1803c739104a0ba0402a04590ba62d980270b91",
    "749fdf0dd7df34dfd449d7df4538ba41718067e2a067eb915c3aa17b7b90",
    "07a0b024a18a4a76e41036ef7376e42d76e41893902400b01cd2a124018a",
    "55e39014718a3338b076eaa1543eef2d76ef147ee46976ef14d98a1090b0",
    "360390360aa10198b326d9825a02a279039817d4f64d94fd2ed4f670d4f6",
    "34718208e2a23030b308e3987901823893981fdaa25a08b3099cfd70d4fd",
    "49dcf634d4fd497b984d32a26ba1826ba8b32579880238b97ee3995de2a3",
    "3335cd6975c60a35cd5435cd1090b92c039914d1882c02a32ca0b96d32a3",
    "4a7b990fa9882d7dc65435c66d3dcd1035c61cdaa31893993e00b93e0988",
    "c05804e719359bc215b8c32fa75441fd144a9e5441c0544184f135b86215",
    "80b004b8632fb8c135f9532fde1a159bc804c85c4ab1144a881c41f5144a",
    "88bb2f8cf215aa6135aa6804e4b93fc3f80ebf232e9c221483b57ad9f571",
    "bab57ae4b57aa0100e9c832ea4513f9c8214ed600eacf2148bbb2ece693f",
    "ecbd7195f571acfd7ad1f571dd1a14d9532effc00effc93fb91b2d9e5a1c",
    "e2813cc18006de1768845763e71768b917688cf21cb0613c88b32db06006",
    "c1821c801006a7593ce28b2db11f63c85763f15f688c576380b80684f13c",
    "a2621ca26b2d99ba1dbefb2cc2200ce12136feb658a4f653c7b65899b658",
    "ac532c90c00ca8121d90c13690632cd1f136f6b80cb36a1d91be53e8f653",
    "d1fe58acf653d15936d5100cf3832cf38a1d2179880638b97ae39959e2a3",
    "4675cd1c35c67f75cd2175cd1490b928039910d1882802a328a0b96932a3",
    "4e7b990ba988583dc62175c6187dcd6575c618daa31c93993a00b93a0988",
    "0598b322d9825e02a27d03986294f638d4fd5b94f60594f63071820ce2a2",
    "3430b30ce3987d01823c93981bdaa25e08b3"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock089OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock089OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock089InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock089InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock089InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock089OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f6df8e37df8617e17e186186185f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df8616df8e38617df8618617e185f85f85f86186196175d",
    "85f7e185f7e185f7e185f7e17df8616df8e37df8618618617e185f7e17e1",
    "85f86195f75d7e17df85f8617df7e17df7e17e18616e18e386185f8617e1",
    "86185f8617e17e17df6e18e37e17df7e17df86185f7df7e17e18616e18e3",
    "7df7e18617e186185f7df85f7df8616df8e37df8618618617e185f7e17e1",
    "86186196175d85f7e185f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock089OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock089OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block089_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock089Input a) =
      generatedSixthXiShortBlock089InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock089Output a) =
      generatedSixthXiShortBlock089OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock089Input a) =
      generatedSixthXiShortBlock089InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock089Output a) =
      generatedSixthXiShortBlock089OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block089_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock089InputMask a) =
      generatedSixthXiShortBlock089OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock089InputMask a)) *
      generatedSixthXiShortBlock089InputNumerator a =
        generatedSixthXiShortBlock089OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block089_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock089Input a
    let y := generatedSixthXiShortBlock089Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block089_cache a
  have hs := generatedSixth_xi_short_block089_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block089_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock089Input a
    let y := generatedSixthXiShortBlock089Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block089_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block089_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock089Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block089_certificate a).1
    (generatedSixth_xi_short_block089_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
