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
def generatedSixthXiShortBlock068Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (88, 58)),
    Sum.inr (Sum.inl (81, 10)),
    Sum.inr (Sum.inl (83, 41)),
    Sum.inr (Sum.inl (87, 43)),
    Sum.inr (Sum.inl (83, 57)),
    Sum.inr (Sum.inl (88, 4)),
    Sum.inr (Sum.inl (81, 46)),
    Sum.inr (Sum.inl (87, 21)),
    Sum.inr (Sum.inl (3, 37)),
    Sum.inr (Sum.inl (3, 21)),
    Sum.inr (Sum.inl (23, 23)),
    Sum.inr (Sum.inl (3, 53)),
    Sum.inr (Sum.inl (83, 43)),
    Sum.inr (Sum.inl (81, 49)),
    Sum.inr (Sum.inl (87, 10)),
    Sum.inr (Sum.inl (88, 21)),
    Sum.inr (Sum.inl (196, 26)),
    Sum.inr (Sum.inl (195, 58)),
    Sum.inr (Sum.inl (144, 27)),
    Sum.inr (Sum.inl (167, 9)),
    Sum.inr (Sum.inl (32, 43)),
    Sum.inr (Sum.inl (12, 9)),
    Sum.inr (Sum.inl (32, 35)),
    Sum.inr (Sum.inl (32, 47)),
    Sum.inr (Sum.inl (196, 11)),
    Sum.inr (Sum.inl (144, 59)),
    Sum.inr (Sum.inl (167, 43)),
    Sum.inr (Sum.inl (195, 26)),
    Sum.inr (Sum.inl (167, 41)),
    Sum.inr (Sum.inl (196, 36)),
    Sum.inr (Sum.inl (144, 57)),
    Sum.inr (Sum.inl (195, 50)),
    Sum.inr (Sum.inl (12, 41)),
    Sum.inr (Sum.inl (12, 25)),
    Sum.inr (Sum.inl (32, 39)),
    Sum.inr (Sum.inl (12, 57)),
    Sum.inr (Sum.inl (167, 11)),
    Sum.inr (Sum.inl (144, 25)),
    Sum.inr (Sum.inl (195, 18)),
    Sum.inr (Sum.inl (196, 53)),
    Sum.inr (Sum.inr (493, 23)),
    Sum.inr (Sum.inr (428, 1)),
    Sum.inr (Sum.inr (364, 9)),
    Sum.inr (Sum.inr (294, 12)),
    Sum.inr (Sum.inr (243, 18)),
    Sum.inr (Sum.inr (248, 5)),
    Sum.inr (Sum.inr (243, 7)),
    Sum.inr (Sum.inr (243, 6)),
    Sum.inr (Sum.inr (493, 13)),
    Sum.inr (Sum.inr (364, 2)),
    Sum.inr (Sum.inr (294, 20)),
    Sum.inr (Sum.inr (428, 11)),
    Sum.inr (Sum.inr (294, 3)),
    Sum.inr (Sum.inr (493, 8)),
    Sum.inr (Sum.inr (364, 21)),
    Sum.inr (Sum.inr (428, 15)),
    Sum.inr (Sum.inr (248, 16)),
    Sum.inr (Sum.inr (248, 17)),
    Sum.inr (Sum.inr (243, 4)),
    Sum.inr (Sum.inr (248, 19)),
    Sum.inr (Sum.inr (294, 10)),
    Sum.inr (Sum.inr (364, 14)),
    Sum.inr (Sum.inr (428, 22)),
    Sum.inr (Sum.inr (493, 0)),
    Sum.inr (Sum.inr (300, 13)),
    Sum.inr (Sum.inr (365, 11)),
    Sum.inr (Sum.inr (429, 2)),
    Sum.inr (Sum.inr (487, 20)),
    Sum.inr (Sum.inr (50, 18)),
    Sum.inr (Sum.inr (57, 5)),
    Sum.inr (Sum.inr (50, 7)),
    Sum.inr (Sum.inr (50, 6)),
    Sum.inr (Sum.inr (300, 23)),
    Sum.inr (Sum.inr (429, 9)),
    Sum.inr (Sum.inr (487, 12)),
    Sum.inr (Sum.inr (365, 1)),
    Sum.inr (Sum.inr (487, 10)),
    Sum.inr (Sum.inr (300, 0)),
    Sum.inr (Sum.inr (429, 14)),
    Sum.inr (Sum.inr (365, 22)),
    Sum.inr (Sum.inr (57, 16)),
    Sum.inr (Sum.inr (57, 17)),
    Sum.inr (Sum.inr (50, 4)),
    Sum.inr (Sum.inr (57, 19)),
    Sum.inr (Sum.inr (487, 3)),
    Sum.inr (Sum.inr (429, 21)),
    Sum.inr (Sum.inr (365, 15)),
    Sum.inr (Sum.inr (300, 8)),
    Sum.inr (Sum.inr (357, 8)),
    Sum.inr (Sum.inr (292, 15)),
    Sum.inr (Sum.inr (484, 21)),
    Sum.inr (Sum.inr (430, 3)),
    Sum.inr (Sum.inr (123, 18)),
    Sum.inr (Sum.inr (112, 5)),
    Sum.inr (Sum.inr (123, 7)),
    Sum.inr (Sum.inr (123, 6)),
    Sum.inr (Sum.inr (357, 0)),
    Sum.inr (Sum.inr (484, 14)),
    Sum.inr (Sum.inr (430, 10)),
    Sum.inr (Sum.inr (292, 22)),
    Sum.inr (Sum.inr (430, 12)),
    Sum.inr (Sum.inr (357, 23)),
    Sum.inr (Sum.inr (484, 9)),
    Sum.inr (Sum.inr (292, 1)),
    Sum.inr (Sum.inr (112, 16)),
    Sum.inr (Sum.inr (112, 17)),
    Sum.inr (Sum.inr (123, 4)),
    Sum.inr (Sum.inr (112, 19)),
    Sum.inr (Sum.inr (430, 20)),
    Sum.inr (Sum.inr (484, 2)),
    Sum.inr (Sum.inr (292, 11)),
    Sum.inr (Sum.inr (357, 13)),
    Sum.inr (Sum.inr (431, 0)),
    Sum.inr (Sum.inr (494, 22)),
    Sum.inr (Sum.inr (302, 14)),
    Sum.inr (Sum.inr (356, 10)),
    Sum.inr (Sum.inr (177, 18)),
    Sum.inr (Sum.inr (186, 5)),
    Sum.inr (Sum.inr (177, 7)),
    Sum.inr (Sum.inr (177, 6)),
    Sum.inr (Sum.inr (431, 8)),
    Sum.inr (Sum.inr (302, 21)),
    Sum.inr (Sum.inr (356, 3)),
    Sum.inr (Sum.inr (494, 15)),
    Sum.inr (Sum.inr (356, 20)),
    Sum.inr (Sum.inr (431, 13)),
    Sum.inr (Sum.inr (302, 2)),
    Sum.inr (Sum.inr (494, 11)),
    Sum.inr (Sum.inr (186, 16)),
    Sum.inr (Sum.inr (186, 17)),
    Sum.inr (Sum.inr (177, 4)),
    Sum.inr (Sum.inr (186, 19)),
    Sum.inr (Sum.inr (356, 12)),
    Sum.inr (Sum.inr (302, 9)),
    Sum.inr (Sum.inr (494, 1)),
    Sum.inr (Sum.inr (431, 23)),
    Sum.inr (Sum.inl (196, 22)),
    Sum.inr (Sum.inl (195, 57)),
    Sum.inr (Sum.inl (144, 23)),
    Sum.inr (Sum.inl (167, 5)),
    Sum.inr (Sum.inl (32, 37)),
    Sum.inr (Sum.inl (12, 59)),
    Sum.inr (Sum.inl (32, 45)),
    Sum.inr (Sum.inl (32, 33)),
    Sum.inr (Sum.inl (196, 7)),
    Sum.inr (Sum.inl (144, 55)),
    Sum.inr (Sum.inl (167, 39)),
    Sum.inr (Sum.inl (195, 25)),
    Sum.inr (Sum.inl (167, 37)),
    Sum.inr (Sum.inl (196, 40)),
    Sum.inr (Sum.inl (144, 53)),
    Sum.inr (Sum.inl (195, 49)),
    Sum.inr (Sum.inl (12, 27)),
    Sum.inr (Sum.inl (12, 43)),
    Sum.inr (Sum.inl (32, 41)),
    Sum.inr (Sum.inl (12, 11)),
    Sum.inr (Sum.inl (167, 7)),
    Sum.inr (Sum.inl (144, 21)),
    Sum.inr (Sum.inl (195, 17)),
    Sum.inr (Sum.inl (196, 57)),
    Sum.inr (Sum.inl (88, 39)),
    Sum.inr (Sum.inl (87, 56)),
    Sum.inr (Sum.inl (81, 22)),
    Sum.inr (Sum.inl (83, 55)),
    Sum.inr (Sum.inl (23, 21)),
    Sum.inr (Sum.inl (3, 55)),
    Sum.inr (Sum.inl (23, 29)),
    Sum.inr (Sum.inl (23, 17)),
    Sum.inr (Sum.inl (88, 54)),
    Sum.inr (Sum.inl (81, 9)),
    Sum.inr (Sum.inl (83, 37)),
    Sum.inr (Sum.inl (87, 39)),
    Sum.inr (Sum.inl (83, 53)),
    Sum.inr (Sum.inl (88, 8)),
    Sum.inr (Sum.inl (81, 45)),
    Sum.inr (Sum.inl (87, 25)),
    Sum.inr (Sum.inl (3, 23)),
    Sum.inr (Sum.inl (3, 39)),
    Sum.inr (Sum.inl (23, 25)),
    Sum.inr (Sum.inl (3, 7)),
    Sum.inr (Sum.inl (83, 39)),
    Sum.inr (Sum.inl (81, 50)),
    Sum.inr (Sum.inl (87, 6)),
    Sum.inr (Sum.inl (88, 25)),
    Sum.inr (Sum.inl (133, 53)),
    Sum.inr (Sum.inl (132, 42)),
    Sum.inr (Sum.inl (126, 43)),
    Sum.inr (Sum.inl (128, 61)),
    Sum.inr (Sum.inl (26, 52)),
    Sum.inr (Sum.inl (6, 62)),
    Sum.inr (Sum.inl (26, 60)),
    Sum.inr (Sum.inl (26, 48)),
    Sum.inr (Sum.inl (133, 26)),
    Sum.inr (Sum.inl (126, 10)),
    Sum.inr (Sum.inl (128, 45)),
    Sum.inr (Sum.inl (132, 11)),
    Sum.inr (Sum.inl (128, 53)),
    Sum.inr (Sum.inl (133, 36)),
    Sum.inr (Sum.inl (126, 42)),
    Sum.inr (Sum.inl (132, 53)),
    Sum.inr (Sum.inl (6, 30)),
    Sum.inr (Sum.inl (6, 46)),
    Sum.inr (Sum.inl (26, 56)),
    Sum.inr (Sum.inl (6, 14)),
    Sum.inr (Sum.inl (128, 37)),
    Sum.inr (Sum.inl (126, 11)),
    Sum.inr (Sum.inl (132, 20)),
    Sum.inr (Sum.inl (133, 11)),
    Sum.inr (Sum.inl (210, 18)),
    Sum.inr (Sum.inl (204, 10)),
    Sum.inr (Sum.inl (147, 8)),
    Sum.inr (Sum.inl (170, 26)),
    Sum.inr (Sum.inl (35, 10)),
    Sum.inr (Sum.inl (15, 0)),
    Sum.inr (Sum.inl (35, 2)),
    Sum.inr (Sum.inl (35, 14)),
    Sum.inr (Sum.inl (210, 61)),
    Sum.inr (Sum.inl (147, 26)),
    Sum.inr (Sum.inl (170, 10)),
    Sum.inr (Sum.inl (204, 40)),
    Sum.inr (Sum.inl (170, 8)),
    Sum.inr (Sum.inl (210, 41)),
    Sum.inr (Sum.inl (147, 24)),
    Sum.inr (Sum.inl (204, 55)),
    Sum.inr (Sum.inl (15, 32)),
    Sum.inr (Sum.inl (15, 16)),
    Sum.inr (Sum.inl (35, 6)),
    Sum.inr (Sum.inl (15, 48)),
    Sum.inr (Sum.inl (170, 24)),
    Sum.inr (Sum.inl (147, 10)),
    Sum.inr (Sum.inl (204, 21)),
    Sum.inr (Sum.inl (210, 6)),
    Sum.inr (Sum.inl (71, 33)),
    Sum.inr (Sum.inl (70, 17)),
    Sum.inr (Sum.inl (64, 32)),
    Sum.inr (Sum.inl (66, 28)),
    Sum.inr (Sum.inl (22, 18)),
    Sum.inr (Sum.inl (2, 52)),
    Sum.inr (Sum.inl (22, 24)),
    Sum.inr (Sum.inl (22, 26)),
    Sum.inr (Sum.inl (71, 48)),
    Sum.inr (Sum.inl (64, 0)),
    Sum.inr (Sum.inl (66, 12)),
    Sum.inr (Sum.inl (70, 48)),
    Sum.inr (Sum.inl (66, 20)),
    Sum.inr (Sum.inl (71, 14)),
    Sum.inr (Sum.inl (64, 1)),
    Sum.inr (Sum.inl (70, 47)),
    Sum.inr (Sum.inl (2, 20)),
    Sum.inr (Sum.inl (2, 36)),
    Sum.inr (Sum.inl (22, 16)),
    Sum.inr (Sum.inl (2, 4)),
    Sum.inr (Sum.inl (66, 4)),
    Sum.inr (Sum.inl (64, 33)),
    Sum.inr (Sum.inl (70, 14)),
    Sum.inr (Sum.inl (71, 31))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock068Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨17408 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock068InputMaskData : ℕ :=
  sixthHex% [
    "d82180ee2980f52980832180e4e180fae180dde18083e180fc8180d68980",
    "e98980838180c0b180c2b180c1b18083b180cfa980c7a180cba98083a180",
    "b35980935980a35180c35180d9495fef495ff4495f82495fe5895ffb895f",
    "dc895f82895ffde15fd7e15fe8e95f82e95fc1d15fc3d15fc0d95f82d95f",
    "cec95fc6c95fcac15f82c15fb2395f92395fa2315fc2315fbba15e8da15e",
    "96a15ee0a15e87615e99615ebe615ee0615e9f095eb5095e8a015ee0015e",
    "a3315ea1315ea2395ee0395eac215ea4215ea8295ee0295ed0d95ef0d95e",
    "c0d15ea0d15e93915da5915dbe915dc8915daf515db1515d96515dc8515d",
    "b7315d9d315da2395dc8395d8b095d89095d8a015dc8015d84115d8c115d",
    "80195dc8195df8e95dd8e95de8e15d88e15db1795c87795c9c795cea795c",
    "8db95c93b95cb4b95ceab95c95d95cbfd95c80d15cead15ca9e95cabe95c",
    "a8e15ceae15ca6f95caef95ca2f15ceaf15cda095cfa095cca015caa015c",
    "b9f95b8ff95b94f95be2f95b85315b9b315bbc315be2315b9d515bb7515b",
    "88595be2595ba1615ba3615ba0695be2695bae795ba6795baa715be2715b",
    "d2815bf2815bc2895ba2895b9b115aad115ab6115ac0115aa7d95ab9d95a",
    "9ed95ac0d95abfb95a95b95aaab15ac0b15a83815a81815a82895ac0895a",
    "8c915a84915a88995ac0995af0615ad0615ae0695a80695ab32159852159",
    "9e2159e821598fe95991e959b6e959e8e959978159bd8159828959e88959",
    "abb959a9b959aab159e8b159a4a159aca159a0a959e8a959d85159f85159",
    "c85959a85959d1c958e7c958fcc9588ac958ed0158f30158d401588a0158",
    "f56958df6958e061588a6158c95958cb5958c851588a5158c64958ce4958",
    "c241588a4158bab1589ab158aab958cab958b931578f3157943157e23157",
    "85f9579bf957bcf957e2f9579d9157b79157889957e29957a1a157a3a157",
    "a0a957e2a957aeb957a6b957aab157e2b157d24157f24157c24957a24957",
    "9bd956add956b6d956c0d956a71156b911569e1156c01156bf7956957956",
    "aa7156c07156834156814156824956c04956"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock068InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock068InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock068OutputMaskData : ℕ :=
  sixthHex% [
    "5d13910b12a00689802588ba4b5fd4605fdf725fd42c5fd468faa0252980",
    "1dfb912528ba54caa06418ba4351800683912457df5d1fdf1557d4191fdf",
    "64b0ba60f980372aa046639131b86e16f95f1b627f49234527f42b0cf420",
    "1ef42b40f42b75115f49827f00106e49834549215f79f3452ffa7f6a286e",
    "39bc2031b42079fc2b04f420795b457d127f2ac15f5b886e372b4f106a7e",
    "1df15e4fb06421670a0a670118670a46670a73827e4f115e06834f4f1064",
    "3ef27e0e206458295e1dfb4f3f2f013727017f6f0a0267010e88640ac15e",
    "5d127e2c5b4f136a76342b4739b0676bf15d0526332e26383c2633622633",
    "2683471a10675382761a115d6bf3475b215d0d286748fa761b6e38136638",
    "5b2e332626382ac95d2e8067795347081a7660f95c47b86d4a234d186277",
    "76b5195db5124fb51911b51955106d69834d20115c69827769206d59f277",
    "0ffb4d4a295c68fd1260f51228bd1955b512281a772c534d7b806d0ac95c",
    "de4e8ff90fbef4949ea6d5a4b942ca9242c18042cade42ca9ae7bea6749e",
    "efe68fa675a4a6d7be9605a4c00c9e85de8fd64ac1de42c1960acaeb02c1",
    "e7eda4e3a49eb477bec53e8faddda58a9c948707b4d5468ecad1e0e1d1eb",
    "f3d1e0add1e0e97494d5e7b49c75a5d5e68ea4049494d68ec2dfb4870da5",
    "a5d9ebadd1ebe599e09891ebe53e8ee177b4b6a494c7eda5899c9caeddad",
    "a3468df107b7ee90d9c590d2d790d98990d9bc75ad80e68dc9749c80e7b7",
    "f105adc1d7b797de8dd20c9c8198d28990d2c1d8d9bcd0d2c17fb7c5368d",
    "92e5ade3ac9c8f0fbda84e8ca5d5acf79496e803f8c303f3d103f88f03f8",
    "bae68c8675accfe7bd86749686d68cb60496e00daca5dfbd870bf38f03f3",
    "c74bf8ba43f3b6ac96b2e5ace5368c947fbd28f95c0fb86d02234d506277",
    "4ff51964f51276f51928f5191d106d21834d68115c21827721206d11f277",
    "47fb4d02295c51bd1259b51211fd196cf512601a7764534d33806d42c95c",
    "5b6a767c2b4771b06723f15d3c66331766380566335b66336e8347521067",
    "1b827652115d23f34713215d45286700fa76"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock068OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock068OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock068InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock068InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock068InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock068OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e185f85f96175d85f7e17df861",
    "7df7df7e17e185f7e196175d8617df85f85f7df7df7e185f85f85f96175d",
    "7e185f7df8617df7df85f85f7e185f6df8e38617df7e17e18618617e185f",
    "86185f95f75d85f8617df7e185f7df7df85f8617e195f75d86185f85f7df",
    "85f7df7df7e186185f95f75d7e17df7df7e185f7df8617e18617e195f75d",
    "7df7e185f7df85f7df86185f7e185f6df8e38617df7e17e18618617e185f",
    "85f85f96175d7e185f7df861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock068OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock068OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block068_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock068Input a) =
      generatedSixthXiShortBlock068InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock068Output a) =
      generatedSixthXiShortBlock068OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock068Input a) =
      generatedSixthXiShortBlock068InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock068Output a) =
      generatedSixthXiShortBlock068OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block068_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock068InputMask a) =
      generatedSixthXiShortBlock068OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock068InputMask a)) *
      generatedSixthXiShortBlock068InputNumerator a =
        generatedSixthXiShortBlock068OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block068_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock068Input a
    let y := generatedSixthXiShortBlock068Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block068_cache a
  have hs := generatedSixth_xi_short_block068_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block068_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock068Input a
    let y := generatedSixthXiShortBlock068Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block068_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block068_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock068Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block068_certificate a).1
    (generatedSixth_xi_short_block068_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
