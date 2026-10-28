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
def generatedSixthXiShortBlock051Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (55, 11)),
    Sum.inr (Sum.inr (360, 15)),
    Sum.inr (Sum.inr (355, 15)),
    Sum.inr (Sum.inr (60, 11)),
    Sum.inr (Sum.inr (247, 15)),
    Sum.inr (Sum.inr (424, 11)),
    Sum.inr (Sum.inr (419, 11)),
    Sum.inr (Sum.inr (252, 15)),
    Sum.inr (Sum.inr (189, 11)),
    Sum.inr (Sum.inr (482, 15)),
    Sum.inr (Sum.inr (489, 15)),
    Sum.inr (Sum.inr (182, 11)),
    Sum.inr (Sum.inr (125, 15)),
    Sum.inr (Sum.inr (290, 11)),
    Sum.inr (Sum.inr (297, 11)),
    Sum.inr (Sum.inr (118, 15)),
    Sum.inr (Sum.inr (189, 22)),
    Sum.inr (Sum.inr (482, 1)),
    Sum.inr (Sum.inr (489, 1)),
    Sum.inr (Sum.inr (182, 22)),
    Sum.inr (Sum.inr (125, 1)),
    Sum.inr (Sum.inr (290, 22)),
    Sum.inr (Sum.inr (297, 22)),
    Sum.inr (Sum.inr (118, 1)),
    Sum.inr (Sum.inr (55, 15)),
    Sum.inr (Sum.inr (360, 11)),
    Sum.inr (Sum.inr (355, 11)),
    Sum.inr (Sum.inr (60, 15)),
    Sum.inr (Sum.inr (247, 11)),
    Sum.inr (Sum.inr (424, 15)),
    Sum.inr (Sum.inr (419, 15)),
    Sum.inr (Sum.inr (252, 11)),
    Sum.inr (Sum.inr (55, 1)),
    Sum.inr (Sum.inr (360, 22)),
    Sum.inr (Sum.inr (355, 22)),
    Sum.inr (Sum.inr (60, 1)),
    Sum.inr (Sum.inr (247, 22)),
    Sum.inr (Sum.inr (424, 1)),
    Sum.inr (Sum.inr (419, 1)),
    Sum.inr (Sum.inr (252, 22)),
    Sum.inr (Sum.inr (189, 23)),
    Sum.inr (Sum.inr (118, 0)),
    Sum.inr (Sum.inr (55, 23)),
    Sum.inr (Sum.inr (252, 0)),
    Sum.inr (Sum.inr (360, 23)),
    Sum.inr (Sum.inr (419, 0)),
    Sum.inr (Sum.inr (482, 23)),
    Sum.inr (Sum.inr (297, 0)),
    Sum.inr (Sum.inr (355, 23)),
    Sum.inr (Sum.inr (424, 0)),
    Sum.inr (Sum.inr (489, 23)),
    Sum.inr (Sum.inr (290, 0)),
    Sum.inr (Sum.inr (182, 23)),
    Sum.inr (Sum.inr (125, 0)),
    Sum.inr (Sum.inr (60, 23)),
    Sum.inr (Sum.inr (247, 0)),
    Sum.inr (Sum.inr (118, 8)),
    Sum.inr (Sum.inr (189, 13)),
    Sum.inr (Sum.inr (252, 8)),
    Sum.inr (Sum.inr (55, 13)),
    Sum.inr (Sum.inr (419, 8)),
    Sum.inr (Sum.inr (360, 13)),
    Sum.inr (Sum.inr (297, 8)),
    Sum.inr (Sum.inr (482, 13)),
    Sum.inr (Sum.inr (424, 8)),
    Sum.inr (Sum.inr (355, 13)),
    Sum.inr (Sum.inr (290, 8)),
    Sum.inr (Sum.inr (489, 13)),
    Sum.inr (Sum.inr (125, 8)),
    Sum.inr (Sum.inr (182, 13)),
    Sum.inr (Sum.inr (247, 8)),
    Sum.inr (Sum.inr (60, 13)),
    Sum.inr (Sum.inr (247, 23)),
    Sum.inr (Sum.inr (60, 0)),
    Sum.inr (Sum.inr (125, 23)),
    Sum.inr (Sum.inr (182, 0)),
    Sum.inr (Sum.inr (290, 23)),
    Sum.inr (Sum.inr (489, 0)),
    Sum.inr (Sum.inr (424, 23)),
    Sum.inr (Sum.inr (355, 0)),
    Sum.inr (Sum.inr (297, 23)),
    Sum.inr (Sum.inr (482, 0)),
    Sum.inr (Sum.inr (419, 23)),
    Sum.inr (Sum.inr (360, 0)),
    Sum.inr (Sum.inr (252, 23)),
    Sum.inr (Sum.inr (55, 0)),
    Sum.inr (Sum.inr (118, 23)),
    Sum.inr (Sum.inr (189, 0)),
    Sum.inr (Sum.inr (60, 8)),
    Sum.inr (Sum.inr (247, 13)),
    Sum.inr (Sum.inr (182, 8)),
    Sum.inr (Sum.inr (125, 13)),
    Sum.inr (Sum.inr (489, 8)),
    Sum.inr (Sum.inr (290, 13)),
    Sum.inr (Sum.inr (355, 8)),
    Sum.inr (Sum.inr (424, 13)),
    Sum.inr (Sum.inr (482, 8)),
    Sum.inr (Sum.inr (297, 13)),
    Sum.inr (Sum.inr (360, 8)),
    Sum.inr (Sum.inr (419, 13)),
    Sum.inr (Sum.inr (55, 8)),
    Sum.inr (Sum.inr (252, 13)),
    Sum.inr (Sum.inr (189, 8)),
    Sum.inr (Sum.inr (118, 13)),
    Sum.inr (Sum.inl (80, 18)),
    Sum.inr (Sum.inl (226, 53)),
    Sum.inr (Sum.inl (80, 58)),
    Sum.inr (Sum.inl (226, 55)),
    Sum.inr (Sum.inl (67, 4)),
    Sum.inr (Sum.inl (47, 41)),
    Sum.inr (Sum.inl (67, 58)),
    Sum.inr (Sum.inl (47, 1)),
    Sum.inr (Sum.inl (123, 14)),
    Sum.inr (Sum.inl (110, 47)),
    Sum.inr (Sum.inl (123, 48)),
    Sum.inr (Sum.inl (110, 7)),
    Sum.inr (Sum.inl (190, 50)),
    Sum.inr (Sum.inl (197, 9)),
    Sum.inr (Sum.inl (190, 5)),
    Sum.inr (Sum.inl (197, 11)),
    Sum.inr (Sum.inl (123, 22)),
    Sum.inr (Sum.inl (110, 59)),
    Sum.inr (Sum.inl (123, 40)),
    Sum.inr (Sum.inl (110, 19)),
    Sum.inr (Sum.inl (190, 38)),
    Sum.inr (Sum.inl (197, 17)),
    Sum.inr (Sum.inl (190, 17)),
    Sum.inr (Sum.inl (197, 19)),
    Sum.inr (Sum.inl (80, 16)),
    Sum.inr (Sum.inl (226, 45)),
    Sum.inr (Sum.inl (80, 56)),
    Sum.inr (Sum.inl (226, 47)),
    Sum.inr (Sum.inl (67, 6)),
    Sum.inr (Sum.inl (47, 43)),
    Sum.inr (Sum.inl (67, 56)),
    Sum.inr (Sum.inl (47, 3)),
    Sum.inr (Sum.inl (67, 44)),
    Sum.inr (Sum.inl (47, 61)),
    Sum.inr (Sum.inl (67, 18)),
    Sum.inr (Sum.inl (47, 21)),
    Sum.inr (Sum.inl (80, 44)),
    Sum.inr (Sum.inl (226, 17)),
    Sum.inr (Sum.inl (80, 4)),
    Sum.inr (Sum.inl (226, 19)),
    Sum.inr (Sum.inl (190, 48)),
    Sum.inr (Sum.inl (197, 45)),
    Sum.inr (Sum.inl (190, 7)),
    Sum.inr (Sum.inl (197, 47)),
    Sum.inr (Sum.inl (123, 12)),
    Sum.inr (Sum.inl (110, 45)),
    Sum.inr (Sum.inl (123, 50)),
    Sum.inr (Sum.inl (110, 5)),
    Sum.inr (Sum.inl (190, 36)),
    Sum.inr (Sum.inl (197, 53)),
    Sum.inr (Sum.inl (190, 19)),
    Sum.inr (Sum.inl (197, 55)),
    Sum.inr (Sum.inl (123, 20)),
    Sum.inr (Sum.inl (110, 57)),
    Sum.inr (Sum.inl (123, 42)),
    Sum.inr (Sum.inl (110, 17)),
    Sum.inr (Sum.inl (67, 46)),
    Sum.inr (Sum.inl (47, 63)),
    Sum.inr (Sum.inl (67, 16)),
    Sum.inr (Sum.inl (47, 23)),
    Sum.inr (Sum.inl (80, 46)),
    Sum.inr (Sum.inl (226, 9)),
    Sum.inr (Sum.inl (80, 6)),
    Sum.inr (Sum.inl (226, 11)),
    Sum.inr (Sum.inl (65, 37)),
    Sum.inr (Sum.inl (93, 60)),
    Sum.inr (Sum.inl (65, 41)),
    Sum.inr (Sum.inl (93, 52)),
    Sum.inr (Sum.inl (136, 60)),
    Sum.inr (Sum.inl (49, 21)),
    Sum.inr (Sum.inl (136, 46)),
    Sum.inr (Sum.inl (49, 25)),
    Sum.inr (Sum.inl (189, 37)),
    Sum.inr (Sum.inl (95, 23)),
    Sum.inr (Sum.inl (189, 39)),
    Sum.inr (Sum.inl (95, 27)),
    Sum.inr (Sum.inl (229, 45)),
    Sum.inr (Sum.inl (198, 13)),
    Sum.inr (Sum.inl (229, 46)),
    Sum.inr (Sum.inl (198, 15)),
    Sum.inr (Sum.inl (93, 46)),
    Sum.inr (Sum.inl (65, 58)),
    Sum.inr (Sum.inl (93, 38)),
    Sum.inr (Sum.inl (65, 54)),
    Sum.inr (Sum.inl (49, 52)),
    Sum.inr (Sum.inl (136, 52)),
    Sum.inr (Sum.inl (49, 56)),
    Sum.inr (Sum.inl (136, 38)),
    Sum.inr (Sum.inl (95, 53)),
    Sum.inr (Sum.inl (189, 58)),
    Sum.inr (Sum.inl (95, 57)),
    Sum.inr (Sum.inl (189, 56)),
    Sum.inr (Sum.inl (198, 28)),
    Sum.inr (Sum.inl (229, 13)),
    Sum.inr (Sum.inl (198, 30)),
    Sum.inr (Sum.inl (229, 14)),
    Sum.inr (Sum.inl (189, 41)),
    Sum.inr (Sum.inl (95, 7)),
    Sum.inr (Sum.inl (189, 43)),
    Sum.inr (Sum.inl (95, 11)),
    Sum.inr (Sum.inl (229, 53)),
    Sum.inr (Sum.inl (198, 37)),
    Sum.inr (Sum.inl (229, 54)),
    Sum.inr (Sum.inl (198, 39)),
    Sum.inr (Sum.inl (65, 39)),
    Sum.inr (Sum.inl (93, 7)),
    Sum.inr (Sum.inl (65, 43)),
    Sum.inr (Sum.inl (93, 15)),
    Sum.inr (Sum.inl (136, 29)),
    Sum.inr (Sum.inl (49, 23)),
    Sum.inr (Sum.inl (136, 15)),
    Sum.inr (Sum.inl (49, 27)),
    Sum.inr (Sum.inl (95, 37)),
    Sum.inr (Sum.inl (189, 54)),
    Sum.inr (Sum.inl (95, 41)),
    Sum.inr (Sum.inl (189, 52)),
    Sum.inr (Sum.inl (198, 52)),
    Sum.inr (Sum.inl (229, 21)),
    Sum.inr (Sum.inl (198, 54)),
    Sum.inr (Sum.inl (229, 22)),
    Sum.inr (Sum.inl (93, 21)),
    Sum.inr (Sum.inl (65, 56)),
    Sum.inr (Sum.inl (93, 29)),
    Sum.inr (Sum.inl (65, 52)),
    Sum.inr (Sum.inl (49, 54)),
    Sum.inr (Sum.inl (136, 21)),
    Sum.inr (Sum.inl (49, 58)),
    Sum.inr (Sum.inl (136, 7)),
    Sum.inr (Sum.inl (59, 10)),
    Sum.inr (Sum.inl (62, 10)),
    Sum.inr (Sum.inl (135, 1)),
    Sum.inr (Sum.inl (219, 4)),
    Sum.inr (Sum.inl (59, 11)),
    Sum.inr (Sum.inl (62, 26)),
    Sum.inr (Sum.inl (135, 58)),
    Sum.inr (Sum.inl (219, 38)),
    Sum.inr (Sum.inl (98, 2)),
    Sum.inr (Sum.inl (183, 8)),
    Sum.inr (Sum.inl (85, 63)),
    Sum.inr (Sum.inl (199, 48)),
    Sum.inr (Sum.inl (98, 57)),
    Sum.inr (Sum.inl (183, 42)),
    Sum.inr (Sum.inl (85, 46)),
    Sum.inr (Sum.inl (199, 52)),
    Sum.inr (Sum.inl (135, 3)),
    Sum.inr (Sum.inl (219, 12)),
    Sum.inr (Sum.inl (59, 6)),
    Sum.inr (Sum.inl (62, 6)),
    Sum.inr (Sum.inl (135, 56)),
    Sum.inr (Sum.inl (219, 46)),
    Sum.inr (Sum.inl (59, 7)),
    Sum.inr (Sum.inl (62, 22))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock051Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨13056 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock051InputMaskData : ℕ :=
  sixthHex% [
    "885155ef5157e0515287d153c15156a6d154a9d151ced1571e5152795150",
    "76515511d15457515130d1533fd15658d15074515513d1571cd1527bd153",
    "3dd1565ad15455d1513251528ed1c715d1c51ad1c08151c51bd1c08051c2",
    "8f51c71451c10bd1c49051c69f51c30451c69e51c30551c10a51c491d1c1",
    "2bd1c4b051c6bf51c32451c6be51c32551c12a51c4b1d1c2ae51c73551c5",
    "3a51c0a1d1c53b51c0a0d1c2afd1c734d1c518d1c08351c28c51c71751c2",
    "8d51c71651c51951c082d1c69d51c30651c10951c492d1c10851c493d1c6",
    "9cd1c307d1c6bd51c32651c12951c4b2d1c12851c4b3d1c6bcd1c327d1c5",
    "3851c0a3d1c2acd1c737d1c2add1c736d1c539d1c0a251c4791326ae1320",
    "ae1322799326801324579322579320809326b01324679322679320b09324",
    "4993269e93209e9322491322a31320749326749324a393205a93228d9324",
    "8d93265a13206a9322bd9324bd93266a1322939320441326441324931327",
    "f31325249323249321f393250a9327dd9321dd93230a13253a9327ed9321",
    "ed93233a1327c39325141323141321c31321299323fe9325fe9327291323",
    "d09321071327071325d01323e09321371327371325e01321191323ce1325",
    "ce13271993240015c00d15c60d15c20095c40215c00f95c60f95c20295c0",
    "8215c48f95c28f95c68295c08095c48d95c28d95c68015c40315c00e95c6",
    "0e95c20395c40195c00c95c60c95c20115c08195c48c95c28c95c68115c0",
    "8395c48e15c28e15c68315c02315c42e95c22e95c62395c02195c42c95c2",
    "2c95c62115c4a195c0ac95c6ac95c2a115c4a395c0ae15c6ae15c2a315c0",
    "2095c42d95c22d95c62015c02295c42f15c22f15c62215c4a295c0af15c6",
    "af15c2a215c4a015c0ad15c6ad15c2a095c71986d1c186d54186d39906d5",
    "e086d33806d7b806d16006d5f086d32806d7a806d17006d70906d1d106d5",
    "5106d38986d1c386d71b06d39b06d54306d33a06d5e206d16206d7ba86d3",
    "2a06d5f206d17206d7aa86d1d306d70b86d38b86d55386d63386d0eb06d4",
    "6b06d2b306d4ca06d21206d69206d04a86d"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock051InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock051InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock051OutputMaskData : ℕ :=
  sixthHex% [
    "1b02705be15075d42f44770f2f9a701e3950300c2f70ef0f5e75151e9635",
    "30a34a01006a6aed155b4e35757b4a35986a0c942f3d370f13027053e150",
    "494c2f09af0f279a701639506b77063c02791237063402790dab482b9e37",
    "05ab4852de376f306349051c67306330451c78ac2d2fd95201ec2d27d952",
    "5fe27979d70657e279009706487e371f0b48313e37170b482ae51c7d9063",
    "53a51c7590634c39526a0c2d443952134c2d2e006308351c26006371751c",
    "399c2d6ee95240dc2d66e9525b07060c72792247060472793ddb481bee37",
    "35db4862ae376bd51c3ca06312951c34a0630d09522b3c2d050952527c2d",
    "6f927949a70667927930e706780e372f7b48014e37277b483d0808013939",
    "7070083d0139040b28497a193833280402192342126e33231f7a12234b23",
    "6b01325730032679326b08036272122f03235e4a12627b232a3132160003",
    "6749322a38030d78083149394000080d7139347b28790a19084328347219",
    "1333285e42192f0b28133a195b70086741391608085b79397c3932400803",
    "3141327c3003453a12084b237902124533233d09320138037071323d0003",
    "040a12497b233832120403232343286e32191f7b28234a196b0008573139",
    "2678086b093987d9e6e492cd95dbfc87d0d7bbee83a9e5a8d8ac99bbe7b2",
    "c6e688d4eda3a5a492c6efb98b91ede8dac69993f78b98dca472cdb679e6",
    "c730d7a47bfce905a88a4e83fb07b2e90c99940da3f74688860fb9940492",
    "a83ac6ba31edcb78dca833f7e1a0dcf3abf782e2c6e1a9edacd7b9cf9c92",
    "bed5a3acde88d1dfb2b29499c3dda8d1d683ede8d7ffe3fc8eaacdede1e6",
    "b34bf7d000dca149edb342c68f7c929d77b9ec3e888f75a3f27499e07fb2",
    "913683f27da8bf03fcdc48d7ad01e6bf0acd927bfcf136838c3e889e33f7",
    "ab78dcb975a3c47da8a730d7bce3fcaeee83d3e688b0abf7f4a0dc97eda3",
    "eae5a8f8e8d7cd01e6df0c99a20492c149ed8542c6e60fb99b07b2890acd",
    "92d9e6f194998c9c929e91edabdac6b9d7b9c4dfb2a792cd80d3fc92de83",
    "efd6888c9bf7c890dcabdda3d6d5a8c4d8d7"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock051OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock051OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock051InputNumeratorData : ℕ :=
  sixthHex% [
    "7e18617df7e17e18617df7e17df7e185f7df85f7df86185f7df7e185f7df",
    "86185f7e186185f7df86185f86185f7e186185f7df86185f7e18617df7e1",
    "86185f7e186185f7df86185f7df7e185f7df86185f7e186185f7df86185f",
    "86185f7e186185f7df86185f7e18617df7e186185f7e186185f7df7df7e1",
    "7df7e17e186186185f85f7df85f7df7df7e186185f85f7df85f7df7df7e1",
    "7e186186185f86185f85f7df85f7df86185f86185f7e186186185f7e1861",
    "7e18617df7e17df7e185f7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock051InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock051InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock051OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e186186185f7e186186185f7df7e17e18618617e17e17df85f8618617e1",
    "7e17df7df85f8617e17e17df7e17df7df85f8617e17e17df7df85f85f861",
    "7e17df7df85f7e17df7df85f8617e17e17df7df85f85f8617e17df7df85f",
    "8617e17e17df85f8618617e17e17df7df85f8617e17e17df7e17df8617e1",
    "7df85f7e17df7df85f7e17df85f8617df85f7df85f7e17df85f8617df85f",
    "85f8617df85f8617e185f8617e17df7df85f7df85f85f8617df85f85f861",
    "85f8618617e18617e17e17df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock051OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock051OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block051_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock051Input a) =
      generatedSixthXiShortBlock051InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock051Output a) =
      generatedSixthXiShortBlock051OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock051Input a) =
      generatedSixthXiShortBlock051InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock051Output a) =
      generatedSixthXiShortBlock051OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block051_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock051InputMask a) =
      generatedSixthXiShortBlock051OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock051InputMask a)) *
      generatedSixthXiShortBlock051InputNumerator a =
        generatedSixthXiShortBlock051OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block051_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock051Input a
    let y := generatedSixthXiShortBlock051Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block051_cache a
  have hs := generatedSixth_xi_short_block051_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block051_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock051Input a
    let y := generatedSixthXiShortBlock051Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block051_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block051_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock051Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block051_certificate a).1
    (generatedSixth_xi_short_block051_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
