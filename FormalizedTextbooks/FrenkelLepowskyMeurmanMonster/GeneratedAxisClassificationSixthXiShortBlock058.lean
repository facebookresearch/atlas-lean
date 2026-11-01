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
def generatedSixthXiShortBlock058Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (134, 52)),
    Sum.inr (Sum.inl (191, 46)),
    Sum.inr (Sum.inl (100, 25)),
    Sum.inr (Sum.inl (44, 49)),
    Sum.inr (Sum.inl (162, 46)),
    Sum.inr (Sum.inl (77, 53)),
    Sum.inr (Sum.inl (223, 54)),
    Sum.inr (Sum.inl (86, 39)),
    Sum.inr (Sum.inl (77, 21)),
    Sum.inr (Sum.inl (162, 49)),
    Sum.inr (Sum.inl (86, 46)),
    Sum.inr (Sum.inl (223, 11)),
    Sum.inr (Sum.inl (191, 38)),
    Sum.inr (Sum.inl (134, 43)),
    Sum.inr (Sum.inl (44, 56)),
    Sum.inr (Sum.inl (100, 19)),
    Sum.inr (Sum.inl (77, 31)),
    Sum.inr (Sum.inl (162, 33)),
    Sum.inr (Sum.inl (86, 62)),
    Sum.inr (Sum.inl (223, 3)),
    Sum.inr (Sum.inl (191, 55)),
    Sum.inr (Sum.inl (134, 33)),
    Sum.inr (Sum.inl (44, 62)),
    Sum.inr (Sum.inl (100, 3)),
    Sum.inr (Sum.inl (162, 52)),
    Sum.inr (Sum.inl (77, 58)),
    Sum.inr (Sum.inl (223, 26)),
    Sum.inr (Sum.inl (86, 49)),
    Sum.inr (Sum.inl (134, 46)),
    Sum.inr (Sum.inl (191, 27)),
    Sum.inr (Sum.inl (100, 22)),
    Sum.inr (Sum.inl (44, 23)),
    Sum.inr (Sum.inl (162, 36)),
    Sum.inr (Sum.inl (77, 48)),
    Sum.inr (Sum.inl (223, 18)),
    Sum.inr (Sum.inl (86, 33)),
    Sum.inr (Sum.inl (134, 36)),
    Sum.inr (Sum.inl (191, 10)),
    Sum.inr (Sum.inl (100, 6)),
    Sum.inr (Sum.inl (44, 17)),
    Sum.inr (Sum.inl (120, 47)),
    Sum.inr (Sum.inl (76, 31)),
    Sum.inr (Sum.inl (120, 35)),
    Sum.inr (Sum.inl (76, 23)),
    Sum.inr (Sum.inl (182, 63)),
    Sum.inr (Sum.inl (200, 63)),
    Sum.inr (Sum.inl (182, 45)),
    Sum.inr (Sum.inl (200, 51)),
    Sum.inr (Sum.inl (76, 11)),
    Sum.inr (Sum.inl (120, 15)),
    Sum.inr (Sum.inl (76, 3)),
    Sum.inr (Sum.inl (120, 3)),
    Sum.inr (Sum.inl (200, 29)),
    Sum.inr (Sum.inl (182, 23)),
    Sum.inr (Sum.inl (200, 17)),
    Sum.inr (Sum.inl (182, 5)),
    Sum.inr (Sum.inl (101, 40)),
    Sum.inr (Sum.inl (82, 63)),
    Sum.inr (Sum.inl (101, 42)),
    Sum.inr (Sum.inl (82, 51)),
    Sum.inr (Sum.inl (45, 31)),
    Sum.inr (Sum.inl (224, 31)),
    Sum.inr (Sum.inl (45, 28)),
    Sum.inr (Sum.inl (224, 29)),
    Sum.inr (Sum.inl (82, 45)),
    Sum.inr (Sum.inl (101, 7)),
    Sum.inr (Sum.inl (82, 33)),
    Sum.inr (Sum.inl (101, 5)),
    Sum.inr (Sum.inl (224, 22)),
    Sum.inr (Sum.inl (45, 15)),
    Sum.inr (Sum.inl (224, 20)),
    Sum.inr (Sum.inl (45, 12)),
    Sum.inr (Sum.inl (101, 12)),
    Sum.inr (Sum.inl (82, 32)),
    Sum.inr (Sum.inl (101, 14)),
    Sum.inr (Sum.inl (82, 44)),
    Sum.inr (Sum.inl (45, 55)),
    Sum.inr (Sum.inl (224, 47)),
    Sum.inr (Sum.inl (45, 52)),
    Sum.inr (Sum.inl (224, 45)),
    Sum.inr (Sum.inl (82, 50)),
    Sum.inr (Sum.inl (101, 35)),
    Sum.inr (Sum.inl (82, 62)),
    Sum.inr (Sum.inl (101, 33)),
    Sum.inr (Sum.inl (224, 38)),
    Sum.inr (Sum.inl (45, 39)),
    Sum.inr (Sum.inl (224, 36)),
    Sum.inr (Sum.inl (45, 36)),
    Sum.inr (Sum.inl (120, 18)),
    Sum.inr (Sum.inl (76, 34)),
    Sum.inr (Sum.inl (120, 30)),
    Sum.inr (Sum.inl (76, 42)),
    Sum.inr (Sum.inl (182, 62)),
    Sum.inr (Sum.inl (200, 62)),
    Sum.inr (Sum.inl (182, 44)),
    Sum.inr (Sum.inl (200, 50)),
    Sum.inr (Sum.inl (76, 54)),
    Sum.inr (Sum.inl (120, 50)),
    Sum.inr (Sum.inl (76, 62)),
    Sum.inr (Sum.inl (120, 62)),
    Sum.inr (Sum.inl (200, 28)),
    Sum.inr (Sum.inl (182, 22)),
    Sum.inr (Sum.inl (200, 16)),
    Sum.inr (Sum.inl (182, 4)),
    Sum.inr (Sum.inl (72, 26)),
    Sum.inr (Sum.inl (72, 53)),
    Sum.inr (Sum.inl (124, 38)),
    Sum.inr (Sum.inl (124, 27)),
    Sum.inr (Sum.inl (139, 52)),
    Sum.inr (Sum.inl (139, 53)),
    Sum.inr (Sum.inl (55, 54)),
    Sum.inr (Sum.inl (55, 30)),
    Sum.inr (Sum.inl (78, 42)),
    Sum.inr (Sum.inl (78, 23)),
    Sum.inr (Sum.inl (155, 43)),
    Sum.inr (Sum.inl (155, 15)),
    Sum.inr (Sum.inl (177, 53)),
    Sum.inr (Sum.inl (177, 29)),
    Sum.inr (Sum.inl (225, 14)),
    Sum.inr (Sum.inl (225, 15)),
    Sum.inr (Sum.inl (124, 46)),
    Sum.inr (Sum.inl (124, 19)),
    Sum.inr (Sum.inl (72, 22)),
    Sum.inr (Sum.inl (72, 57)),
    Sum.inr (Sum.inl (55, 52)),
    Sum.inr (Sum.inl (55, 28)),
    Sum.inr (Sum.inl (139, 56)),
    Sum.inr (Sum.inl (139, 57)),
    Sum.inr (Sum.inl (155, 41)),
    Sum.inr (Sum.inl (155, 13)),
    Sum.inr (Sum.inl (78, 38)),
    Sum.inr (Sum.inl (78, 27)),
    Sum.inr (Sum.inl (225, 28)),
    Sum.inr (Sum.inl (225, 29)),
    Sum.inr (Sum.inl (177, 54)),
    Sum.inr (Sum.inl (177, 30)),
    Sum.inr (Sum.inl (78, 58)),
    Sum.inr (Sum.inl (78, 7)),
    Sum.inr (Sum.inl (155, 28)),
    Sum.inr (Sum.inl (155, 56)),
    Sum.inr (Sum.inl (177, 37)),
    Sum.inr (Sum.inl (177, 13)),
    Sum.inr (Sum.inl (225, 38)),
    Sum.inr (Sum.inl (225, 39)),
    Sum.inr (Sum.inl (72, 56)),
    Sum.inr (Sum.inl (72, 23)),
    Sum.inr (Sum.inl (124, 50)),
    Sum.inr (Sum.inl (124, 15)),
    Sum.inr (Sum.inl (139, 22)),
    Sum.inr (Sum.inl (139, 23)),
    Sum.inr (Sum.inl (55, 39)),
    Sum.inr (Sum.inl (55, 15)),
    Sum.inr (Sum.inl (155, 30)),
    Sum.inr (Sum.inl (155, 58)),
    Sum.inr (Sum.inl (78, 54)),
    Sum.inr (Sum.inl (78, 11)),
    Sum.inr (Sum.inl (225, 52)),
    Sum.inr (Sum.inl (225, 53)),
    Sum.inr (Sum.inl (177, 38)),
    Sum.inr (Sum.inl (177, 14)),
    Sum.inr (Sum.inl (124, 58)),
    Sum.inr (Sum.inl (124, 7)),
    Sum.inr (Sum.inl (72, 52)),
    Sum.inr (Sum.inl (72, 27)),
    Sum.inr (Sum.inl (55, 37)),
    Sum.inr (Sum.inl (55, 13)),
    Sum.inr (Sum.inl (139, 26)),
    Sum.inr (Sum.inl (139, 27)),
    Sum.inr (Sum.inl (190, 34)),
    Sum.inr (Sum.inl (197, 57)),
    Sum.inr (Sum.inl (190, 21)),
    Sum.inr (Sum.inl (197, 59)),
    Sum.inr (Sum.inl (123, 30)),
    Sum.inr (Sum.inl (110, 63)),
    Sum.inr (Sum.inl (123, 32)),
    Sum.inr (Sum.inl (110, 23)),
    Sum.inr (Sum.inl (67, 36)),
    Sum.inr (Sum.inl (47, 57)),
    Sum.inr (Sum.inl (67, 26)),
    Sum.inr (Sum.inl (47, 17)),
    Sum.inr (Sum.inl (80, 45)),
    Sum.inr (Sum.inl (226, 5)),
    Sum.inr (Sum.inl (80, 5)),
    Sum.inr (Sum.inl (226, 7)),
    Sum.inr (Sum.inl (67, 38)),
    Sum.inr (Sum.inl (47, 59)),
    Sum.inr (Sum.inl (67, 24)),
    Sum.inr (Sum.inl (47, 19)),
    Sum.inr (Sum.inl (80, 47)),
    Sum.inr (Sum.inl (226, 29)),
    Sum.inr (Sum.inl (80, 7)),
    Sum.inr (Sum.inl (226, 31)),
    Sum.inr (Sum.inl (190, 54)),
    Sum.inr (Sum.inl (197, 33)),
    Sum.inr (Sum.inl (190, 1)),
    Sum.inr (Sum.inl (197, 35)),
    Sum.inr (Sum.inl (123, 6)),
    Sum.inr (Sum.inl (110, 43)),
    Sum.inr (Sum.inl (123, 56)),
    Sum.inr (Sum.inl (110, 3)),
    Sum.inr (Sum.inl (123, 28)),
    Sum.inr (Sum.inl (110, 61)),
    Sum.inr (Sum.inl (123, 34)),
    Sum.inr (Sum.inl (110, 21)),
    Sum.inr (Sum.inl (190, 32)),
    Sum.inr (Sum.inl (197, 29)),
    Sum.inr (Sum.inl (190, 23)),
    Sum.inr (Sum.inl (197, 31)),
    Sum.inr (Sum.inl (80, 19)),
    Sum.inr (Sum.inl (226, 33)),
    Sum.inr (Sum.inl (80, 59)),
    Sum.inr (Sum.inl (226, 35)),
    Sum.inr (Sum.inl (67, 12)),
    Sum.inr (Sum.inl (47, 45)),
    Sum.inr (Sum.inl (67, 50)),
    Sum.inr (Sum.inl (47, 5)),
    Sum.inr (Sum.inl (80, 17)),
    Sum.inr (Sum.inl (226, 57)),
    Sum.inr (Sum.inl (80, 57)),
    Sum.inr (Sum.inl (226, 59)),
    Sum.inr (Sum.inl (67, 14)),
    Sum.inr (Sum.inl (47, 47)),
    Sum.inr (Sum.inl (67, 48)),
    Sum.inr (Sum.inl (47, 7)),
    Sum.inr (Sum.inl (123, 4)),
    Sum.inr (Sum.inl (110, 41)),
    Sum.inr (Sum.inl (123, 58)),
    Sum.inr (Sum.inl (110, 1)),
    Sum.inr (Sum.inl (190, 52)),
    Sum.inr (Sum.inl (197, 5)),
    Sum.inr (Sum.inl (190, 3)),
    Sum.inr (Sum.inl (197, 7)),
    Sum.inr (Sum.inl (51, 18)),
    Sum.inr (Sum.inl (51, 61)),
    Sum.inr (Sum.inl (109, 14)),
    Sum.inr (Sum.inl (109, 51)),
    Sum.inr (Sum.inl (79, 2)),
    Sum.inr (Sum.inl (79, 63)),
    Sum.inr (Sum.inl (181, 57)),
    Sum.inr (Sum.inl (181, 29)),
    Sum.inr (Sum.inl (137, 3)),
    Sum.inr (Sum.inl (137, 2)),
    Sum.inr (Sum.inl (68, 7)),
    Sum.inr (Sum.inl (68, 19)),
    Sum.inr (Sum.inl (159, 4)),
    Sum.inr (Sum.inl (159, 16)),
    Sum.inr (Sum.inl (227, 51)),
    Sum.inr (Sum.inl (227, 50)),
    Sum.inr (Sum.inl (109, 6)),
    Sum.inr (Sum.inl (109, 59)),
    Sum.inr (Sum.inl (51, 30)),
    Sum.inr (Sum.inl (51, 49)),
    Sum.inr (Sum.inl (181, 59)),
    Sum.inr (Sum.inl (181, 31)),
    Sum.inr (Sum.inl (79, 14)),
    Sum.inr (Sum.inl (79, 51))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock058Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨14848 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock058InputMaskData : ℕ :=
  sixthHex% [
    "19a6e87fd6e82326e8455ee82e36e8484ee814bee872cee81fc6e879b6e8",
    "2546e8433ee82856e84e2ee812dee874aee81666e8701ee82ceee84a9ee8",
    "21fee8478ee81b7ee87d06e83670081b00087b00085678084b0008667808",
    "0678082b08086b00084678082678080b08081678083b08085b0808767008",
    "5b70087608081608083b78082608080b78086b78084600080608082b7808",
    "4b78086600087b78085600083600081b70082d70080008086008084d7808",
    "5008087d78081d78083000087008085d78083d78081000080d7808200008",
    "4000086d70084078086d08080d08082070083d08081070087070085d0008",
    "1d08083070085070087d00086070084d00082d0008007808013e8b674e8b",
    "33be8b55c68b77ae8b11d68b45268b23568b779e8b11e68b45168b23668b",
    "01068b67768b33868b55fe8b0efe8b68868b3c768b5a068b78668b1e168b",
    "4ae68b2c9e8b78568b1e268b4ad68b2cae8b0ec68b68be8b3c4e8b5a3e8b",
    "773e8b11468b45b68b23c68b01a68b67d68b33268b555e8b01968b67e68b",
    "33168b556e8b77068b117e8b458e8b23fe8b78f68b1e868b4a768b2c0e8b",
    "0e668b681e8b3cee8b5a9e8b0e568b682e8b3cde8b5aae8b78ce8b1ebe8b",
    "4a4e8b2c368b45cee12c7ee1708ee11936e13c9ee15526e109d6e16066e1",
    "7e9ee11726e14bd6e12266e107c6e16e76e13286e15b3ee17f9ee11626e1",
    "4ad6e12366e106c6e16f76e13386e15a3ee144c6e12d76e17186e1183ee1",
    "3d96e1542ee108dee1616ee143aee12a16e176e6e11f56e13af6e15346e1",
    "0fb6e1660ee178f6e11146e14db6e1240ee101a6e1681ee134eee15d5ee1",
    "79f6e11046e14cb6e1250ee100a6e1691ee135eee15c5ee142a6e12b1ee1",
    "77eee11e5ee13bfee1524ee10ebee16706e102e00103000163000162e801",
    "53000152e80132e80133080173000172e80112e80113080122e801230801",
    "43080142e00143e00142080122080123e80112080113e80173e801720001",
    "32080133e80153e80152000163e80162000102000103e00101e001000801",
    "60080161e80150080151e80131e801300001"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock058InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock058InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock058OutputMaskData : ℕ :=
  sixthHex% [
    "36e397509397143dc8030dc82532ad3202ad76acf210dcf23e46e85836e8",
    "1c98b70ba8b72d97d23aa7d27e098d18798d2175c83645c872eb97149b97",
    "43e4f22594f2613aad760aad3e09320238037371323e000355e212189323",
    "69da1255eb2351ab281cda196d932851a2194b00087731390678084b0939",
    "61d3282ca2195deb2861da197b78084749393600087b71397f3132430003",
    "3249327f380314da1259ab2328e21214d3233392127ee3230faa12339b23",
    "2939321508036441322930032d70081141396008082d7939469b280bea19",
    "7aa3284692191d08082139395070081d013976e3283b92194adb2876ea19",
    "72aa123fdb234e921272a3236801325430032579326808034c61ee2a11ee",
    "66b7b17187b13d2bff2a1bff66bda000cda01e80d409b0d445168b23668b",
    "1e8ac578fac5345c9a236c9a5bf7b14cc7b10061ee6611ee5bfda03d8da0",
    "712bff661bff78568b1e268b5280d445b0d4091c9a1e2c9a528ac534fac5",
    "1e20d40910d445b68b23c68b1e2ac5785ac534fc9a23cc9a3d81ee5bf1ee",
    "1757b10067b14ccbff5bfbff175da0712da078f68b1e868b5220d44510d4",
    "09bc9a1e8c9a522ac5345ac52a17b13d27b17181ee17f1ee2a1da04c6da0",
    "00cbff17fbff2c0dc15deb9e1945c119e39e4ad18f4a77d00ed98f7f3fd0",
    "0f039e0fa5c14b0b9e3aedc1189fd069798f2dd7d02d718f1898be183ee1",
    "5c90be2d76e10f04f07ee2af3a4cf03aeaaf4ad6e13b30be7f9ee17f38be",
    "2c0aaf2cacf06802af19e4f024a8be240ee160a0be1146e13334f042d2af",
    "067cf006daaf76e6e10700be43aee14308be103aaf109cf05432af25d4f0",
    "617dc1109b9e5435c154939e07a18f0707d043a98f324fd042739e42d5c1",
    "067b9e779dc155efd024098f60a7d060018f069a1024e13b55a80a069321",
    "733b2a20000151493073321b77721024493b55000a777b2173932a51e801",
    "20a130739a1b64013b373a1046732164080a60e001429b2a33d21b60e930",
    "64a93b46d210379b2164a00a11080142332a337a1b11013021d32a72e801",
    "03a13021da1b25321007493b76000a253b21"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock058OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock058OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock058InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df86185f85f7df86185f86185f7e18617df85f85f8617e17df7df85f",
    "7e17df7df85f8617e17e17df7e17df7df85f8617e17e17df8617e17e17df",
    "85f8618617e17e17df8617e17df85f7e17df7df85f7e17df85f8617df85f",
    "7df85f7e17df85f8617df85f85f8617df85f8617e185f8617e18617df7e1",
    "86185f7e18617df7e185f7df7e18617df7e17df7e185f7df7e18617df7e1",
    "85f7df86185f7df7e185f7df85f8618617e17df85f85f8617df85f85f861",
    "7e17df7df85f8617e17e17df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock058InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock058InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock058OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f8617df85f7e17df8617e18617e185f86186185f7e186185f7df86185f",
    "7e18617df7e186185f7e186185f7df86185f7df7e185f7df86185f7e1861",
    "85f7df86185f85f7df86185f86185f7e18617df7e185f7df85f7df86185f",
    "86185f7e18617e18617df7e185f7df86185f86185f7e18617df7e185f7df",
    "85f7df86185f7e18617df7e17df7e185f7df7e18617df7e17df7e185f7df",
    "86185f7e18617e18617df7e186185f7e186185f7df86185f85f7df86185f",
    "7df7e185f7df85f7df86185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock058OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock058OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block058_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock058Input a) =
      generatedSixthXiShortBlock058InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock058Output a) =
      generatedSixthXiShortBlock058OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock058Input a) =
      generatedSixthXiShortBlock058InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock058Output a) =
      generatedSixthXiShortBlock058OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block058_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock058InputMask a) =
      generatedSixthXiShortBlock058OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock058InputMask a)) *
      generatedSixthXiShortBlock058InputNumerator a =
        generatedSixthXiShortBlock058OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block058_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock058Input a
    let y := generatedSixthXiShortBlock058Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block058_cache a
  have hs := generatedSixth_xi_short_block058_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block058_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock058Input a
    let y := generatedSixthXiShortBlock058Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block058_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block058_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock058Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block058_certificate a).1
    (generatedSixth_xi_short_block058_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
