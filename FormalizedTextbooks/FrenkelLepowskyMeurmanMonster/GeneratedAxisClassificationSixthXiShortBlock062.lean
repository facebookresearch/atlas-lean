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
def generatedSixthXiShortBlock062Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (196, 39)),
    Sum.inr (Sum.inl (144, 5)),
    Sum.inr (Sum.inl (167, 21)),
    Sum.inr (Sum.inl (195, 13)),
    Sum.inr (Sum.inl (167, 23)),
    Sum.inr (Sum.inl (196, 8)),
    Sum.inr (Sum.inl (144, 7)),
    Sum.inr (Sum.inl (195, 37)),
    Sum.inr (Sum.inl (12, 23)),
    Sum.inr (Sum.inl (12, 39)),
    Sum.inr (Sum.inl (32, 25)),
    Sum.inr (Sum.inl (12, 7)),
    Sum.inr (Sum.inl (167, 53)),
    Sum.inr (Sum.inl (144, 39)),
    Sum.inr (Sum.inl (195, 5)),
    Sum.inr (Sum.inl (196, 25)),
    Sum.inr (Sum.inl (88, 37)),
    Sum.inr (Sum.inl (87, 58)),
    Sum.inr (Sum.inl (81, 13)),
    Sum.inr (Sum.inl (83, 36)),
    Sum.inr (Sum.inl (23, 43)),
    Sum.inr (Sum.inl (3, 9)),
    Sum.inr (Sum.inl (23, 35)),
    Sum.inr (Sum.inl (23, 47)),
    Sum.inr (Sum.inl (88, 52)),
    Sum.inr (Sum.inl (81, 18)),
    Sum.inr (Sum.inl (83, 54)),
    Sum.inr (Sum.inl (87, 37)),
    Sum.inr (Sum.inl (83, 38)),
    Sum.inr (Sum.inl (88, 10)),
    Sum.inr (Sum.inl (81, 54)),
    Sum.inr (Sum.inl (87, 27)),
    Sum.inr (Sum.inl (3, 41)),
    Sum.inr (Sum.inl (3, 25)),
    Sum.inr (Sum.inl (23, 39)),
    Sum.inr (Sum.inl (3, 57)),
    Sum.inr (Sum.inl (83, 52)),
    Sum.inr (Sum.inl (81, 41)),
    Sum.inr (Sum.inl (87, 4)),
    Sum.inr (Sum.inl (88, 27)),
    Sum.inr (Sum.inr (365, 13)),
    Sum.inr (Sum.inr (300, 11)),
    Sum.inr (Sum.inr (492, 2)),
    Sum.inr (Sum.inr (422, 20)),
    Sum.inr (Sum.inr (115, 18)),
    Sum.inr (Sum.inr (120, 5)),
    Sum.inr (Sum.inr (115, 7)),
    Sum.inr (Sum.inr (115, 6)),
    Sum.inr (Sum.inr (365, 23)),
    Sum.inr (Sum.inr (492, 9)),
    Sum.inr (Sum.inr (422, 12)),
    Sum.inr (Sum.inr (300, 1)),
    Sum.inr (Sum.inr (422, 10)),
    Sum.inr (Sum.inr (365, 0)),
    Sum.inr (Sum.inr (492, 14)),
    Sum.inr (Sum.inr (300, 22)),
    Sum.inr (Sum.inr (120, 16)),
    Sum.inr (Sum.inr (120, 17)),
    Sum.inr (Sum.inr (115, 4)),
    Sum.inr (Sum.inr (120, 19)),
    Sum.inr (Sum.inr (422, 3)),
    Sum.inr (Sum.inr (492, 21)),
    Sum.inr (Sum.inr (300, 15)),
    Sum.inr (Sum.inr (365, 8)),
    Sum.inr (Sum.inr (428, 23)),
    Sum.inr (Sum.inr (493, 1)),
    Sum.inr (Sum.inr (301, 9)),
    Sum.inr (Sum.inr (359, 12)),
    Sum.inr (Sum.inr (178, 18)),
    Sum.inr (Sum.inr (185, 5)),
    Sum.inr (Sum.inr (178, 7)),
    Sum.inr (Sum.inr (178, 6)),
    Sum.inr (Sum.inr (428, 13)),
    Sum.inr (Sum.inr (301, 2)),
    Sum.inr (Sum.inr (359, 20)),
    Sum.inr (Sum.inr (493, 11)),
    Sum.inr (Sum.inr (359, 3)),
    Sum.inr (Sum.inr (428, 8)),
    Sum.inr (Sum.inr (301, 21)),
    Sum.inr (Sum.inr (493, 15)),
    Sum.inr (Sum.inr (185, 16)),
    Sum.inr (Sum.inr (185, 17)),
    Sum.inr (Sum.inr (178, 4)),
    Sum.inr (Sum.inr (185, 19)),
    Sum.inr (Sum.inr (359, 10)),
    Sum.inr (Sum.inr (301, 14)),
    Sum.inr (Sum.inr (493, 22)),
    Sum.inr (Sum.inr (428, 0)),
    Sum.inr (Sum.inr (494, 0)),
    Sum.inr (Sum.inr (431, 22)),
    Sum.inr (Sum.inr (367, 14)),
    Sum.inr (Sum.inr (293, 10)),
    Sum.inr (Sum.inr (240, 18)),
    Sum.inr (Sum.inr (251, 5)),
    Sum.inr (Sum.inr (240, 7)),
    Sum.inr (Sum.inr (240, 6)),
    Sum.inr (Sum.inr (494, 8)),
    Sum.inr (Sum.inr (367, 21)),
    Sum.inr (Sum.inr (293, 3)),
    Sum.inr (Sum.inr (431, 15)),
    Sum.inr (Sum.inr (293, 20)),
    Sum.inr (Sum.inr (494, 13)),
    Sum.inr (Sum.inr (367, 2)),
    Sum.inr (Sum.inr (431, 11)),
    Sum.inr (Sum.inr (251, 16)),
    Sum.inr (Sum.inr (251, 17)),
    Sum.inr (Sum.inr (240, 4)),
    Sum.inr (Sum.inr (251, 19)),
    Sum.inr (Sum.inr (293, 12)),
    Sum.inr (Sum.inr (367, 9)),
    Sum.inr (Sum.inr (431, 1)),
    Sum.inr (Sum.inr (494, 23)),
    Sum.inr (Sum.inr (292, 8)),
    Sum.inr (Sum.inr (357, 15)),
    Sum.inr (Sum.inr (421, 21)),
    Sum.inr (Sum.inr (495, 3)),
    Sum.inr (Sum.inr (58, 18)),
    Sum.inr (Sum.inr (49, 5)),
    Sum.inr (Sum.inr (58, 7)),
    Sum.inr (Sum.inr (58, 6)),
    Sum.inr (Sum.inr (292, 0)),
    Sum.inr (Sum.inr (421, 14)),
    Sum.inr (Sum.inr (495, 10)),
    Sum.inr (Sum.inr (357, 22)),
    Sum.inr (Sum.inr (495, 12)),
    Sum.inr (Sum.inr (292, 23)),
    Sum.inr (Sum.inr (421, 9)),
    Sum.inr (Sum.inr (357, 1)),
    Sum.inr (Sum.inr (49, 16)),
    Sum.inr (Sum.inr (49, 17)),
    Sum.inr (Sum.inr (58, 4)),
    Sum.inr (Sum.inr (49, 19)),
    Sum.inr (Sum.inr (495, 20)),
    Sum.inr (Sum.inr (421, 2)),
    Sum.inr (Sum.inr (357, 11)),
    Sum.inr (Sum.inr (292, 13)),
    Sum.inr (Sum.inl (88, 41)),
    Sum.inr (Sum.inl (87, 54)),
    Sum.inr (Sum.inl (81, 14)),
    Sum.inr (Sum.inl (83, 40)),
    Sum.inr (Sum.inl (23, 37)),
    Sum.inr (Sum.inl (3, 59)),
    Sum.inr (Sum.inl (23, 45)),
    Sum.inr (Sum.inl (23, 33)),
    Sum.inr (Sum.inl (88, 56)),
    Sum.inr (Sum.inl (81, 17)),
    Sum.inr (Sum.inl (83, 58)),
    Sum.inr (Sum.inl (87, 41)),
    Sum.inr (Sum.inl (83, 42)),
    Sum.inr (Sum.inl (88, 6)),
    Sum.inr (Sum.inl (81, 53)),
    Sum.inr (Sum.inl (87, 23)),
    Sum.inr (Sum.inl (3, 27)),
    Sum.inr (Sum.inl (3, 43)),
    Sum.inr (Sum.inl (23, 41)),
    Sum.inr (Sum.inl (3, 11)),
    Sum.inr (Sum.inl (83, 56)),
    Sum.inr (Sum.inl (81, 42)),
    Sum.inr (Sum.inl (87, 8)),
    Sum.inr (Sum.inl (88, 23)),
    Sum.inr (Sum.inl (196, 58)),
    Sum.inr (Sum.inl (195, 46)),
    Sum.inr (Sum.inl (144, 41)),
    Sum.inr (Sum.inl (167, 59)),
    Sum.inr (Sum.inl (32, 27)),
    Sum.inr (Sum.inl (12, 5)),
    Sum.inr (Sum.inl (32, 19)),
    Sum.inr (Sum.inl (32, 31)),
    Sum.inr (Sum.inl (196, 43)),
    Sum.inr (Sum.inl (144, 9)),
    Sum.inr (Sum.inl (167, 25)),
    Sum.inr (Sum.inl (195, 14)),
    Sum.inr (Sum.inl (167, 27)),
    Sum.inr (Sum.inl (196, 4)),
    Sum.inr (Sum.inl (144, 11)),
    Sum.inr (Sum.inl (195, 38)),
    Sum.inr (Sum.inl (12, 37)),
    Sum.inr (Sum.inl (12, 21)),
    Sum.inr (Sum.inl (32, 23)),
    Sum.inr (Sum.inl (12, 53)),
    Sum.inr (Sum.inl (167, 57)),
    Sum.inr (Sum.inl (144, 43)),
    Sum.inr (Sum.inl (195, 6)),
    Sum.inr (Sum.inl (196, 21)),
    Sum.inr (Sum.inl (210, 57)),
    Sum.inr (Sum.inl (204, 22)),
    Sum.inr (Sum.inl (147, 54)),
    Sum.inr (Sum.inl (170, 36)),
    Sum.inr (Sum.inl (35, 52)),
    Sum.inr (Sum.inl (15, 62)),
    Sum.inr (Sum.inl (35, 60)),
    Sum.inr (Sum.inl (35, 48)),
    Sum.inr (Sum.inl (210, 22)),
    Sum.inr (Sum.inl (147, 36)),
    Sum.inr (Sum.inl (170, 52)),
    Sum.inr (Sum.inl (204, 52)),
    Sum.inr (Sum.inl (170, 54)),
    Sum.inr (Sum.inl (210, 2)),
    Sum.inr (Sum.inl (147, 38)),
    Sum.inr (Sum.inl (204, 43)),
    Sum.inr (Sum.inl (15, 30)),
    Sum.inr (Sum.inl (15, 46)),
    Sum.inr (Sum.inl (35, 56)),
    Sum.inr (Sum.inl (15, 14)),
    Sum.inr (Sum.inl (170, 38)),
    Sum.inr (Sum.inl (147, 52)),
    Sum.inr (Sum.inl (204, 9)),
    Sum.inr (Sum.inl (210, 45)),
    Sum.inr (Sum.inl (133, 59)),
    Sum.inr (Sum.inl (132, 36)),
    Sum.inr (Sum.inl (126, 4)),
    Sum.inr (Sum.inl (128, 25)),
    Sum.inr (Sum.inl (26, 4)),
    Sum.inr (Sum.inl (6, 50)),
    Sum.inr (Sum.inl (26, 12)),
    Sum.inr (Sum.inl (26, 0)),
    Sum.inr (Sum.inl (133, 20)),
    Sum.inr (Sum.inl (126, 37)),
    Sum.inr (Sum.inl (128, 9)),
    Sum.inr (Sum.inl (132, 5)),
    Sum.inr (Sum.inl (128, 17)),
    Sum.inr (Sum.inl (133, 42)),
    Sum.inr (Sum.inl (126, 5)),
    Sum.inr (Sum.inl (132, 59)),
    Sum.inr (Sum.inl (6, 18)),
    Sum.inr (Sum.inl (6, 34)),
    Sum.inr (Sum.inl (26, 8)),
    Sum.inr (Sum.inl (6, 2)),
    Sum.inr (Sum.inl (128, 1)),
    Sum.inr (Sum.inl (126, 36)),
    Sum.inr (Sum.inl (132, 26)),
    Sum.inr (Sum.inl (133, 5)),
    Sum.inr (Sum.inl (215, 30)),
    Sum.inr (Sum.inl (209, 46)),
    Sum.inr (Sum.inl (152, 19)),
    Sum.inr (Sum.inl (175, 31)),
    Sum.inr (Sum.inl (40, 13)),
    Sum.inr (Sum.inl (20, 3)),
    Sum.inr (Sum.inl (40, 7)),
    Sum.inr (Sum.inl (40, 5)),
    Sum.inr (Sum.inl (215, 15)),
    Sum.inr (Sum.inl (152, 3)),
    Sum.inr (Sum.inl (175, 15)),
    Sum.inr (Sum.inl (209, 15)),
    Sum.inr (Sum.inl (175, 13)),
    Sum.inr (Sum.inl (215, 31)),
    Sum.inr (Sum.inl (152, 23)),
    Sum.inr (Sum.inl (209, 14)),
    Sum.inr (Sum.inl (20, 35)),
    Sum.inr (Sum.inl (20, 19)),
    Sum.inr (Sum.inl (40, 15)),
    Sum.inr (Sum.inl (20, 51)),
    Sum.inr (Sum.inl (175, 29)),
    Sum.inr (Sum.inl (152, 7)),
    Sum.inr (Sum.inl (209, 47)),
    Sum.inr (Sum.inl (215, 14))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock062Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨15872 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock062InputMaskData : ℕ :=
  sixthHex% [
    "bbc8b08dc0b096c8b0e0c0b08700b09900b0be00b0e000b09f68b0b568b0",
    "8a60b0e060b0a350b0a158b0a258b0e050b0ac48b0a440b0a848b0e040b0",
    "d0b0b0f0b0b0c0b0b0a0b0b0a3386f95386f8e306ff8306f9ff06f81f06f",
    "a6f06ff8f06f87906fad986f92986ff8906fbba86fb9a06fbaa86ff8a06f",
    "b4b06fbcb06fb0b86ff8b86fc8486fe8486fd8486fb8486fe2d86ed4d86e",
    "cfd06eb9d06ede106ec0106ee7106eb9106ec6706eec786ed3786eb9706e",
    "fa406ef8486efb406eb9486ef5506efd506ef1586eb9586e89a06ea9a06e",
    "99a06ef9a06edce86deae86df1e06d87e06de0206dfe206dd9206d87206d",
    "f8486dd2406ded406d87486dc4786dc6706dc5786d87706dcb606dc3606d",
    "cf686d87686db7906d97906da7906dc7906ddd086ceb086cf0006c86006c",
    "e1c06cffc06cd8c06c86c06cf9a86cd3a06ceca06c86a86cc5906cc7986c",
    "c4906c86986cca806cc2806cce886c86886cb6786c96786ca6786cc6786c",
    "e3806bd5806bce886bb8886bdf406bc1406be6406bb8406bc7286bed206b",
    "d2206bb8286bfb106bf9186bfa106bb8186bf4086bfc086bf0006bb8006b",
    "88f86ba8f86b98f86bf8f86be2606ad4606acf686ab9686adea06ac0a06a",
    "e7a06ab9a06ac6c86aecc06ad3c06ab9c86afaf86af8f06afbf86ab9f06a",
    "f5e86afde86af1e06ab9e06a89106aa9106a99106af9106adc5069ea5069",
    "f15869875869e09069fe9069d99069879069f8f069d2f869edf86987f069",
    "c4c069c6c869c5c06987c869cbd869c3d869cfd06987d069b72069972069",
    "a72069c720699db068abb068b0b868c6b868a17068bf7068987068c67068",
    "b91068931868ac1868c61068852868872068842868c620688a3868823868",
    "8e3068c63068f6c868d6c868e6c86886c868d54067e34067f848678e4867",
    "e98067f78067d080678e8067f1e067dbe867e4e8678ee067cdd867cfd067",
    "ccd8678ed067c2c067cac067c6c8678ec867be30679e3067ae3067ce3067",
    "d4a066e2a066f9a8668fa866e86066f66066d160668f6066f00066da0866",
    "e508668f0066cc3066ce3866cd30668f3866"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock062InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock062InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock062OutputMaskData : ℕ :=
  sixthHex% [
    "3afaa16cfb901020b033218a5df6e476f6ef64f6e43af6e40f13903380b0",
    "7a12a133818a42639003f18a24b8b0102aa132feef4bb6ef03fee40fb6ef",
    "03598a0710b021839050caa139534f1e127e62c95e3088645e5f0a755f01",
    "675f0a395f0a7dfa7e30295e08fb4f302864308a7e71186427115e13834f",
    "401701481f0100570a7d5f0171b06475f95e536a7e22234f6d806e4ac15f",
    "361a7f645b450a8c2b218c20338c2b6d8c2b29295f64fa7f5c286e64fb45",
    "15195f548b4502827f36106e14c4201ccc2054842b298c20542345506a7f",
    "76f95f07b06e6ac95c4d886d31534d6312770dc51926c51234c5196ac519",
    "5f206d12f34d2a215c12f27763106d228277748b4d40195c138d121b8512",
    "53cd192ec512536a7757234d71b06d00f95c4b1a766c5b4710806742c15d",
    "2c16330716381516334b16337ef3473320670bf27633215d33834772115d",
    "241867108a76325e383a5638721e330f163803f95d07b067212347506a76",
    "a3ac9484eda5f83685aa77bfb5e0d19ee0da8ce0d1d2e0d1e705a5aad685",
    "920494aad7bfaa75a5ebe7bfbdee85897c94dae8dad2e0da9aa8d1e7a0da",
    "9a0fbf9e4685b8d5a5c99c94827fbea53e8fd9e5af8ba4959433fbbf33f0",
    "ad33fbf333fbc6d68f8b05afb3d7be8b0495fae68fbb7495ed7dafd9efbe",
    "fb3bf0f333f0bb7bfbc673f0ca9c95ced5afe8468f990fbe85368ca277bd",
    "deac9d8ceda7937ac9b87ac2aa7ac9f47ac9b0dfbdfd0c9dc5de8cfd0da7",
    "8cefbdcd7da79b749dafe68cfc72c2f47ac2bc32c9c13ac2cdd5a7c99c9d",
    "ef0fbd9e468cd1e5adf6a49c8a7fbcd83e86c7a9e8eca9e3fea9e8a0a9e8",
    "e40c9ca9dfbc910dada9de86a97c9ce8ee86bee7bc8a75ada8a1e3a0a9e3",
    "e8e1e895e9e3e84686ec0fbcca9c9cbbd5ad031a76245b475880670ac15d",
    "1556333e56382c563372563336f3477b206743f2767b215d7b83473a115d",
    "6c1867588a760b1e380316384b5e333656384bf95d4fb067692347186a76",
    "22c95c05886d79534d2b12773485191f85120d851953851917206d5af34d",
    "62215c5af2772b106d6a82773c8b4d08195c"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock062OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock062OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock062InputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock062InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock062InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock062OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df8616df8e38617df8618617e185f85f85f85f7e196175d8617df85f85f",
    "7df7df7e185f85f85f96175d85f7e17df8617df7df7e17e17e185f6df8e3",
    "8617df7e17e18618617e185f85f85f96175d7e185f7df8617df7df85f85f",
    "8617e195f75d86185f85f7df85f7df7df7e186185f95f75d85f8617df7e1",
    "85f7df7df85f7df85f6e18e386185f7e18617e18617df7e17df7e16e18e3",
    "85f86186185f7e18617df85f85f85f96175d7e185f7df8617df7df85f85f",
    "7e185f6df8e38617df7e17e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock062OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock062OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block062_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock062Input a) =
      generatedSixthXiShortBlock062InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock062Output a) =
      generatedSixthXiShortBlock062OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock062Input a) =
      generatedSixthXiShortBlock062InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock062Output a) =
      generatedSixthXiShortBlock062OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block062_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock062InputMask a) =
      generatedSixthXiShortBlock062OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock062InputMask a)) *
      generatedSixthXiShortBlock062InputNumerator a =
        generatedSixthXiShortBlock062OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block062_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock062Input a
    let y := generatedSixthXiShortBlock062Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block062_cache a
  have hs := generatedSixth_xi_short_block062_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block062_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock062Input a
    let y := generatedSixthXiShortBlock062Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block062_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block062_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock062Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block062_certificate a).1
    (generatedSixth_xi_short_block062_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
