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
def generatedSixthXiShortBlock096Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (210, 24)),
    Sum.inr (Sum.inl (204, 18)),
    Sum.inr (Sum.inl (147, 32)),
    Sum.inr (Sum.inl (170, 0)),
    Sum.inr (Sum.inl (35, 24)),
    Sum.inr (Sum.inl (15, 52)),
    Sum.inr (Sum.inl (35, 16)),
    Sum.inr (Sum.inl (35, 28)),
    Sum.inr (Sum.inl (210, 55)),
    Sum.inr (Sum.inl (147, 50)),
    Sum.inr (Sum.inl (170, 16)),
    Sum.inr (Sum.inl (204, 48)),
    Sum.inr (Sum.inl (170, 18)),
    Sum.inr (Sum.inl (210, 35)),
    Sum.inr (Sum.inl (147, 48)),
    Sum.inr (Sum.inl (204, 47)),
    Sum.inr (Sum.inl (15, 20)),
    Sum.inr (Sum.inl (15, 36)),
    Sum.inr (Sum.inl (35, 20)),
    Sum.inr (Sum.inl (15, 4)),
    Sum.inr (Sum.inl (170, 2)),
    Sum.inr (Sum.inl (147, 34)),
    Sum.inr (Sum.inl (204, 13)),
    Sum.inr (Sum.inl (210, 12)),
    Sum.inr (Sum.inl (196, 30)),
    Sum.inr (Sum.inl (195, 43)),
    Sum.inr (Sum.inl (144, 15)),
    Sum.inr (Sum.inl (167, 47)),
    Sum.inr (Sum.inl (32, 7)),
    Sum.inr (Sum.inl (12, 3)),
    Sum.inr (Sum.inl (32, 15)),
    Sum.inr (Sum.inl (32, 3)),
    Sum.inr (Sum.inl (196, 15)),
    Sum.inr (Sum.inl (144, 47)),
    Sum.inr (Sum.inl (167, 13)),
    Sum.inr (Sum.inl (195, 11)),
    Sum.inr (Sum.inl (167, 15)),
    Sum.inr (Sum.inl (196, 32)),
    Sum.inr (Sum.inl (144, 45)),
    Sum.inr (Sum.inl (195, 35)),
    Sum.inr (Sum.inl (12, 35)),
    Sum.inr (Sum.inl (12, 19)),
    Sum.inr (Sum.inl (32, 11)),
    Sum.inr (Sum.inl (12, 51)),
    Sum.inr (Sum.inl (167, 45)),
    Sum.inr (Sum.inl (144, 13)),
    Sum.inr (Sum.inl (195, 3)),
    Sum.inr (Sum.inl (196, 49)),
    Sum.inr (Sum.inl (88, 47)),
    Sum.inr (Sum.inl (87, 48)),
    Sum.inr (Sum.inl (81, 20)),
    Sum.inr (Sum.inl (83, 45)),
    Sum.inr (Sum.inl (23, 40)),
    Sum.inr (Sum.inl (3, 56)),
    Sum.inr (Sum.inl (23, 32)),
    Sum.inr (Sum.inl (23, 44)),
    Sum.inr (Sum.inl (88, 62)),
    Sum.inr (Sum.inl (81, 11)),
    Sum.inr (Sum.inl (83, 63)),
    Sum.inr (Sum.inl (87, 47)),
    Sum.inr (Sum.inl (83, 47)),
    Sum.inr (Sum.inl (88, 0)),
    Sum.inr (Sum.inl (81, 47)),
    Sum.inr (Sum.inl (87, 17)),
    Sum.inr (Sum.inl (3, 24)),
    Sum.inr (Sum.inl (3, 40)),
    Sum.inr (Sum.inl (23, 36)),
    Sum.inr (Sum.inl (3, 8)),
    Sum.inr (Sum.inl (83, 61)),
    Sum.inr (Sum.inl (81, 48)),
    Sum.inr (Sum.inl (87, 14)),
    Sum.inr (Sum.inl (88, 17)),
    Sum.inr (Sum.inr (187, 8)),
    Sum.inr (Sum.inr (250, 15)),
    Sum.inr (Sum.inr (58, 21)),
    Sum.inr (Sum.inr (112, 3)),
    Sum.inr (Sum.inr (421, 18)),
    Sum.inr (Sum.inr (430, 5)),
    Sum.inr (Sum.inr (421, 7)),
    Sum.inr (Sum.inr (421, 6)),
    Sum.inr (Sum.inr (187, 0)),
    Sum.inr (Sum.inr (58, 14)),
    Sum.inr (Sum.inr (112, 10)),
    Sum.inr (Sum.inr (250, 22)),
    Sum.inr (Sum.inr (112, 12)),
    Sum.inr (Sum.inr (187, 23)),
    Sum.inr (Sum.inr (58, 9)),
    Sum.inr (Sum.inr (250, 1)),
    Sum.inr (Sum.inr (430, 16)),
    Sum.inr (Sum.inr (430, 17)),
    Sum.inr (Sum.inr (421, 4)),
    Sum.inr (Sum.inr (430, 19)),
    Sum.inr (Sum.inr (112, 20)),
    Sum.inr (Sum.inr (58, 2)),
    Sum.inr (Sum.inr (250, 11)),
    Sum.inr (Sum.inr (187, 13)),
    Sum.inr (Sum.inr (113, 0)),
    Sum.inr (Sum.inr (48, 22)),
    Sum.inr (Sum.inr (240, 14)),
    Sum.inr (Sum.inr (186, 10)),
    Sum.inr (Sum.inr (367, 18)),
    Sum.inr (Sum.inr (356, 5)),
    Sum.inr (Sum.inr (367, 7)),
    Sum.inr (Sum.inr (367, 6)),
    Sum.inr (Sum.inr (113, 8)),
    Sum.inr (Sum.inr (240, 21)),
    Sum.inr (Sum.inr (186, 3)),
    Sum.inr (Sum.inr (48, 15)),
    Sum.inr (Sum.inr (186, 20)),
    Sum.inr (Sum.inr (113, 13)),
    Sum.inr (Sum.inr (240, 2)),
    Sum.inr (Sum.inr (48, 11)),
    Sum.inr (Sum.inr (356, 16)),
    Sum.inr (Sum.inr (356, 17)),
    Sum.inr (Sum.inr (367, 4)),
    Sum.inr (Sum.inr (356, 19)),
    Sum.inr (Sum.inr (186, 12)),
    Sum.inr (Sum.inr (240, 9)),
    Sum.inr (Sum.inr (48, 1)),
    Sum.inr (Sum.inr (113, 23)),
    Sum.inr (Sum.inr (51, 23)),
    Sum.inr (Sum.inr (114, 1)),
    Sum.inr (Sum.inr (178, 9)),
    Sum.inr (Sum.inr (248, 12)),
    Sum.inr (Sum.inr (301, 18)),
    Sum.inr (Sum.inr (294, 5)),
    Sum.inr (Sum.inr (301, 7)),
    Sum.inr (Sum.inr (301, 6)),
    Sum.inr (Sum.inr (51, 13)),
    Sum.inr (Sum.inr (178, 2)),
    Sum.inr (Sum.inr (248, 20)),
    Sum.inr (Sum.inr (114, 11)),
    Sum.inr (Sum.inr (248, 3)),
    Sum.inr (Sum.inr (51, 8)),
    Sum.inr (Sum.inr (178, 21)),
    Sum.inr (Sum.inr (114, 15)),
    Sum.inr (Sum.inr (294, 16)),
    Sum.inr (Sum.inr (294, 17)),
    Sum.inr (Sum.inr (301, 4)),
    Sum.inr (Sum.inr (294, 19)),
    Sum.inr (Sum.inr (248, 10)),
    Sum.inr (Sum.inr (178, 14)),
    Sum.inr (Sum.inr (114, 22)),
    Sum.inr (Sum.inr (51, 0)),
    Sum.inr (Sum.inr (242, 13)),
    Sum.inr (Sum.inr (179, 11)),
    Sum.inr (Sum.inr (115, 2)),
    Sum.inr (Sum.inr (57, 20)),
    Sum.inr (Sum.inr (492, 18)),
    Sum.inr (Sum.inr (487, 5)),
    Sum.inr (Sum.inr (492, 7)),
    Sum.inr (Sum.inr (492, 6)),
    Sum.inr (Sum.inr (242, 23)),
    Sum.inr (Sum.inr (115, 9)),
    Sum.inr (Sum.inr (57, 12)),
    Sum.inr (Sum.inr (179, 1)),
    Sum.inr (Sum.inr (57, 10)),
    Sum.inr (Sum.inr (242, 0)),
    Sum.inr (Sum.inr (115, 14)),
    Sum.inr (Sum.inr (179, 22)),
    Sum.inr (Sum.inr (487, 16)),
    Sum.inr (Sum.inr (487, 17)),
    Sum.inr (Sum.inr (492, 4)),
    Sum.inr (Sum.inr (487, 19)),
    Sum.inr (Sum.inr (57, 3)),
    Sum.inr (Sum.inr (115, 21)),
    Sum.inr (Sum.inr (179, 15)),
    Sum.inr (Sum.inr (242, 8)),
    Sum.inr (Sum.inl (88, 35)),
    Sum.inr (Sum.inl (87, 60)),
    Sum.inr (Sum.inl (81, 23)),
    Sum.inr (Sum.inl (83, 33)),
    Sum.inr (Sum.inl (23, 38)),
    Sum.inr (Sum.inl (3, 10)),
    Sum.inr (Sum.inl (23, 46)),
    Sum.inr (Sum.inl (23, 34)),
    Sum.inr (Sum.inl (88, 50)),
    Sum.inr (Sum.inl (81, 8)),
    Sum.inr (Sum.inl (83, 51)),
    Sum.inr (Sum.inl (87, 35)),
    Sum.inr (Sum.inl (83, 35)),
    Sum.inr (Sum.inl (88, 12)),
    Sum.inr (Sum.inl (81, 44)),
    Sum.inr (Sum.inl (87, 29)),
    Sum.inr (Sum.inl (3, 42)),
    Sum.inr (Sum.inl (3, 26)),
    Sum.inr (Sum.inl (23, 42)),
    Sum.inr (Sum.inl (3, 58)),
    Sum.inr (Sum.inl (83, 49)),
    Sum.inr (Sum.inl (81, 51)),
    Sum.inr (Sum.inl (87, 2)),
    Sum.inr (Sum.inl (88, 29)),
    Sum.inr (Sum.inl (196, 18)),
    Sum.inr (Sum.inl (195, 40)),
    Sum.inr (Sum.inl (144, 3)),
    Sum.inr (Sum.inl (167, 35)),
    Sum.inr (Sum.inl (32, 9)),
    Sum.inr (Sum.inl (12, 49)),
    Sum.inr (Sum.inl (32, 1)),
    Sum.inr (Sum.inl (32, 13)),
    Sum.inr (Sum.inl (196, 3)),
    Sum.inr (Sum.inl (144, 35)),
    Sum.inr (Sum.inl (167, 1)),
    Sum.inr (Sum.inl (195, 8)),
    Sum.inr (Sum.inl (167, 3)),
    Sum.inr (Sum.inl (196, 44)),
    Sum.inr (Sum.inl (144, 33)),
    Sum.inr (Sum.inl (195, 32)),
    Sum.inr (Sum.inl (12, 17)),
    Sum.inr (Sum.inl (12, 33)),
    Sum.inr (Sum.inl (32, 5)),
    Sum.inr (Sum.inl (12, 1)),
    Sum.inr (Sum.inl (167, 33)),
    Sum.inr (Sum.inl (144, 1)),
    Sum.inr (Sum.inl (195, 0)),
    Sum.inr (Sum.inl (196, 61)),
    Sum.inr (Sum.inl (210, 27)),
    Sum.inr (Sum.inl (204, 30)),
    Sum.inr (Sum.inl (147, 44)),
    Sum.inr (Sum.inl (170, 12)),
    Sum.inr (Sum.inl (35, 22)),
    Sum.inr (Sum.inl (15, 6)),
    Sum.inr (Sum.inl (35, 30)),
    Sum.inr (Sum.inl (35, 18)),
    Sum.inr (Sum.inl (210, 52)),
    Sum.inr (Sum.inl (147, 62)),
    Sum.inr (Sum.inl (170, 28)),
    Sum.inr (Sum.inl (204, 60)),
    Sum.inr (Sum.inl (170, 30)),
    Sum.inr (Sum.inl (210, 32)),
    Sum.inr (Sum.inl (147, 60)),
    Sum.inr (Sum.inl (204, 35)),
    Sum.inr (Sum.inl (15, 38)),
    Sum.inr (Sum.inl (15, 22)),
    Sum.inr (Sum.inl (35, 26)),
    Sum.inr (Sum.inl (15, 54)),
    Sum.inr (Sum.inl (170, 14)),
    Sum.inr (Sum.inl (147, 46)),
    Sum.inr (Sum.inl (204, 1)),
    Sum.inr (Sum.inl (210, 15)),
    Sum.inr (Sum.inl (133, 51)),
    Sum.inr (Sum.inl (132, 44)),
    Sum.inr (Sum.inl (126, 45)),
    Sum.inr (Sum.inl (128, 36)),
    Sum.inr (Sum.inl (26, 57)),
    Sum.inr (Sum.inl (6, 61)),
    Sum.inr (Sum.inl (26, 49)),
    Sum.inr (Sum.inl (26, 61)),
    Sum.inr (Sum.inl (133, 28)),
    Sum.inr (Sum.inl (126, 12)),
    Sum.inr (Sum.inl (128, 52)),
    Sum.inr (Sum.inl (132, 13)),
    Sum.inr (Sum.inl (128, 44)),
    Sum.inr (Sum.inl (133, 34)),
    Sum.inr (Sum.inl (126, 44)),
    Sum.inr (Sum.inl (132, 51))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock096Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨24576 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock096InputMaskData : ℕ :=
  sixthHex% [
    "9e563bb4563b8b5e3be1563ba26e3ba0663ba3663be1663bad763ba5763b",
    "a9763be17e3bd18e3bf1863bc18e3ba18e3ba9f63a9ff63a84f63af2fe3a",
    "95363a8b3e3aac363af2363a8d5e3aa75e3a98563af25e3ab16e3ab3663a",
    "b0663af2663abe7e3ab67e3aba7e3af2763ac28e3ae2863ad28e3ab28e3a",
    "80f639b6f639adf639dbfe39bc3639a23e39853639db3639a456398e5639",
    "b15e39db56399866399a6e39996e39db6e39977e399f7e39937e39db7639",
    "eb8e39cb8639fb8e399b8e39d3f638e5f638fef63888fe38ef3638f13e38",
    "d63638883638f75638dd5638e25e38885638cb6e38c96638ca6638886638",
    "c47e38cc7e38c07e38887638b88638988e38a88638c8863883fe37b5fe37",
    "aefe37d8f637bf3e37a13637863e37d83e37a75e378d5e37b25637d85e37",
    "9b6637996e379a6e37d86e37947e379c7e37907e37d87637e88637c88e37",
    "f8863798863790f636a6f636bdf636cbfe36ac3636b23e36953636cb3636",
    "b456369e5636a15e36cb56368866368a6e36896e36cb6e368776368f7636",
    "837636cb7e36fb8636db8e36eb86368b8636b9f6358ff63594f635e2fe35",
    "8536359b3e35bc3635e236359d5e35b75e35885635e25e35a16e35a36635",
    "a06635e26635ae7635a67635aa7635e27e35d28635f28e35c28635a28635",
    "eaf634dcf634c7f634b1fe34d63634c83e34ef3634b13634ce5e34e45e34",
    "db5634b15e34f26634f06e34f36e34b16e34fd7634f57634f97634b17e34",
    "818e34a18634918e34f18e34aaf6339cf63387f633f1fe33963e33883633",
    "af3e33f13e338e5633a456339b5e33f15633b26e33b06633b36633f16633",
    "bd7633b57633b97633f17e33c18633e18e33d18633b18633f9f632cff632",
    "d4f632a2fe32c53e32db3632fc3e32a23e32dd5632f75632c85e32a25632",
    "e16632e36e32e06e32a26e32ee7632e67632ea7632a27e32928e32b28632",
    "828e32e28e32d0f631e6f631fdf6318bfe31ec3e31f23631d53e318b3e31",
    "f45e31de5e31e156318b5e31c86e31ca6631c966318b6631c77631cf7631",
    "c376318b7e31bb8e319b8631ab8e31cb8e31"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock096InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock096InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock096OutputMaskData : ℕ :=
  sixthHex% [
    "43727e7fe15e36734f0ea0640e027e4f906468d95e2d0b4f7e9f01769701",
    "4f9f0a43d7014f38643a315e6de27e1cab4f70a06e57e15f5a7a7f797b45",
    "66ec2b3cac205fec2b01ec2b34095f089a7f41086e79db4508395f49ab45",
    "6ee27f2b306e09e42001ec2038e42b34ac204903453c0a7f6bd95f1a906e",
    "60d15c47906d4a0b4d690a77769d192cdd124f9d19119d1955386d69ab4d",
    "20395c18ea7769086d289a770fd34d4a015c199512119d1228951924dd12",
    "5972772c7b4d7ba86d0ae15c13ea7634ab473930671a315d05a6335fe638",
    "3ca63362a6332603471a90675302766bd15d6b73472ae15d0da867487a76",
    "6aae3862a6385bae3357e6385b095d2e006779d347089a76b0fbf297bac3",
    "9a21e3b920d9a6b7b7fcf7bc9fb7b7c1b7b78512c3b981e3f013f2c8c0d9",
    "c862c389f0d9aeb9e3eb6bf2b8ffbcb0f7bc89ffb785b7bc8958d9fc51e3",
    "ab82c3dacbf2c780d3e0c1e2ed5ac2ce5bf8d1cc968b8c9de8cc96b6cc96",
    "f269e2cefac28768d3bfbbf8ce59e28fcbf8a882c2ed50d3cf849dc78c9d",
    "fe8496f2cc9d8f63f8fa6ac2adb9e2dcf0d3d7f1e1f0b0d0fd2bf0de2aca",
    "c1bda49bfdaff8bda4a6bda49358d0afcbf0e659e1de8acaaf68d0eefaca",
    "c9b3f08c61e1dff5afd7fdafeef5a4e2bdaf9f12caea1bf0bdc8d0cc81e1",
    "a4cacb838bfa8e10daad11e0b2868ee8c6858b868ed5868ee063fadcf0da",
    "9562cbadb1e0ad13faec81e0cbc8da8e1acbacce85a4c6859dce8e918685",
    "9d69e0e860dabfb3facefacb5be2767ca34771386752395d3cee3366ae38",
    "05ee335bee336e0b475298671b0a7623d95d237b4762e95d45a067007276",
    "53e6385bee3862e6336eae3813015d66086731db4740927628d95c0f986d",
    "02034d2102774fd51915951276d51928d5191d306d21a34d68315c50e277",
    "21006d60927747db4d02095c20dd1228d51211dd191d9512117a7764734d",
    "33a06d42e95c38a86e1fe95f12727f3173455fa42b05e42066a42b38a42b",
    "7c015f40927f09006e31d34540315f01a34526ea7f63386e30ac2038a420",
    "01ac2b0de420010b4574027f23d15f52986e"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock096OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock096OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock096InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock096InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock096InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock096OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df8617e17e186186185f7e185f85f96175d85f7e17df8617df7df7e17e1",
    "7e185f6df8e38617df7e17e18618617e185f85f85f96175d7e185f7df861",
    "7df7df85f85f86185f95f75d7e17df7df7e185f7df8617e17df85f6e18e3",
    "86185f7e18617e18617df7e186185f95f75d85f8617df7e185f7df7df85f",
    "8617e195f75d86185f85f7df85f7df7df7e17e17e16df8e385f7e18617df",
    "8618617e17e185f7e196175d7df86185f85f7df7df85f7e17e17e16df8e3",
    "7e185f8617df86186185f85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock096OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock096OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block096_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock096Input a) =
      generatedSixthXiShortBlock096InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock096Output a) =
      generatedSixthXiShortBlock096OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock096Input a) =
      generatedSixthXiShortBlock096InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock096Output a) =
      generatedSixthXiShortBlock096OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block096_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock096InputMask a) =
      generatedSixthXiShortBlock096OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock096InputMask a)) *
      generatedSixthXiShortBlock096InputNumerator a =
        generatedSixthXiShortBlock096OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block096_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock096Input a
    let y := generatedSixthXiShortBlock096Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block096_cache a
  have hs := generatedSixth_xi_short_block096_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block096_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock096Input a
    let y := generatedSixthXiShortBlock096Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block096_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block096_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock096Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block096_certificate a).1
    (generatedSixth_xi_short_block096_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
