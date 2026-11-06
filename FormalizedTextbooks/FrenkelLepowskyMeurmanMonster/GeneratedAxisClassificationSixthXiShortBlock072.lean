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
def generatedSixthXiShortBlock072Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (96, 0)),
    Sum.inr (Sum.inr (33, 1)),
    Sum.inr (Sum.inr (225, 2)),
    Sum.inr (Sum.inr (171, 3)),
    Sum.inr (Sum.inr (382, 4)),
    Sum.inr (Sum.inr (373, 5)),
    Sum.inr (Sum.inr (382, 6)),
    Sum.inr (Sum.inr (382, 7)),
    Sum.inr (Sum.inr (96, 8)),
    Sum.inr (Sum.inr (225, 9)),
    Sum.inr (Sum.inr (171, 10)),
    Sum.inr (Sum.inr (33, 11)),
    Sum.inr (Sum.inr (171, 12)),
    Sum.inr (Sum.inr (96, 13)),
    Sum.inr (Sum.inr (225, 14)),
    Sum.inr (Sum.inr (33, 15)),
    Sum.inr (Sum.inr (373, 16)),
    Sum.inr (Sum.inr (373, 17)),
    Sum.inr (Sum.inr (382, 18)),
    Sum.inr (Sum.inr (373, 19)),
    Sum.inr (Sum.inr (171, 20)),
    Sum.inr (Sum.inr (225, 21)),
    Sum.inr (Sum.inr (33, 22)),
    Sum.inr (Sum.inr (96, 23)),
    Sum.inr (Sum.inr (104, 23)),
    Sum.inr (Sum.inr (41, 22)),
    Sum.inr (Sum.inr (233, 21)),
    Sum.inr (Sum.inr (163, 20)),
    Sum.inr (Sum.inr (374, 4)),
    Sum.inr (Sum.inr (381, 5)),
    Sum.inr (Sum.inr (374, 6)),
    Sum.inr (Sum.inr (374, 7)),
    Sum.inr (Sum.inr (104, 13)),
    Sum.inr (Sum.inr (233, 14)),
    Sum.inr (Sum.inr (163, 12)),
    Sum.inr (Sum.inr (41, 15)),
    Sum.inr (Sum.inr (163, 10)),
    Sum.inr (Sum.inr (104, 8)),
    Sum.inr (Sum.inr (233, 9)),
    Sum.inr (Sum.inr (41, 11)),
    Sum.inr (Sum.inr (381, 16)),
    Sum.inr (Sum.inr (381, 17)),
    Sum.inr (Sum.inr (374, 18)),
    Sum.inr (Sum.inr (381, 19)),
    Sum.inr (Sum.inr (163, 3)),
    Sum.inr (Sum.inr (233, 2)),
    Sum.inr (Sum.inr (41, 1)),
    Sum.inr (Sum.inr (104, 0)),
    Sum.inr (Sum.inr (105, 13)),
    Sum.inr (Sum.inr (40, 15)),
    Sum.inr (Sum.inr (232, 14)),
    Sum.inr (Sum.inr (162, 12)),
    Sum.inr (Sum.inr (375, 4)),
    Sum.inr (Sum.inr (380, 5)),
    Sum.inr (Sum.inr (375, 6)),
    Sum.inr (Sum.inr (375, 7)),
    Sum.inr (Sum.inr (105, 23)),
    Sum.inr (Sum.inr (232, 21)),
    Sum.inr (Sum.inr (162, 20)),
    Sum.inr (Sum.inr (40, 22)),
    Sum.inr (Sum.inr (162, 3)),
    Sum.inr (Sum.inr (105, 0)),
    Sum.inr (Sum.inr (232, 2)),
    Sum.inr (Sum.inr (40, 1)),
    Sum.inr (Sum.inr (380, 16)),
    Sum.inr (Sum.inr (380, 17)),
    Sum.inr (Sum.inr (375, 18)),
    Sum.inr (Sum.inr (380, 19)),
    Sum.inr (Sum.inr (162, 10)),
    Sum.inr (Sum.inr (232, 9)),
    Sum.inr (Sum.inr (40, 11)),
    Sum.inr (Sum.inr (105, 8)),
    Sum.inr (Sum.inl (211, 33)),
    Sum.inr (Sum.inl (205, 36)),
    Sum.inr (Sum.inl (148, 5)),
    Sum.inr (Sum.inl (171, 26)),
    Sum.inr (Sum.inl (36, 20)),
    Sum.inr (Sum.inl (16, 14)),
    Sum.inr (Sum.inl (36, 17)),
    Sum.inr (Sum.inl (36, 29)),
    Sum.inr (Sum.inl (211, 62)),
    Sum.inr (Sum.inl (148, 26)),
    Sum.inr (Sum.inl (171, 5)),
    Sum.inr (Sum.inl (205, 59)),
    Sum.inr (Sum.inl (171, 59)),
    Sum.inr (Sum.inl (211, 0)),
    Sum.inr (Sum.inl (148, 36)),
    Sum.inr (Sum.inl (205, 5)),
    Sum.inr (Sum.inl (16, 17)),
    Sum.inr (Sum.inl (16, 33)),
    Sum.inr (Sum.inl (36, 24)),
    Sum.inr (Sum.inl (16, 62)),
    Sum.inr (Sum.inl (171, 36)),
    Sum.inr (Sum.inl (148, 59)),
    Sum.inr (Sum.inl (205, 26)),
    Sum.inr (Sum.inl (211, 31)),
    Sum.inr (Sum.inl (214, 41)),
    Sum.inr (Sum.inl (208, 56)),
    Sum.inr (Sum.inl (151, 26)),
    Sum.inr (Sum.inl (174, 5)),
    Sum.inr (Sum.inl (39, 13)),
    Sum.inr (Sum.inl (19, 2)),
    Sum.inr (Sum.inl (39, 29)),
    Sum.inr (Sum.inl (39, 34)),
    Sum.inr (Sum.inl (214, 54)),
    Sum.inr (Sum.inl (151, 5)),
    Sum.inr (Sum.inl (174, 26)),
    Sum.inr (Sum.inl (208, 39)),
    Sum.inr (Sum.inl (174, 42)),
    Sum.inr (Sum.inl (214, 6)),
    Sum.inr (Sum.inl (151, 53)),
    Sum.inr (Sum.inl (208, 23)),
    Sum.inr (Sum.inl (19, 29)),
    Sum.inr (Sum.inl (19, 45)),
    Sum.inr (Sum.inl (39, 50)),
    Sum.inr (Sum.inl (19, 50)),
    Sum.inr (Sum.inl (174, 53)),
    Sum.inr (Sum.inl (151, 42)),
    Sum.inr (Sum.inl (208, 8)),
    Sum.inr (Sum.inl (214, 25)),
    Sum.inr (Sum.inl (212, 36)),
    Sum.inr (Sum.inl (206, 33)),
    Sum.inr (Sum.inl (149, 40)),
    Sum.inr (Sum.inl (172, 0)),
    Sum.inr (Sum.inl (37, 20)),
    Sum.inr (Sum.inl (17, 27)),
    Sum.inr (Sum.inl (37, 17)),
    Sum.inr (Sum.inl (37, 29)),
    Sum.inr (Sum.inl (212, 33)),
    Sum.inr (Sum.inl (149, 45)),
    Sum.inr (Sum.inl (172, 5)),
    Sum.inr (Sum.inl (206, 36)),
    Sum.inr (Sum.inl (172, 9)),
    Sum.inr (Sum.inl (212, 45)),
    Sum.inr (Sum.inl (149, 33)),
    Sum.inr (Sum.inl (206, 40)),
    Sum.inr (Sum.inl (17, 17)),
    Sum.inr (Sum.inl (17, 18)),
    Sum.inr (Sum.inl (37, 24)),
    Sum.inr (Sum.inl (17, 24)),
    Sum.inr (Sum.inl (172, 12)),
    Sum.inr (Sum.inl (149, 36)),
    Sum.inr (Sum.inl (206, 45)),
    Sum.inr (Sum.inl (212, 40)),
    Sum.inr (Sum.inl (188, 17)),
    Sum.inr (Sum.inl (187, 36)),
    Sum.inr (Sum.inl (143, 5)),
    Sum.inr (Sum.inl (166, 42)),
    Sum.inr (Sum.inl (31, 4)),
    Sum.inr (Sum.inl (11, 11)),
    Sum.inr (Sum.inl (31, 1)),
    Sum.inr (Sum.inl (31, 13)),
    Sum.inr (Sum.inl (188, 20)),
    Sum.inr (Sum.inl (143, 0)),
    Sum.inr (Sum.inl (166, 47)),
    Sum.inr (Sum.inl (187, 33)),
    Sum.inr (Sum.inl (166, 17)),
    Sum.inr (Sum.inl (188, 42)),
    Sum.inr (Sum.inl (143, 62)),
    Sum.inr (Sum.inl (187, 31)),
    Sum.inr (Sum.inl (11, 20)),
    Sum.inr (Sum.inl (11, 36)),
    Sum.inr (Sum.inl (31, 8)),
    Sum.inr (Sum.inl (11, 59)),
    Sum.inr (Sum.inl (166, 20)),
    Sum.inr (Sum.inl (143, 59)),
    Sum.inr (Sum.inl (187, 26)),
    Sum.inr (Sum.inl (188, 47)),
    Sum.inr (Sum.inr (98, 13)),
    Sum.inr (Sum.inr (35, 15)),
    Sum.inr (Sum.inr (227, 14)),
    Sum.inr (Sum.inr (169, 12)),
    Sum.inr (Sum.inr (380, 4)),
    Sum.inr (Sum.inr (375, 5)),
    Sum.inr (Sum.inr (380, 6)),
    Sum.inr (Sum.inr (380, 7)),
    Sum.inr (Sum.inr (98, 23)),
    Sum.inr (Sum.inr (227, 21)),
    Sum.inr (Sum.inr (169, 20)),
    Sum.inr (Sum.inr (35, 22)),
    Sum.inr (Sum.inr (169, 3)),
    Sum.inr (Sum.inr (98, 0)),
    Sum.inr (Sum.inr (227, 2)),
    Sum.inr (Sum.inr (35, 1)),
    Sum.inr (Sum.inr (375, 16)),
    Sum.inr (Sum.inr (375, 17)),
    Sum.inr (Sum.inr (380, 18)),
    Sum.inr (Sum.inr (375, 19)),
    Sum.inr (Sum.inr (169, 10)),
    Sum.inr (Sum.inr (227, 9)),
    Sum.inr (Sum.inr (35, 11)),
    Sum.inr (Sum.inr (98, 8)),
    Sum.inr (Sum.inr (99, 23)),
    Sum.inr (Sum.inr (34, 22)),
    Sum.inr (Sum.inr (226, 21)),
    Sum.inr (Sum.inr (168, 20)),
    Sum.inr (Sum.inr (381, 4)),
    Sum.inr (Sum.inr (374, 5)),
    Sum.inr (Sum.inr (381, 6)),
    Sum.inr (Sum.inr (381, 7)),
    Sum.inr (Sum.inr (99, 13)),
    Sum.inr (Sum.inr (226, 14)),
    Sum.inr (Sum.inr (168, 12)),
    Sum.inr (Sum.inr (34, 15)),
    Sum.inr (Sum.inr (168, 10)),
    Sum.inr (Sum.inr (99, 8)),
    Sum.inr (Sum.inr (226, 9)),
    Sum.inr (Sum.inr (34, 11)),
    Sum.inr (Sum.inr (374, 16)),
    Sum.inr (Sum.inr (374, 17)),
    Sum.inr (Sum.inr (381, 18)),
    Sum.inr (Sum.inr (374, 19)),
    Sum.inr (Sum.inr (168, 3)),
    Sum.inr (Sum.inr (226, 2)),
    Sum.inr (Sum.inr (34, 1)),
    Sum.inr (Sum.inr (99, 0)),
    Sum.inr (Sum.inr (107, 0)),
    Sum.inr (Sum.inr (42, 1)),
    Sum.inr (Sum.inr (234, 2)),
    Sum.inr (Sum.inr (160, 3)),
    Sum.inr (Sum.inr (373, 4)),
    Sum.inr (Sum.inr (382, 5)),
    Sum.inr (Sum.inr (373, 6)),
    Sum.inr (Sum.inr (373, 7)),
    Sum.inr (Sum.inr (107, 8)),
    Sum.inr (Sum.inr (234, 9)),
    Sum.inr (Sum.inr (160, 10)),
    Sum.inr (Sum.inr (42, 11)),
    Sum.inr (Sum.inr (160, 12)),
    Sum.inr (Sum.inr (107, 13)),
    Sum.inr (Sum.inr (234, 14)),
    Sum.inr (Sum.inr (42, 15)),
    Sum.inr (Sum.inr (382, 16)),
    Sum.inr (Sum.inr (382, 17)),
    Sum.inr (Sum.inr (373, 18)),
    Sum.inr (Sum.inr (382, 19)),
    Sum.inr (Sum.inr (160, 20)),
    Sum.inr (Sum.inr (234, 21)),
    Sum.inr (Sum.inr (42, 22)),
    Sum.inr (Sum.inr (107, 23)),
    Sum.inr (Sum.inr (97, 8)),
    Sum.inr (Sum.inr (32, 11)),
    Sum.inr (Sum.inr (224, 9)),
    Sum.inr (Sum.inr (170, 10)),
    Sum.inr (Sum.inr (383, 4)),
    Sum.inr (Sum.inr (372, 5)),
    Sum.inr (Sum.inr (383, 6)),
    Sum.inr (Sum.inr (383, 7)),
    Sum.inr (Sum.inr (97, 0)),
    Sum.inr (Sum.inr (224, 2)),
    Sum.inr (Sum.inr (170, 3)),
    Sum.inr (Sum.inr (32, 1)),
    Sum.inr (Sum.inr (170, 20)),
    Sum.inr (Sum.inr (97, 23)),
    Sum.inr (Sum.inr (224, 21)),
    Sum.inr (Sum.inr (32, 22))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock072Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨18432 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock072InputMaskData : ℕ :=
  sixthHex% [
    "b3d21b99da1ba6da1bccd21b8fea1b8dea1b8ee21bcce21b80fa1b88fa1b",
    "84fa1bccfa1bfc0a1bdc021bec0a1b8c021b85921ab39a1aa8921ade9a1a",
    "b9521aa7521a80521ade521aa13a1a8b321ab4321ade3a1a9d0a1a9f0a1a",
    "9c021ade021a92121a9a121a96121ade121aeeea1acee21afeea1a9ee21a",
    "b8a2198eaa1995a219e3aa198462199a6219bd6219e362199c0219b60a19",
    "890a19e30219a03219a23219a13a19e33a19af2219a72219ab2219e32219",
    "d3da19f3d219c3da19a3d219ea4a18dc4218c74a18b14218d68a18c88a18",
    "ef8a18b18a18ceea18e4e218dbe218b1ea18f2d218f0d218f3da18b1da18",
    "fdca18f5ca18f9ca18b1ca18813a18a13218913a18f13218baba178cb217",
    "97ba17e1b217867a17987a17bf7a17e17a179e1a17b412178b1217e11a17",
    "a22217a02217a32a17e12a17ad3217a53217a93217e13217d1c217f1ca17",
    "c1c217a1ca17a852169e5a16855216f35a169492168a9216ad9216f39216",
    "8cf216a6fa1699fa16f3f216b0c216b2c216b1ca16f3ca16bfda16b7da16",
    "bbda16f3da16c32216e32a16d32216b32a16956215a36a15b86215ce6a15",
    "a9a215b7a21590a215cea215b1ca159bc215a4c215ceca158dfa158ffa15",
    "8cf215cef21582ea158aea1586ea15ceea15fe1215de1a15ee12158e1a15",
    "c78a14f18214ea8a149c8214fb4a14e54a14c24a149c4a14e32214c92a14",
    "f62a149c2214df1a14dd1a14de12149c1214d00214d80214d402149c0214",
    "acf2148cfa14bcf214dcfa14aa0a139c0213870a13f1021396c21388c213",
    "afc213f1c2138eaa13a4a2139ba213f1aa13b29213b09213b39a13f19a13",
    "bd8213b58213b98213f18213c17a13e17213d17a13b17213f8e212ceea12",
    "d5e212a3ea12c42a12da2a12fd2a12a32a12dc4212f64a12c94a12a34212",
    "e07212e27212e17a12a37a12ef6a12e76a12eb6a12a36a12939a12b39212",
    "839a12e39212c5d211f3da11e8d2119eda11f91a11e71a11c01a119e1a11",
    "e17a11cb7211f472119e7a11dd4a11df4a11dc42119e4211d25a11da5a11",
    "d65a119e5a11aeaa118ea211beaa11dea211"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock072InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock072InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock072OutputMaskData : ℕ :=
  sixthHex% [
    "8dc0b0c01390f8c181c012aac0b0b0f062aaa66b90e3b981c16dcfc965cf",
    "f06dc48d65cf818aaaf48390a350b0a359819c698bca68bab6b39a95b2a0",
    "8a25cea125c5b325ceed25ced8c0ba95139aadc18b9512a0e4f0bad422a0",
    "822b9ac7f98b946dc59c65c5a56dced865c5a5caa0d0c39a8710ba87198b",
    "bc6983ea68b296b392b5b2a8aa25c68125cd9325c6cd25c68980b2c45392",
    "fc8183c452a8b5b0b28562a8d36b9296b983b46dcdbc65cd856dc6f865cd",
    "85caa8f0c392a710b2a719839c6982ca68b3b6b39395b2a98a25c7a125cc",
    "b325c7ed25c7a980b3e45393dc8182e452a9e4f0b3d422a9822b93c7f982",
    "946dcc9c65cca56dc7d865ccd48aa9a18393f650b3f65982644443324572",
    "4e9e526d9f6872080659080d4b080615080651ad721c7e5224ac431c7f68",
    "1cdd722c0f687a06523fd4431d000d15080d2c000651080d5de76828ee52",
    "7f3d727f34433144496745781b9e58389f6227080c0c08071e080c40080c",
    "04ad78497e5871ac49497f62389d78084f625e46581b9449480007400807",
    "79000c04080779a7620cae585b7d785b74491144414745703b9e50189f6a",
    "0708042c080f3e080460080455ed70183e5020ec41183f6a69dd70590f6a",
    "0f06504ad44168000f60080f59000424080f59a76a2cae507b7d707b7441",
    "3144406745711b9e51389f6b2708050c080e1e080540080575ed71383e51",
    "00ec40383f6b389d71084f6b5e46511b944048000e40080e79000504080e",
    "08e76b7dee512a3d712a3440d821898e20b8f2fb98d1faa2bf2dcc942dc7",
    "862dccd82dccedc8b8a01b9898c989a01aa2a0b8b8906aa2c6639883b189",
    "a165c7a96dc79065cced6dc790c2a2e5cb98b218b8b21189f82188ae20b9",
    "d2fb99f1faa39f2dcdb42dc6a62dcdf82dcdcdc8b9801b99b8c988801aa3",
    "f1f8b9c12aa3972399d2f1888165c6896dc6b065cdcd6dc6c182a3b48b99",
    "e358b9e35188d821808e20b1f2fb91d1faabbf2dc5942dce862dc5d82dc5",
    "9c88b1d15b91e98980d15aaba0b8b1906aabc6639183b180a165cea96dce",
    "9065c5ed6dcee182ab948b91c358b1c35180"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock072OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock072OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock072InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock072InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock072InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock072OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df8618617e185f85f85f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df8616df8e37df8618618617e185f7e17e17df7df6df8e37e185f7e185f",
    "7e185f7e185f7e17df6e18e37e17df7e17df86185f7df7e185f7df95f75d",
    "86185f7df85f7df7e18617e185f86195f75d7e17df85f8617df7e17df7e1",
    "85f7df95f75d7df7e17df85f7df7e17df85f7df7df6df8e37e185f7e185f",
    "7e185f7e185f7df8616df8e37df8618618617e185f7e17e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock072OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock072OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block072_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock072Input a) =
      generatedSixthXiShortBlock072InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock072Output a) =
      generatedSixthXiShortBlock072OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock072Input a) =
      generatedSixthXiShortBlock072InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock072Output a) =
      generatedSixthXiShortBlock072OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block072_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock072InputMask a) =
      generatedSixthXiShortBlock072OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock072InputMask a)) *
      generatedSixthXiShortBlock072InputNumerator a =
        generatedSixthXiShortBlock072OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block072_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock072Input a
    let y := generatedSixthXiShortBlock072Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block072_cache a
  have hs := generatedSixth_xi_short_block072_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block072_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock072Input a
    let y := generatedSixthXiShortBlock072Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block072_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block072_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock072Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block072_certificate a).1
    (generatedSixth_xi_short_block072_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
