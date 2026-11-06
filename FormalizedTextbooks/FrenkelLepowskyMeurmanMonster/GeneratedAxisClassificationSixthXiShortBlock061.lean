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
def generatedSixthXiShortBlock061Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (511, 16)),
    Sum.inr (Sum.inr (511, 17)),
    Sum.inr (Sum.inr (500, 18)),
    Sum.inr (Sum.inr (511, 19)),
    Sum.inr (Sum.inr (33, 20)),
    Sum.inr (Sum.inr (107, 21)),
    Sum.inr (Sum.inr (171, 22)),
    Sum.inr (Sum.inr (234, 23)),
    Sum.inr (Sum.inl (212, 59)),
    Sum.inr (Sum.inl (206, 12)),
    Sum.inr (Sum.inl (149, 8)),
    Sum.inr (Sum.inl (172, 13)),
    Sum.inr (Sum.inl (37, 4)),
    Sum.inr (Sum.inl (17, 11)),
    Sum.inr (Sum.inl (37, 1)),
    Sum.inr (Sum.inl (37, 13)),
    Sum.inr (Sum.inl (212, 62)),
    Sum.inr (Sum.inl (149, 13)),
    Sum.inr (Sum.inl (172, 8)),
    Sum.inr (Sum.inl (206, 9)),
    Sum.inr (Sum.inl (172, 4)),
    Sum.inr (Sum.inl (212, 50)),
    Sum.inr (Sum.inl (149, 1)),
    Sum.inr (Sum.inl (206, 5)),
    Sum.inr (Sum.inl (17, 1)),
    Sum.inr (Sum.inl (17, 2)),
    Sum.inr (Sum.inl (37, 8)),
    Sum.inr (Sum.inl (17, 8)),
    Sum.inr (Sum.inl (172, 1)),
    Sum.inr (Sum.inl (149, 4)),
    Sum.inr (Sum.inl (206, 0)),
    Sum.inr (Sum.inl (212, 55)),
    Sum.inr (Sum.inl (188, 57)),
    Sum.inr (Sum.inl (187, 22)),
    Sum.inr (Sum.inl (143, 45)),
    Sum.inr (Sum.inl (166, 48)),
    Sum.inr (Sum.inl (31, 43)),
    Sum.inr (Sum.inl (11, 2)),
    Sum.inr (Sum.inl (31, 46)),
    Sum.inr (Sum.inl (31, 34)),
    Sum.inr (Sum.inl (188, 60)),
    Sum.inr (Sum.inl (143, 40)),
    Sum.inr (Sum.inl (166, 53)),
    Sum.inr (Sum.inl (187, 19)),
    Sum.inr (Sum.inl (166, 11)),
    Sum.inr (Sum.inl (188, 2)),
    Sum.inr (Sum.inl (143, 22)),
    Sum.inr (Sum.inl (187, 45)),
    Sum.inr (Sum.inl (11, 29)),
    Sum.inr (Sum.inl (11, 45)),
    Sum.inr (Sum.inl (31, 39)),
    Sum.inr (Sum.inl (11, 50)),
    Sum.inr (Sum.inl (166, 14)),
    Sum.inr (Sum.inl (143, 19)),
    Sum.inr (Sum.inl (187, 40)),
    Sum.inr (Sum.inl (188, 7)),
    Sum.inr (Sum.inl (211, 57)),
    Sum.inr (Sum.inl (205, 42)),
    Sum.inr (Sum.inl (148, 29)),
    Sum.inr (Sum.inl (171, 20)),
    Sum.inr (Sum.inl (36, 43)),
    Sum.inr (Sum.inl (16, 2)),
    Sum.inr (Sum.inl (36, 46)),
    Sum.inr (Sum.inl (36, 34)),
    Sum.inr (Sum.inl (211, 38)),
    Sum.inr (Sum.inl (148, 2)),
    Sum.inr (Sum.inl (171, 11)),
    Sum.inr (Sum.inl (205, 53)),
    Sum.inr (Sum.inl (171, 53)),
    Sum.inr (Sum.inl (211, 24)),
    Sum.inr (Sum.inl (148, 60)),
    Sum.inr (Sum.inl (205, 11)),
    Sum.inr (Sum.inl (16, 29)),
    Sum.inr (Sum.inl (16, 45)),
    Sum.inr (Sum.inl (36, 39)),
    Sum.inr (Sum.inl (16, 50)),
    Sum.inr (Sum.inl (171, 42)),
    Sum.inr (Sum.inl (148, 35)),
    Sum.inr (Sum.inl (205, 20)),
    Sum.inr (Sum.inl (211, 7)),
    Sum.inr (Sum.inl (214, 44)),
    Sum.inr (Sum.inl (208, 51)),
    Sum.inr (Sum.inl (151, 28)),
    Sum.inr (Sum.inl (174, 8)),
    Sum.inr (Sum.inl (39, 7)),
    Sum.inr (Sum.inl (19, 8)),
    Sum.inr (Sum.inl (39, 23)),
    Sum.inr (Sum.inl (39, 40)),
    Sum.inr (Sum.inl (214, 51)),
    Sum.inr (Sum.inl (151, 3)),
    Sum.inr (Sum.inl (174, 23)),
    Sum.inr (Sum.inl (208, 44)),
    Sum.inr (Sum.inl (174, 39)),
    Sum.inr (Sum.inl (214, 3)),
    Sum.inr (Sum.inl (151, 51)),
    Sum.inr (Sum.inl (208, 28)),
    Sum.inr (Sum.inl (19, 23)),
    Sum.inr (Sum.inl (19, 39)),
    Sum.inr (Sum.inl (39, 56)),
    Sum.inr (Sum.inl (19, 56)),
    Sum.inr (Sum.inl (174, 56)),
    Sum.inr (Sum.inl (151, 44)),
    Sum.inr (Sum.inl (208, 3)),
    Sum.inr (Sum.inl (214, 28)),
    Sum.inr (Sum.inr (303, 8)),
    Sum.inr (Sum.inr (366, 15)),
    Sum.inr (Sum.inr (430, 21)),
    Sum.inr (Sum.inr (484, 3)),
    Sum.inr (Sum.inr (49, 18)),
    Sum.inr (Sum.inr (58, 5)),
    Sum.inr (Sum.inr (49, 7)),
    Sum.inr (Sum.inr (49, 6)),
    Sum.inr (Sum.inr (303, 0)),
    Sum.inr (Sum.inr (430, 14)),
    Sum.inr (Sum.inr (484, 10)),
    Sum.inr (Sum.inr (366, 22)),
    Sum.inr (Sum.inr (484, 12)),
    Sum.inr (Sum.inr (303, 23)),
    Sum.inr (Sum.inr (430, 9)),
    Sum.inr (Sum.inr (366, 1)),
    Sum.inr (Sum.inr (58, 16)),
    Sum.inr (Sum.inr (58, 17)),
    Sum.inr (Sum.inr (49, 4)),
    Sum.inr (Sum.inr (58, 19)),
    Sum.inr (Sum.inr (484, 20)),
    Sum.inr (Sum.inr (430, 2)),
    Sum.inr (Sum.inr (366, 11)),
    Sum.inr (Sum.inr (303, 13)),
    Sum.inr (Sum.inr (485, 0)),
    Sum.inr (Sum.inr (420, 22)),
    Sum.inr (Sum.inr (356, 14)),
    Sum.inr (Sum.inr (302, 10)),
    Sum.inr (Sum.inr (251, 18)),
    Sum.inr (Sum.inr (240, 5)),
    Sum.inr (Sum.inr (251, 7)),
    Sum.inr (Sum.inr (251, 6)),
    Sum.inr (Sum.inr (485, 8)),
    Sum.inr (Sum.inr (356, 21)),
    Sum.inr (Sum.inr (302, 3)),
    Sum.inr (Sum.inr (420, 15)),
    Sum.inr (Sum.inr (302, 20)),
    Sum.inr (Sum.inr (485, 13)),
    Sum.inr (Sum.inr (356, 2)),
    Sum.inr (Sum.inr (420, 11)),
    Sum.inr (Sum.inr (240, 16)),
    Sum.inr (Sum.inr (240, 17)),
    Sum.inr (Sum.inr (251, 4)),
    Sum.inr (Sum.inr (240, 19)),
    Sum.inr (Sum.inr (302, 12)),
    Sum.inr (Sum.inr (356, 9)),
    Sum.inr (Sum.inr (420, 1)),
    Sum.inr (Sum.inr (485, 23)),
    Sum.inr (Sum.inr (423, 23)),
    Sum.inr (Sum.inr (486, 1)),
    Sum.inr (Sum.inr (294, 9)),
    Sum.inr (Sum.inr (364, 12)),
    Sum.inr (Sum.inr (185, 18)),
    Sum.inr (Sum.inr (178, 5)),
    Sum.inr (Sum.inr (185, 7)),
    Sum.inr (Sum.inr (185, 6)),
    Sum.inr (Sum.inr (423, 13)),
    Sum.inr (Sum.inr (294, 2)),
    Sum.inr (Sum.inr (364, 20)),
    Sum.inr (Sum.inr (486, 11)),
    Sum.inr (Sum.inr (364, 3)),
    Sum.inr (Sum.inr (423, 8)),
    Sum.inr (Sum.inr (294, 21)),
    Sum.inr (Sum.inr (486, 15)),
    Sum.inr (Sum.inr (178, 16)),
    Sum.inr (Sum.inr (178, 17)),
    Sum.inr (Sum.inr (185, 4)),
    Sum.inr (Sum.inr (178, 19)),
    Sum.inr (Sum.inr (364, 10)),
    Sum.inr (Sum.inr (294, 14)),
    Sum.inr (Sum.inr (486, 22)),
    Sum.inr (Sum.inr (423, 0)),
    Sum.inr (Sum.inr (358, 13)),
    Sum.inr (Sum.inr (295, 11)),
    Sum.inr (Sum.inr (487, 2)),
    Sum.inr (Sum.inr (429, 20)),
    Sum.inr (Sum.inr (120, 18)),
    Sum.inr (Sum.inr (115, 5)),
    Sum.inr (Sum.inr (120, 7)),
    Sum.inr (Sum.inr (120, 6)),
    Sum.inr (Sum.inr (358, 23)),
    Sum.inr (Sum.inr (487, 9)),
    Sum.inr (Sum.inr (429, 12)),
    Sum.inr (Sum.inr (295, 1)),
    Sum.inr (Sum.inr (429, 10)),
    Sum.inr (Sum.inr (358, 0)),
    Sum.inr (Sum.inr (487, 14)),
    Sum.inr (Sum.inr (295, 22)),
    Sum.inr (Sum.inr (115, 16)),
    Sum.inr (Sum.inr (115, 17)),
    Sum.inr (Sum.inr (120, 4)),
    Sum.inr (Sum.inr (115, 19)),
    Sum.inr (Sum.inr (429, 3)),
    Sum.inr (Sum.inr (487, 21)),
    Sum.inr (Sum.inr (295, 15)),
    Sum.inr (Sum.inr (358, 8)),
    Sum.inr (Sum.inl (133, 55)),
    Sum.inr (Sum.inl (132, 40)),
    Sum.inr (Sum.inl (126, 8)),
    Sum.inr (Sum.inl (128, 26)),
    Sum.inr (Sum.inl (26, 10)),
    Sum.inr (Sum.inl (6, 0)),
    Sum.inr (Sum.inl (26, 2)),
    Sum.inr (Sum.inl (26, 14)),
    Sum.inr (Sum.inl (133, 24)),
    Sum.inr (Sum.inl (126, 41)),
    Sum.inr (Sum.inl (128, 10)),
    Sum.inr (Sum.inl (132, 9)),
    Sum.inr (Sum.inl (128, 18)),
    Sum.inr (Sum.inl (133, 38)),
    Sum.inr (Sum.inl (126, 9)),
    Sum.inr (Sum.inl (132, 55)),
    Sum.inr (Sum.inl (6, 32)),
    Sum.inr (Sum.inl (6, 16)),
    Sum.inr (Sum.inl (26, 6)),
    Sum.inr (Sum.inl (6, 48)),
    Sum.inr (Sum.inl (128, 2)),
    Sum.inr (Sum.inl (126, 40)),
    Sum.inr (Sum.inl (132, 22)),
    Sum.inr (Sum.inl (133, 9)),
    Sum.inr (Sum.inl (210, 58)),
    Sum.inr (Sum.inl (204, 26)),
    Sum.inr (Sum.inl (147, 58)),
    Sum.inr (Sum.inl (170, 40)),
    Sum.inr (Sum.inl (35, 58)),
    Sum.inr (Sum.inl (15, 12)),
    Sum.inr (Sum.inl (35, 50)),
    Sum.inr (Sum.inl (35, 62)),
    Sum.inr (Sum.inl (210, 21)),
    Sum.inr (Sum.inl (147, 40)),
    Sum.inr (Sum.inl (170, 56)),
    Sum.inr (Sum.inl (204, 56)),
    Sum.inr (Sum.inl (170, 58)),
    Sum.inr (Sum.inl (210, 1)),
    Sum.inr (Sum.inl (147, 42)),
    Sum.inr (Sum.inl (204, 39)),
    Sum.inr (Sum.inl (15, 44)),
    Sum.inr (Sum.inl (15, 28)),
    Sum.inr (Sum.inl (35, 54)),
    Sum.inr (Sum.inl (15, 60)),
    Sum.inr (Sum.inl (170, 42)),
    Sum.inr (Sum.inl (147, 56)),
    Sum.inr (Sum.inl (204, 5)),
    Sum.inr (Sum.inl (210, 46)),
    Sum.inr (Sum.inl (196, 54)),
    Sum.inr (Sum.inl (195, 45)),
    Sum.inr (Sum.inl (144, 37)),
    Sum.inr (Sum.inl (167, 55)),
    Sum.inr (Sum.inl (32, 21)),
    Sum.inr (Sum.inl (12, 55)),
    Sum.inr (Sum.inl (32, 29)),
    Sum.inr (Sum.inl (32, 17))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock061Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨15616 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock061InputMaskData : ℕ :=
  sixthHex% [
    "c32066cb2066c728668f2866bfd8669fd866afd866cfd866ea9065dc9065",
    "c79865b19865d65065c85065ef5065b15065ce3865e43065db3065b13865",
    "f20865f00065f30865b10065fd1065f51065f91865b1186581e865a1e865",
    "91e865f1e865ab70649d7064867864f0786497b06489b064aeb064f0b064",
    "8fd864a5d0649ad064f0d864b3e064b1e864b2e064f0e864bcf064b4f064",
    "b8f864f0f864c00064e00064d00064b00064d5f863e3f863f8f0638ef063",
    "e93063f73063d030638e3063f15863db5063e450638e5863cd6063cf6863",
    "cc60638e6863c27863ca7863c670638e7063be80639e8063ae8063ce8063",
    "941862a21862b91062cf1062a8d062b6d06291d062cfd062b0b8629ab062",
    "a5b062cfb8628c88628e80628d8862cf80628398628b9862879062cf9062",
    "ff6862df6862ef68628f6862aa28619c2861872061f1206196e06188e061",
    "afe061f1e0618e8061a488619b8861f18061b2b061b0b861b3b061f1b861",
    "bda861b5a861b9a061f1a061c15861e15861d15861b15861abc8609dc860",
    "86c060f0c060970060890060ae0060f000608f6060a568609a6860f06060",
    "b35860b15060b25860f05060bc4860b44860b84060f04060c0b060e0b060",
    "d0b060b0b0609b880fad880fb6880fc0880fa7480fb9480f9e480fc0480f",
    "bf280f95280faa280fc0280f83180f81180f82180fc0180f8c000f84000f",
    "88000fc0000ff0f00fd0f00fe0f00f80f00fdb600eed600ef6600e80600e",
    "e7a00ef9a00edea00e80a00effc00ed5c00eeac00e80c00ec3f80ec1f80e",
    "c2f80e80f80ecce80ec4e80ec8e80e80e80eb0100e90100ea0100ec0100e",
    "db500ded500df6500d80500de7900df9900dde900d80900dfff80dd5f80d",
    "eaf80d80f80dc3c00dc1c00dc2c00d80c00dccd80dc4d80dc8d80d80d80d",
    "b0200d90200da0200dc0200ddbb80cedb80cf6b80c80b80ce7780cf9780c",
    "de780c80780cff100cd5100cea100c80100cc3200cc1200cc2200c80200c",
    "cc300cc4300cc8300c80300cb0c00c90c00ca0c00cc0c00cdb300bed300b",
    "f6300b80300be7f80bf9f80bdef80b80f80b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock061InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock061InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock061OutputMaskData : ℕ :=
  sixthHex% [
    "2acd1222c5126a8d191785121b6a771f234d39b06d48f95c25806e02c15f",
    "7e1a7f2c5b4533cc2b18cc200acc2b54cc2b61295f2cfa7f14286e2cfb45",
    "5d195f1c8b454a827f7e106e2d8420258c206dc42b10cc201c2345186a7f",
    "3ef95f4fb06e71534f56127e2ac95e788864671f0a4c1f015e1f0a001f0a",
    "35fa7e78295e40fb4f782864788a7e3918646f115e5b834f795701715f01",
    "39170a441f0139b0643df95e1b6a7e6a234fece5a6cba497b77fb7e53e8d",
    "8be9e3a0e9e8b2e9e3ece9e3d90c9794dfb7ac0da694de8d947c97d5ee8d",
    "83e7b7b775a6e4e1e8ece9e8a4a1e3d9a9e8d5468dd10fb7f79c9786d5a6",
    "b836879f77b6e3ac96b1edacdf3ac2f43ac9e63ac2b83ac28ddfb6c00c96",
    "f8de87c00dacb1efb6f07daca6749692e687b032c9b83ac9f072c28d7ac9",
    "f0d5acf49c96d20fb6a34687bf7fb5983e84e4e5a4b6a49ed873f0f373fb",
    "e173f0bf73f0fbd684b605a48ed7b5b6049ec7e68486749ed07da4e4efb5",
    "b77bfbbf73fbf73bf08a33fbf79c9ef3d5a4d54684a40fb59eac9fb9edae",
    "c5368e9777b4f9a0dad2a0d1c0a0da9ea0dada05ae97d68eaf049f97d7b4",
    "9775aed6e7b480ee8eb47c9f96a8d19ea0d1d6e8daabe0d1a70fb4a3468e",
    "85d5aef49c9f0144412605702b9e5079df6a1708043c080f2e0804700804",
    "34ad70083e5030ec41797f6a089d70384f6a1f06505ad44178000f70080f",
    "49000434080f38e76a3cae501a3d706b7441334c40140d711996514bd76b",
    "2500050e000e1c000542000506a5713a365102e4404b776b4bd5717b076b",
    "5c4e51199c404a080e42000e7b080506000e7baf6b7fe651597571283c40",
    "1b4c433c0d7231965263d7680d000626000d3400066a00065fe572637652",
    "5ba443123768129572224768050e5240dc4362080d6a000d5308062e000d",
    "53af6857e652717572003c435c44497b0578769e5824df624a080c610807",
    "73080c2d080c18ed78247e581cac49553f6224dd78140f62334658769449",
    "2500072d080714000c69080765e76261ae58473d783674499bbb9abcfaab",
    "b1618be320b1fcb7dfd7b7d4c5b7df9bb7df"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock061OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock061OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock061InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock061InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock061InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock061OutputNumeratorData : ℕ :=
  sixthHex% [
    "8618617e185f85f85f96175d85f7e17df8617df7df7e17e185f7e196175d",
    "8617df85f85f7df7df7e185f86185f95f75d7e17df7df7e185f7df8617e1",
    "8617e195f75d7df7e185f7df85f7df86185f7df7e16e18e37e17df86185f",
    "7e18618617e17df85f6e18e37df7e17e18617e186186185f7e17df6e18e3",
    "85f8617e17df86185f86185f85f7df95f75d7df7e17df85f7df7e17df85f",
    "85f86195f75d85f86185f8617df7e186185f85f7df95f75d86185f7df85f",
    "7df7e18617e17df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock061OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock061OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block061_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock061Input a) =
      generatedSixthXiShortBlock061InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock061Output a) =
      generatedSixthXiShortBlock061OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock061Input a) =
      generatedSixthXiShortBlock061InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock061Output a) =
      generatedSixthXiShortBlock061OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block061_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock061InputMask a) =
      generatedSixthXiShortBlock061OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock061InputMask a)) *
      generatedSixthXiShortBlock061InputNumerator a =
        generatedSixthXiShortBlock061OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block061_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock061Input a
    let y := generatedSixthXiShortBlock061Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block061_cache a
  have hs := generatedSixth_xi_short_block061_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block061_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock061Input a
    let y := generatedSixthXiShortBlock061Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block061_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block061_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock061Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block061_certificate a).1
    (generatedSixth_xi_short_block061_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
