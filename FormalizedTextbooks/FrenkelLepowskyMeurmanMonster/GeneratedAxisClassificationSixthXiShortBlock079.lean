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
def generatedSixthXiShortBlock079Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (319, 16)),
    Sum.inr (Sum.inr (319, 17)),
    Sum.inr (Sum.inr (308, 18)),
    Sum.inr (Sum.inr (319, 19)),
    Sum.inr (Sum.inr (225, 20)),
    Sum.inr (Sum.inr (171, 21)),
    Sum.inr (Sum.inr (107, 22)),
    Sum.inr (Sum.inr (42, 23)),
    Sum.inr (Sum.inl (212, 4)),
    Sum.inr (Sum.inl (206, 1)),
    Sum.inr (Sum.inl (149, 5)),
    Sum.inr (Sum.inl (172, 45)),
    Sum.inr (Sum.inl (37, 36)),
    Sum.inr (Sum.inl (17, 43)),
    Sum.inr (Sum.inl (37, 33)),
    Sum.inr (Sum.inl (37, 45)),
    Sum.inr (Sum.inl (212, 1)),
    Sum.inr (Sum.inl (149, 0)),
    Sum.inr (Sum.inl (172, 40)),
    Sum.inr (Sum.inl (206, 4)),
    Sum.inr (Sum.inl (172, 36)),
    Sum.inr (Sum.inl (212, 13)),
    Sum.inr (Sum.inl (149, 12)),
    Sum.inr (Sum.inl (206, 8)),
    Sum.inr (Sum.inl (17, 33)),
    Sum.inr (Sum.inl (17, 34)),
    Sum.inr (Sum.inl (37, 40)),
    Sum.inr (Sum.inl (17, 40)),
    Sum.inr (Sum.inl (172, 33)),
    Sum.inr (Sum.inl (149, 9)),
    Sum.inr (Sum.inl (206, 13)),
    Sum.inr (Sum.inl (212, 8)),
    Sum.inr (Sum.inl (188, 9)),
    Sum.inr (Sum.inl (187, 12)),
    Sum.inr (Sum.inl (143, 55)),
    Sum.inr (Sum.inl (166, 0)),
    Sum.inr (Sum.inl (31, 20)),
    Sum.inr (Sum.inl (11, 14)),
    Sum.inr (Sum.inl (31, 17)),
    Sum.inr (Sum.inl (31, 29)),
    Sum.inr (Sum.inl (188, 12)),
    Sum.inr (Sum.inl (143, 50)),
    Sum.inr (Sum.inl (166, 5)),
    Sum.inr (Sum.inl (187, 9)),
    Sum.inr (Sum.inl (166, 59)),
    Sum.inr (Sum.inl (188, 50)),
    Sum.inr (Sum.inl (143, 12)),
    Sum.inr (Sum.inl (187, 55)),
    Sum.inr (Sum.inl (11, 17)),
    Sum.inr (Sum.inl (11, 33)),
    Sum.inr (Sum.inl (31, 24)),
    Sum.inr (Sum.inl (11, 62)),
    Sum.inr (Sum.inl (166, 62)),
    Sum.inr (Sum.inl (143, 9)),
    Sum.inr (Sum.inl (187, 50)),
    Sum.inr (Sum.inl (188, 55)),
    Sum.inr (Sum.inl (211, 45)),
    Sum.inr (Sum.inl (205, 60)),
    Sum.inr (Sum.inl (148, 19)),
    Sum.inr (Sum.inl (171, 12)),
    Sum.inr (Sum.inl (36, 52)),
    Sum.inr (Sum.inl (16, 8)),
    Sum.inr (Sum.inl (36, 49)),
    Sum.inr (Sum.inl (36, 61)),
    Sum.inr (Sum.inl (211, 50)),
    Sum.inr (Sum.inl (148, 12)),
    Sum.inr (Sum.inl (171, 19)),
    Sum.inr (Sum.inl (205, 35)),
    Sum.inr (Sum.inl (171, 45)),
    Sum.inr (Sum.inl (211, 12)),
    Sum.inr (Sum.inl (148, 50)),
    Sum.inr (Sum.inl (205, 29)),
    Sum.inr (Sum.inl (16, 23)),
    Sum.inr (Sum.inl (16, 39)),
    Sum.inr (Sum.inl (36, 56)),
    Sum.inr (Sum.inl (16, 56)),
    Sum.inr (Sum.inl (171, 50)),
    Sum.inr (Sum.inl (148, 45)),
    Sum.inr (Sum.inl (205, 2)),
    Sum.inr (Sum.inl (211, 19)),
    Sum.inr (Sum.inl (214, 47)),
    Sum.inr (Sum.inl (208, 62)),
    Sum.inr (Sum.inl (151, 17)),
    Sum.inr (Sum.inl (174, 14)),
    Sum.inr (Sum.inl (39, 1)),
    Sum.inr (Sum.inl (19, 14)),
    Sum.inr (Sum.inl (39, 17)),
    Sum.inr (Sum.inl (39, 46)),
    Sum.inr (Sum.inl (214, 48)),
    Sum.inr (Sum.inl (151, 14)),
    Sum.inr (Sum.inl (174, 17)),
    Sum.inr (Sum.inl (208, 33)),
    Sum.inr (Sum.inl (174, 33)),
    Sum.inr (Sum.inl (214, 0)),
    Sum.inr (Sum.inl (151, 62)),
    Sum.inr (Sum.inl (208, 17)),
    Sum.inr (Sum.inl (19, 17)),
    Sum.inr (Sum.inl (19, 33)),
    Sum.inr (Sum.inl (39, 62)),
    Sum.inr (Sum.inl (19, 62)),
    Sum.inr (Sum.inl (174, 62)),
    Sum.inr (Sum.inl (151, 33)),
    Sum.inr (Sum.inl (208, 14)),
    Sum.inr (Sum.inl (214, 31)),
    Sum.inr (Sum.inr (495, 8)),
    Sum.inr (Sum.inr (430, 15)),
    Sum.inr (Sum.inr (366, 21)),
    Sum.inr (Sum.inr (292, 3)),
    Sum.inr (Sum.inr (241, 18)),
    Sum.inr (Sum.inr (250, 5)),
    Sum.inr (Sum.inr (241, 7)),
    Sum.inr (Sum.inr (241, 6)),
    Sum.inr (Sum.inr (495, 0)),
    Sum.inr (Sum.inr (366, 14)),
    Sum.inr (Sum.inr (292, 10)),
    Sum.inr (Sum.inr (430, 22)),
    Sum.inr (Sum.inr (292, 12)),
    Sum.inr (Sum.inr (495, 23)),
    Sum.inr (Sum.inr (366, 9)),
    Sum.inr (Sum.inr (430, 1)),
    Sum.inr (Sum.inr (250, 16)),
    Sum.inr (Sum.inr (250, 17)),
    Sum.inr (Sum.inr (241, 4)),
    Sum.inr (Sum.inr (250, 19)),
    Sum.inr (Sum.inr (292, 20)),
    Sum.inr (Sum.inr (366, 2)),
    Sum.inr (Sum.inr (430, 11)),
    Sum.inr (Sum.inr (495, 13)),
    Sum.inr (Sum.inr (293, 0)),
    Sum.inr (Sum.inr (356, 22)),
    Sum.inr (Sum.inr (420, 14)),
    Sum.inr (Sum.inr (494, 10)),
    Sum.inr (Sum.inr (59, 18)),
    Sum.inr (Sum.inr (48, 5)),
    Sum.inr (Sum.inr (59, 7)),
    Sum.inr (Sum.inr (59, 6)),
    Sum.inr (Sum.inr (293, 8)),
    Sum.inr (Sum.inr (420, 21)),
    Sum.inr (Sum.inr (494, 3)),
    Sum.inr (Sum.inr (356, 15)),
    Sum.inr (Sum.inr (494, 20)),
    Sum.inr (Sum.inr (293, 13)),
    Sum.inr (Sum.inr (420, 2)),
    Sum.inr (Sum.inr (356, 11)),
    Sum.inr (Sum.inr (48, 16)),
    Sum.inr (Sum.inr (48, 17)),
    Sum.inr (Sum.inr (59, 4)),
    Sum.inr (Sum.inr (48, 19)),
    Sum.inr (Sum.inr (494, 12)),
    Sum.inr (Sum.inr (420, 9)),
    Sum.inr (Sum.inr (356, 1)),
    Sum.inr (Sum.inr (293, 23)),
    Sum.inr (Sum.inr (359, 23)),
    Sum.inr (Sum.inr (294, 1)),
    Sum.inr (Sum.inr (486, 9)),
    Sum.inr (Sum.inr (428, 12)),
    Sum.inr (Sum.inr (121, 18)),
    Sum.inr (Sum.inr (114, 5)),
    Sum.inr (Sum.inr (121, 7)),
    Sum.inr (Sum.inr (121, 6)),
    Sum.inr (Sum.inr (359, 13)),
    Sum.inr (Sum.inr (486, 2)),
    Sum.inr (Sum.inr (428, 20)),
    Sum.inr (Sum.inr (294, 11)),
    Sum.inr (Sum.inr (428, 3)),
    Sum.inr (Sum.inr (359, 8)),
    Sum.inr (Sum.inr (486, 21)),
    Sum.inr (Sum.inr (294, 15)),
    Sum.inr (Sum.inr (114, 16)),
    Sum.inr (Sum.inr (114, 17)),
    Sum.inr (Sum.inr (121, 4)),
    Sum.inr (Sum.inr (114, 19)),
    Sum.inr (Sum.inr (428, 10)),
    Sum.inr (Sum.inr (486, 14)),
    Sum.inr (Sum.inr (294, 22)),
    Sum.inr (Sum.inr (359, 0)),
    Sum.inr (Sum.inr (422, 13)),
    Sum.inr (Sum.inr (487, 11)),
    Sum.inr (Sum.inr (295, 2)),
    Sum.inr (Sum.inr (365, 20)),
    Sum.inr (Sum.inr (184, 18)),
    Sum.inr (Sum.inr (179, 5)),
    Sum.inr (Sum.inr (184, 7)),
    Sum.inr (Sum.inr (184, 6)),
    Sum.inr (Sum.inr (422, 23)),
    Sum.inr (Sum.inr (295, 9)),
    Sum.inr (Sum.inr (365, 12)),
    Sum.inr (Sum.inr (487, 1)),
    Sum.inr (Sum.inr (365, 10)),
    Sum.inr (Sum.inr (422, 0)),
    Sum.inr (Sum.inr (295, 14)),
    Sum.inr (Sum.inr (487, 22)),
    Sum.inr (Sum.inr (179, 16)),
    Sum.inr (Sum.inr (179, 17)),
    Sum.inr (Sum.inr (184, 4)),
    Sum.inr (Sum.inr (179, 19)),
    Sum.inr (Sum.inr (365, 3)),
    Sum.inr (Sum.inr (295, 21)),
    Sum.inr (Sum.inr (487, 15)),
    Sum.inr (Sum.inr (422, 8)),
    Sum.inr (Sum.inl (133, 23)),
    Sum.inr (Sum.inl (132, 54)),
    Sum.inr (Sum.inl (126, 22)),
    Sum.inr (Sum.inl (128, 5)),
    Sum.inr (Sum.inl (26, 21)),
    Sum.inr (Sum.inl (6, 55)),
    Sum.inr (Sum.inl (26, 29)),
    Sum.inr (Sum.inl (26, 17)),
    Sum.inr (Sum.inl (133, 56)),
    Sum.inr (Sum.inl (126, 55)),
    Sum.inr (Sum.inl (128, 21)),
    Sum.inr (Sum.inl (132, 23)),
    Sum.inr (Sum.inl (128, 13)),
    Sum.inr (Sum.inl (133, 6)),
    Sum.inr (Sum.inl (126, 23)),
    Sum.inr (Sum.inl (132, 41)),
    Sum.inr (Sum.inl (6, 23)),
    Sum.inr (Sum.inl (6, 39)),
    Sum.inr (Sum.inl (26, 25)),
    Sum.inr (Sum.inl (6, 7)),
    Sum.inr (Sum.inl (128, 29)),
    Sum.inr (Sum.inl (126, 54)),
    Sum.inr (Sum.inl (132, 8)),
    Sum.inr (Sum.inl (133, 41)),
    Sum.inr (Sum.inl (210, 26)),
    Sum.inr (Sum.inl (204, 7)),
    Sum.inr (Sum.inl (147, 23)),
    Sum.inr (Sum.inl (170, 55)),
    Sum.inr (Sum.inl (35, 37)),
    Sum.inr (Sum.inl (15, 59)),
    Sum.inr (Sum.inl (35, 45)),
    Sum.inr (Sum.inl (35, 33)),
    Sum.inr (Sum.inl (210, 53)),
    Sum.inr (Sum.inl (147, 5)),
    Sum.inr (Sum.inl (170, 39)),
    Sum.inr (Sum.inl (204, 37)),
    Sum.inr (Sum.inl (170, 37)),
    Sum.inr (Sum.inl (210, 33)),
    Sum.inr (Sum.inl (147, 7)),
    Sum.inr (Sum.inl (204, 58)),
    Sum.inr (Sum.inl (15, 27)),
    Sum.inr (Sum.inl (15, 43)),
    Sum.inr (Sum.inl (35, 41)),
    Sum.inr (Sum.inl (15, 11)),
    Sum.inr (Sum.inl (170, 53)),
    Sum.inr (Sum.inl (147, 21)),
    Sum.inr (Sum.inl (204, 24)),
    Sum.inr (Sum.inl (210, 14)),
    Sum.inr (Sum.inl (196, 20)),
    Sum.inr (Sum.inl (195, 1)),
    Sum.inr (Sum.inl (144, 6)),
    Sum.inr (Sum.inl (167, 38)),
    Sum.inr (Sum.inl (32, 4)),
    Sum.inr (Sum.inl (12, 50)),
    Sum.inr (Sum.inl (32, 12)),
    Sum.inr (Sum.inl (32, 0))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock079Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨20224 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock079InputMaskData : ℕ :=
  sixthHex% [
    "98c34690c3469ccb46d4cb46e43b46c43346f43346943b469a7b45ac7345",
    "b77b45c17345a6bb45b8bb459fbb45c1bb45bedb4594d345abdb45c1d345",
    "82eb4580eb4583eb45c1eb458dfb4585fb4589f345c1f345f10345d10b45",
    "e10b45810345ea9b44dc9344c79b44b19344d65b44c85b44ef5b44b15b44",
    "ce3b44e43344db3b44b13344f20344f00344f30344b10344fd1b44f51b44",
    "f91344b1134481eb44a1e34491e344f1eb448f1343b91b43a21343d41b43",
    "b3db43addb438adb43d4db43abbb4381b343bebb43d4b343978343958343",
    "968343d483439893439093439c9b43d49b43e46b43c46343f46343946b43",
    "fff342c9fb42d2f342a4fb42c33b42dd3b42fa3b42a43b42db5b42f15342",
    "ce5b42a45342e76b42e56b42e66b42a46b42e87342e07342ec7b42a47b42",
    "948342b48b42848b42e48342eacb41dcc341c7cb41b1c341d60341c80341",
    "ef0341b10341ce6b41e46341db6b41b16341f25b41f05b41f35b41b15b41",
    "fd4b41f54b41f94341b1434181bb41a1b34191b341f1bb41da2b40ec2340",
    "f72b40812340e6e340f8e340dfe34081e340fe8b40d48340eb8b40818340",
    "c2b340c0b340c3b34081b340cdab40c5ab40c9a34081a340b15340915b40",
    "a15b40c15340e3c32fd5cb2fcecb2fb8c32fdf032fc1032fe6032fb8032f",
    "c76b2fed6b2fd2632fb8632ffb5b2ff9532ffa5b2fb8532ff44b2ffc4b2f",
    "f04b2fb84b2f88bb2fa8b32f98b32ff8bb2f922b2ea4232ebf232ec92b2e",
    "aeeb2eb0eb2e97eb2ec9eb2eb6832e9c832ea38b2ec98b2e8abb2e88b32e",
    "8bbb2ec9b32e85a32e8da32e81a32ec9a32ef95b2ed9532ee9532e895b2e",
    "b91b2d8f132d94132de21b2d85db2d9bdb2dbcdb2de2db2d9dbb2db7bb2d",
    "88b32de2b32da1832da38b2da0832de28b2dae932da6932daa932de2932d",
    "d26b2df2632dc2632da26b2d88f32cbefb2ca5fb2cd3f32cb4332caa332c",
    "8d332cd3332cac532c86532cb95b2cd35b2c90632c926b2c91632cd36b2c",
    "9f7b2c977b2c9b7b2cd37b2ce38b2cc3832cf3832c938b2c93732ba57b2b",
    "be7b2bc8732bafbb2bb1bb2b96bb2bc8bb2b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock079InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock079InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock079OutputMaskData : ℕ :=
  sixthHex% [
    "482512402d12086519756d127982770c8b4d2a186d2a115c1d206e4b215f",
    "37fa7f14fb450b6c2b206c20326c2b6c6c2b28c95f651a7f2c886e145b45",
    "14f95f242b4503627f46b06e1524201d2c2055642b286c20248345518a7f",
    "77195f77106e78fb4f2efa7e52215e7120646eb70a45b70157b70a09b70a",
    "4d127e00c15e49534f71806400627e30b06417f95e522b4f70ff0178f701",
    "30bf0a4db70130186445115e63827e638b4fe8d686bed7b7c20c97e10dad",
    "8fdac3a4dac8b6dac3e8dac3ac7fb7e1ac97a83e8690edade10fb7d1ddad",
    "f69497b34686e0d2c8e8dac8a092c3dd9ac8d175ada47c9782efb782e686",
    "8d0da7db0c96a7d7b684d68cea01e2c101e9d301e28d01e2c9a4968477b6",
    "cde5a7f5368cf59496c5468ce20fb6a7dda78509e98d01e9c549e2b841e9",
    "c5ee8cb0e7b6967496967da7d00c95860da4fad684d9d7beb700d09c00db",
    "8e00d0d000d0e5e5a4a83684e1a495d977bed9d5a4e907bece4e848b9c95",
    "d808dbd000db9848d0e540db98efbeede684cb75a4cb7c95c0d7bf96d68e",
    "ea0daec90c94a7dbfa8cdbf19edbfac0dbfaf53e8eb8edaef17fbfc9ac94",
    "b84e8e889c94afd5aeea07bfc8d3f1c0dbf18893faf59bf1f974948c7dae",
    "aaee8eaae7bf314c41674d706ad65049d76a2700040c000f1e0004400004",
    "75e57049765000e44149776a49d57008476a5e4e506adc4148080f40000f",
    "79080404000f08ef6a7de6505b75705b7c41324c40644d7169d6514ad76b",
    "2400050f000e1d000543000576e5714a765103e4404a776b3b95717a076b",
    "2c0e51189c404b080e43000e7a080507000e7aaf6b0fa651293571293c40",
    "3144436745726ade5249df682708060c080d1e080640080604ad72383e52",
    "71ac43383f6849dd72084f685e46526ad44348000d40080d79000604080d",
    "79a7680cae522a3d722a34434744491145781cde583fdf6251080c7a0807",
    "68080c36080c72ad784e3e5807ac494e3f624e9d780f0f625906586d9449",
    "3e00073608070f000c7208077ee7620bee582d7d782d7449fc60baaa618b",
    "a7faab84fb919b6cffb06cf4a26cfffc6cff"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock079OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock079OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock079InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock079InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock079InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock079OutputNumeratorData : ℕ :=
  sixthHex% [
    "8618617e185f85f85f96175d85f7e17df8617df7df7e17e185f7e196175d",
    "8617df85f85f7df7df7e185f7df7e16e18e385f86186185f7e18617df85f",
    "7df85f6e18e386185f7e18617e18617df7e186185f95f75d85f8617df7e1",
    "85f7df7df85f8617e195f75d86185f85f7df85f7df7df7e185f86195f75d",
    "7e17df85f8617df7e17df7e17e18616e18e386185f8617e186185f8617e1",
    "85f86195f75d85f86185f8617df7e186185f85f7df95f75d86185f7df85f",
    "7df7e18617e17df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock079OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock079OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block079_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock079Input a) =
      generatedSixthXiShortBlock079InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock079Output a) =
      generatedSixthXiShortBlock079OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock079Input a) =
      generatedSixthXiShortBlock079InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock079Output a) =
      generatedSixthXiShortBlock079OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block079_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock079InputMask a) =
      generatedSixthXiShortBlock079OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock079InputMask a)) *
      generatedSixthXiShortBlock079InputNumerator a =
        generatedSixthXiShortBlock079OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block079_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock079Input a
    let y := generatedSixthXiShortBlock079Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block079_cache a
  have hs := generatedSixth_xi_short_block079_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block079_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock079Input a
    let y := generatedSixthXiShortBlock079Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block079_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block079_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock079Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block079_certificate a).1
    (generatedSixth_xi_short_block079_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
