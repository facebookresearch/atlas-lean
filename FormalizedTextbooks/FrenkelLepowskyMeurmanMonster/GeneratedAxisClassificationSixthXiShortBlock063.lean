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
def generatedSixthXiShortBlock063Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (71, 15)),
    Sum.inr (Sum.inl (70, 15)),
    Sum.inr (Sum.inl (64, 15)),
    Sum.inr (Sum.inl (66, 3)),
    Sum.inr (Sum.inl (22, 13)),
    Sum.inr (Sum.inl (2, 3)),
    Sum.inr (Sum.inl (22, 7)),
    Sum.inr (Sum.inl (22, 5)),
    Sum.inr (Sum.inl (71, 30)),
    Sum.inr (Sum.inl (64, 47)),
    Sum.inr (Sum.inl (66, 19)),
    Sum.inr (Sum.inl (70, 46)),
    Sum.inr (Sum.inl (66, 11)),
    Sum.inr (Sum.inl (71, 32)),
    Sum.inr (Sum.inl (64, 46)),
    Sum.inr (Sum.inl (70, 49)),
    Sum.inr (Sum.inl (2, 35)),
    Sum.inr (Sum.inl (2, 19)),
    Sum.inr (Sum.inl (22, 15)),
    Sum.inr (Sum.inl (2, 51)),
    Sum.inr (Sum.inl (66, 27)),
    Sum.inr (Sum.inl (64, 14)),
    Sum.inr (Sum.inl (70, 16)),
    Sum.inr (Sum.inl (71, 49)),
    Sum.inr (Sum.inl (179, 61)),
    Sum.inr (Sum.inl (178, 40)),
    Sum.inr (Sum.inl (142, 62)),
    Sum.inr (Sum.inl (165, 35)),
    Sum.inr (Sum.inl (30, 3)),
    Sum.inr (Sum.inl (10, 49)),
    Sum.inr (Sum.inl (30, 9)),
    Sum.inr (Sum.inl (30, 11)),
    Sum.inr (Sum.inl (179, 18)),
    Sum.inr (Sum.inl (142, 28)),
    Sum.inr (Sum.inl (165, 1)),
    Sum.inr (Sum.inl (178, 55)),
    Sum.inr (Sum.inl (165, 33)),
    Sum.inr (Sum.inl (179, 44)),
    Sum.inr (Sum.inl (142, 33)),
    Sum.inr (Sum.inl (178, 31)),
    Sum.inr (Sum.inl (10, 17)),
    Sum.inr (Sum.inl (10, 33)),
    Sum.inr (Sum.inl (30, 1)),
    Sum.inr (Sum.inl (10, 1)),
    Sum.inr (Sum.inl (165, 3)),
    Sum.inr (Sum.inl (142, 3)),
    Sum.inr (Sum.inl (178, 0)),
    Sum.inr (Sum.inl (179, 3)),
    Sum.inr (Sum.inl (104, 56)),
    Sum.inr (Sum.inl (103, 45)),
    Sum.inr (Sum.inl (97, 50)),
    Sum.inr (Sum.inl (99, 31)),
    Sum.inr (Sum.inl (24, 13)),
    Sum.inr (Sum.inl (4, 3)),
    Sum.inr (Sum.inl (24, 7)),
    Sum.inr (Sum.inl (24, 5)),
    Sum.inr (Sum.inl (104, 39)),
    Sum.inr (Sum.inl (97, 32)),
    Sum.inr (Sum.inl (99, 13)),
    Sum.inr (Sum.inl (103, 50)),
    Sum.inr (Sum.inl (99, 15)),
    Sum.inr (Sum.inl (104, 3)),
    Sum.inr (Sum.inl (97, 15)),
    Sum.inr (Sum.inl (103, 15)),
    Sum.inr (Sum.inl (4, 35)),
    Sum.inr (Sum.inl (4, 19)),
    Sum.inr (Sum.inl (24, 15)),
    Sum.inr (Sum.inl (4, 51)),
    Sum.inr (Sum.inl (99, 29)),
    Sum.inr (Sum.inl (97, 29)),
    Sum.inr (Sum.inl (103, 16)),
    Sum.inr (Sum.inl (104, 28)),
    Sum.inr (Sum.inr (337, 23)),
    Sum.inr (Sum.inr (272, 15)),
    Sum.inr (Sum.inr (464, 2)),
    Sum.inr (Sum.inr (410, 10)),
    Sum.inr (Sum.inr (79, 6)),
    Sum.inr (Sum.inr (68, 5)),
    Sum.inr (Sum.inr (79, 4)),
    Sum.inr (Sum.inr (79, 18)),
    Sum.inr (Sum.inr (337, 13)),
    Sum.inr (Sum.inr (464, 9)),
    Sum.inr (Sum.inr (410, 3)),
    Sum.inr (Sum.inr (272, 22)),
    Sum.inr (Sum.inr (410, 20)),
    Sum.inr (Sum.inr (337, 8)),
    Sum.inr (Sum.inr (464, 14)),
    Sum.inr (Sum.inr (272, 1)),
    Sum.inr (Sum.inr (68, 16)),
    Sum.inr (Sum.inr (68, 17)),
    Sum.inr (Sum.inr (79, 7)),
    Sum.inr (Sum.inr (68, 19)),
    Sum.inr (Sum.inr (410, 12)),
    Sum.inr (Sum.inr (464, 21)),
    Sum.inr (Sum.inr (272, 11)),
    Sum.inr (Sum.inr (337, 0)),
    Sum.inr (Sum.inr (282, 13)),
    Sum.inr (Sum.inr (347, 22)),
    Sum.inr (Sum.inr (411, 9)),
    Sum.inr (Sum.inr (465, 3)),
    Sum.inr (Sum.inr (4, 6)),
    Sum.inr (Sum.inr (15, 5)),
    Sum.inr (Sum.inr (4, 4)),
    Sum.inr (Sum.inr (4, 18)),
    Sum.inr (Sum.inr (282, 23)),
    Sum.inr (Sum.inr (411, 2)),
    Sum.inr (Sum.inr (465, 10)),
    Sum.inr (Sum.inr (347, 15)),
    Sum.inr (Sum.inr (465, 12)),
    Sum.inr (Sum.inr (282, 0)),
    Sum.inr (Sum.inr (411, 21)),
    Sum.inr (Sum.inr (347, 11)),
    Sum.inr (Sum.inr (15, 16)),
    Sum.inr (Sum.inr (15, 17)),
    Sum.inr (Sum.inr (4, 7)),
    Sum.inr (Sum.inr (15, 19)),
    Sum.inr (Sum.inr (465, 20)),
    Sum.inr (Sum.inr (411, 14)),
    Sum.inr (Sum.inr (347, 1)),
    Sum.inr (Sum.inr (282, 8)),
    Sum.inr (Sum.inr (403, 8)),
    Sum.inr (Sum.inr (466, 1)),
    Sum.inr (Sum.inr (274, 14)),
    Sum.inr (Sum.inr (344, 20)),
    Sum.inr (Sum.inr (141, 6)),
    Sum.inr (Sum.inr (134, 5)),
    Sum.inr (Sum.inr (141, 4)),
    Sum.inr (Sum.inr (141, 18)),
    Sum.inr (Sum.inr (403, 0)),
    Sum.inr (Sum.inr (274, 21)),
    Sum.inr (Sum.inr (344, 12)),
    Sum.inr (Sum.inr (466, 11)),
    Sum.inr (Sum.inr (344, 10)),
    Sum.inr (Sum.inr (403, 23)),
    Sum.inr (Sum.inr (274, 2)),
    Sum.inr (Sum.inr (466, 15)),
    Sum.inr (Sum.inr (134, 16)),
    Sum.inr (Sum.inr (134, 17)),
    Sum.inr (Sum.inr (141, 7)),
    Sum.inr (Sum.inr (134, 19)),
    Sum.inr (Sum.inr (344, 3)),
    Sum.inr (Sum.inr (274, 9)),
    Sum.inr (Sum.inr (466, 22)),
    Sum.inr (Sum.inr (403, 13)),
    Sum.inr (Sum.inr (467, 0)),
    Sum.inr (Sum.inr (402, 11)),
    Sum.inr (Sum.inr (338, 21)),
    Sum.inr (Sum.inr (280, 12)),
    Sum.inr (Sum.inr (205, 6)),
    Sum.inr (Sum.inr (198, 5)),
    Sum.inr (Sum.inr (205, 4)),
    Sum.inr (Sum.inr (205, 18)),
    Sum.inr (Sum.inr (467, 8)),
    Sum.inr (Sum.inr (338, 14)),
    Sum.inr (Sum.inr (280, 20)),
    Sum.inr (Sum.inr (402, 1)),
    Sum.inr (Sum.inr (280, 3)),
    Sum.inr (Sum.inr (467, 13)),
    Sum.inr (Sum.inr (338, 9)),
    Sum.inr (Sum.inr (402, 22)),
    Sum.inr (Sum.inr (198, 16)),
    Sum.inr (Sum.inr (198, 17)),
    Sum.inr (Sum.inr (205, 7)),
    Sum.inr (Sum.inr (198, 19)),
    Sum.inr (Sum.inr (280, 10)),
    Sum.inr (Sum.inr (338, 2)),
    Sum.inr (Sum.inr (402, 15)),
    Sum.inr (Sum.inr (467, 23)),
    Sum.inr (Sum.inl (104, 59)),
    Sum.inr (Sum.inl (103, 33)),
    Sum.inr (Sum.inl (97, 62)),
    Sum.inr (Sum.inl (99, 19)),
    Sum.inr (Sum.inl (24, 3)),
    Sum.inr (Sum.inl (4, 49)),
    Sum.inr (Sum.inl (24, 9)),
    Sum.inr (Sum.inl (24, 11)),
    Sum.inr (Sum.inl (104, 36)),
    Sum.inr (Sum.inl (97, 44)),
    Sum.inr (Sum.inl (99, 1)),
    Sum.inr (Sum.inl (103, 62)),
    Sum.inr (Sum.inl (99, 3)),
    Sum.inr (Sum.inl (104, 0)),
    Sum.inr (Sum.inl (97, 3)),
    Sum.inr (Sum.inl (103, 3)),
    Sum.inr (Sum.inl (4, 17)),
    Sum.inr (Sum.inl (4, 33)),
    Sum.inr (Sum.inl (24, 1)),
    Sum.inr (Sum.inl (4, 1)),
    Sum.inr (Sum.inl (99, 17)),
    Sum.inr (Sum.inl (97, 17)),
    Sum.inr (Sum.inl (103, 28)),
    Sum.inr (Sum.inl (104, 31)),
    Sum.inr (Sum.inl (179, 49)),
    Sum.inr (Sum.inl (178, 43)),
    Sum.inr (Sum.inl (142, 50)),
    Sum.inr (Sum.inl (165, 47)),
    Sum.inr (Sum.inl (30, 13)),
    Sum.inr (Sum.inl (10, 3)),
    Sum.inr (Sum.inl (30, 7)),
    Sum.inr (Sum.inl (30, 5)),
    Sum.inr (Sum.inl (179, 30)),
    Sum.inr (Sum.inl (142, 16)),
    Sum.inr (Sum.inl (165, 13)),
    Sum.inr (Sum.inl (178, 52)),
    Sum.inr (Sum.inl (165, 45)),
    Sum.inr (Sum.inl (179, 32)),
    Sum.inr (Sum.inl (142, 45)),
    Sum.inr (Sum.inl (178, 28)),
    Sum.inr (Sum.inl (10, 35)),
    Sum.inr (Sum.inl (10, 19)),
    Sum.inr (Sum.inl (30, 15)),
    Sum.inr (Sum.inl (10, 51)),
    Sum.inr (Sum.inl (165, 15)),
    Sum.inr (Sum.inl (142, 15)),
    Sum.inr (Sum.inl (178, 3)),
    Sum.inr (Sum.inl (179, 15)),
    Sum.inr (Sum.inl (71, 3)),
    Sum.inr (Sum.inl (70, 3)),
    Sum.inr (Sum.inl (64, 3)),
    Sum.inr (Sum.inl (66, 0)),
    Sum.inr (Sum.inl (22, 3)),
    Sum.inr (Sum.inl (2, 49)),
    Sum.inr (Sum.inl (22, 9)),
    Sum.inr (Sum.inl (22, 11)),
    Sum.inr (Sum.inl (71, 18)),
    Sum.inr (Sum.inl (64, 35)),
    Sum.inr (Sum.inl (66, 16)),
    Sum.inr (Sum.inl (70, 34)),
    Sum.inr (Sum.inl (66, 8)),
    Sum.inr (Sum.inl (71, 44)),
    Sum.inr (Sum.inl (64, 34)),
    Sum.inr (Sum.inl (70, 61)),
    Sum.inr (Sum.inl (2, 17)),
    Sum.inr (Sum.inl (2, 33)),
    Sum.inr (Sum.inl (22, 1)),
    Sum.inr (Sum.inl (2, 1)),
    Sum.inr (Sum.inl (66, 24)),
    Sum.inr (Sum.inl (64, 2)),
    Sum.inr (Sum.inl (70, 28)),
    Sum.inr (Sum.inl (71, 61)),
    Sum.inr (Sum.inl (215, 18)),
    Sum.inr (Sum.inl (209, 34)),
    Sum.inr (Sum.inl (152, 16)),
    Sum.inr (Sum.inl (175, 19)),
    Sum.inr (Sum.inl (40, 3)),
    Sum.inr (Sum.inl (20, 49)),
    Sum.inr (Sum.inl (40, 9)),
    Sum.inr (Sum.inl (40, 11)),
    Sum.inr (Sum.inl (215, 3)),
    Sum.inr (Sum.inl (152, 0)),
    Sum.inr (Sum.inl (175, 3)),
    Sum.inr (Sum.inl (209, 3)),
    Sum.inr (Sum.inl (175, 1)),
    Sum.inr (Sum.inl (215, 19)),
    Sum.inr (Sum.inl (152, 20)),
    Sum.inr (Sum.inl (209, 2))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock063Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨16128 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock063InputMaskData : ℕ :=
  sixthHex% [
    "db20bbf120bbce28bba428bbe718bbe510bbe610bba418bbe808bbe000bb",
    "ec08bba400bb94f8bbb4f8bb84f8bbe4f8bbfc60baca68bad160baa768ba",
    "c0a0badea0baf9a0baa7a0bad8c0baf2c0bacdc8baa7c8bae4f0bae6f8ba",
    "e5f8baa7f0baebe8bae3e0baefe8baa7e0ba9710bab710ba8710bae710ba",
    "d550b9e358b9f850b98e58b9e990b9f790b9d090b98e90b9f1f8b9dbf8b9",
    "e4f0b98ef0b9cdc8b9cfc0b9ccc0b98ec8b9c2d8b9cad0b9c6d8b98ed0b9",
    "be20b99e20b9ae20b9ce20b996b0b8a0b8b8bbb0b8cdb8b8aa70b8b470b8",
    "9370b8cd70b8b218b89818b8a710b8cd10b88e20b88c28b88f28b8cd20b8",
    "8138b88930b88538b8cd30b8fdc8b8ddc8b8edc8b88dc8b8d240b7e448b7",
    "ff40b78948b7ee80b7f080b7d780b78980b7f6e8b7dce8b7e3e0b789e0b7",
    "cad0b7c8d8b7cbd8b789d0b7c5c0b7cdc8b7c1c0b789c8b7b930b79930b7",
    "a930b7c930b7d1a0b6e7a8b6fca0b68aa8b6ed60b6f360b6d460b68a60b6",
    "f508b6df08b6e000b68a00b6c938b6cb30b6c830b68a38b6c620b6ce28b6",
    "c220b68a28b6bad8b69ad8b6aad8b6cad8b6f890b5ce98b5d590b5a398b5",
    "c450b5da50b5fd50b5a350b5dc30b5f630b5c938b5a338b5e000b5e208b5",
    "e108b5a300b5ef10b5e718b5eb10b5a318b593e8b5b3e8b583e8b5e3e8b5",
    "bb70b48d78b49670b4e078b487b0b499b0b4beb0b4e0b0b49fd0b4b5d0b4",
    "8ad8b4e0d8b4a3e8b4a1e0b4a2e0b4e0e8b4acf0b4a4f8b4a8f0b4e0f8b4",
    "d000b4f000b4c000b4a000b4d2f8b3e4f0b3fff8b389f0b3ee30b3f030b3",
    "d730b38930b3f650b3dc50b3e358b38958b3ca68b3c860b3cb60b38968b3",
    "c578b3cd70b3c178b38970b3b980b39980b3a980b3c980b39118b2a710b2",
    "bc18b2ca10b2add0b2b3d0b294d0b2cad0b2b5b0b29fb0b2a0b8b2cab8b2",
    "8980b28b88b28888b2ca80b28698b28e90b28298b2ca90b2fa68b2da68b2",
    "ea68b28a68b2b828b18e20b19528b1e320b184e0b19ae0b1bde0b1e3e0b1",
    "9c88b1b688b18980b1e380b1a0b8b1a2b0b1a1b0b1e3b8b1afa8b1a7a0b1",
    "aba8b1e3a0b1d358b1f358b1c358b1a358b1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock063InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock063InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock063OutputMaskData : ℕ :=
  sixthHex% [
    "b1b903788b07e1aa137898a466b9007f98a20b0b01422a147b6ef3efeef7",
    "6b6e47afeef07518a0318b0258b9054c2a12ff39179f2a00529802628ba3",
    "9bfd412bfdf00bfd45ebfd41a1aa02689806f1b912688ba262aa067b8ba4",
    "0f18074639156b7df2fffdf67b7d46bffdf6710ba63598045caa03483911",
    "c29884a28b936f39915f2a30a65cd2165c63365cd6d65cd5880b96413992",
    "d81886412a364b0b92522a3026b9936f988656dc61c25c6546dcd5825c65",
    "4caa35083997610b90759887828b32e298252f2a271f3986e64f64564fd5",
    "764f60964f63c81820012a24980b300139871f182306398172aa223b8b30",
    "16cfd7824fd306cf63c24fd418b9845c2a26351821218b393df63c5de52b",
    "905729a0448859326ae932dbc9326e29326d77652ebe572a27763ebe4489",
    "a0652db9448fcdd72c84f639bdb2de2932daadb26a6932ddb3c48df7572f",
    "9e65288af6382de53d4df62a804428b0578949216bf921dad9216f39216c",
    "67762fae442b37653fae578fa4762bbd5789c9c42a80e538ada1df3921db",
    "bda16b7921dbb7d78bf344299a762e8ee53b1044ae7057b9bde5bb8df61a",
    "7480f8c48049e480fc0480f84ed7bb87e5bf1ec4ab87f61b8dd7bf94f61d",
    "e065bea944ab90004c0480488000f84480488a7618cee5baa7d7bdb344ad",
    "50571830440ffdf60dcde5ac34934e8493ffa4934a44934e0ec40dc7f609",
    "5ed71dc7e5aad9c40ec0e5acb4760ffd571dd013fa4493fec0134e0493f9",
    "de65a99af60bf3c40ce75717c20b32a218256faa275fb981b2cf6302cfd2",
    "22cf67c2cf6388982041aa24d88b3041b9875f982346b981322a227b0b37",
    "424fd0d6cfd4524f6496cfd45839841caa26759821610b31821884e20b93",
    "2fb9911faa37f2dcd542dc6462dcd182dcd5c88b9601b99298988601aa36",
    "0b8b9212aa306639932f1881025c6696dc62125cd2d6dc650c2a3548b997",
    "218b90351882bfb917dfaa00121802220ba4cf7d467f7df75f7d42bf7d41",
    "e12a02281806b13912280ba2222a063b0ba44f980706b9123ffdf5ab7df1",
    "2ffd41eb7df6318ba67518041c2a0308b91"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock063OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock063OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock063InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock063InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock063InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock063OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df8617df7df85f7e17e17e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df8616df8e37df8618618617e185f7e17e17df7df6df8e37e185f7e185f",
    "7e185f7e185f85f86195f75d85f86185f8617df7e186185f85f7df95f75d",
    "86185f7df85f7df7e18617e17e17df6e18e385f8617e17df86185f86185f",
    "7e18616e18e386185f8617e186185f8617e186186196175d85f7e185f7e1",
    "85f7e185f7e18617df96175d8617df7df7df85f7e185f85f86186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock063OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock063OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block063_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock063Input a) =
      generatedSixthXiShortBlock063InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock063Output a) =
      generatedSixthXiShortBlock063OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock063Input a) =
      generatedSixthXiShortBlock063InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock063Output a) =
      generatedSixthXiShortBlock063OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block063_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock063InputMask a) =
      generatedSixthXiShortBlock063OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock063InputMask a)) *
      generatedSixthXiShortBlock063InputNumerator a =
        generatedSixthXiShortBlock063OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block063_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock063Input a
    let y := generatedSixthXiShortBlock063Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block063_cache a
  have hs := generatedSixth_xi_short_block063_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block063_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock063Input a
    let y := generatedSixthXiShortBlock063Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block063_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block063_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock063Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block063_certificate a).1
    (generatedSixth_xi_short_block063_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
