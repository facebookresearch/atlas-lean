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
def generatedSixthXiShortBlock075Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (215, 13)),
    Sum.inr (Sum.inl (209, 19)),
    Sum.inr (Sum.inl (152, 56)),
    Sum.inr (Sum.inl (175, 33)),
    Sum.inr (Sum.inl (40, 51)),
    Sum.inr (Sum.inl (20, 61)),
    Sum.inr (Sum.inl (40, 57)),
    Sum.inr (Sum.inl (40, 59)),
    Sum.inr (Sum.inl (215, 28)),
    Sum.inr (Sum.inl (152, 40)),
    Sum.inr (Sum.inl (175, 49)),
    Sum.inr (Sum.inl (209, 50)),
    Sum.inr (Sum.inl (175, 51)),
    Sum.inr (Sum.inl (215, 12)),
    Sum.inr (Sum.inl (152, 60)),
    Sum.inr (Sum.inl (209, 51)),
    Sum.inr (Sum.inl (20, 29)),
    Sum.inr (Sum.inl (20, 45)),
    Sum.inr (Sum.inl (40, 49)),
    Sum.inr (Sum.inl (20, 13)),
    Sum.inr (Sum.inl (175, 35)),
    Sum.inr (Sum.inl (152, 44)),
    Sum.inr (Sum.inl (209, 18)),
    Sum.inr (Sum.inl (215, 29)),
    Sum.inr (Sum.inl (104, 35)),
    Sum.inr (Sum.inl (103, 44)),
    Sum.inr (Sum.inl (97, 30)),
    Sum.inr (Sum.inl (99, 33)),
    Sum.inr (Sum.inl (24, 51)),
    Sum.inr (Sum.inl (4, 61)),
    Sum.inr (Sum.inl (24, 57)),
    Sum.inr (Sum.inl (24, 59)),
    Sum.inr (Sum.inl (104, 60)),
    Sum.inr (Sum.inl (97, 12)),
    Sum.inr (Sum.inl (99, 51)),
    Sum.inr (Sum.inl (103, 51)),
    Sum.inr (Sum.inl (99, 49)),
    Sum.inr (Sum.inl (104, 24)),
    Sum.inr (Sum.inl (97, 35)),
    Sum.inr (Sum.inl (103, 14)),
    Sum.inr (Sum.inl (4, 29)),
    Sum.inr (Sum.inl (4, 45)),
    Sum.inr (Sum.inl (24, 49)),
    Sum.inr (Sum.inl (4, 13)),
    Sum.inr (Sum.inl (99, 35)),
    Sum.inr (Sum.inl (97, 49)),
    Sum.inr (Sum.inl (103, 17)),
    Sum.inr (Sum.inl (104, 7)),
    Sum.inr (Sum.inl (179, 51)),
    Sum.inr (Sum.inl (178, 60)),
    Sum.inr (Sum.inl (142, 51)),
    Sum.inr (Sum.inl (165, 12)),
    Sum.inr (Sum.inl (30, 51)),
    Sum.inr (Sum.inl (10, 61)),
    Sum.inr (Sum.inl (30, 57)),
    Sum.inr (Sum.inl (30, 59)),
    Sum.inr (Sum.inl (179, 28)),
    Sum.inr (Sum.inl (142, 17)),
    Sum.inr (Sum.inl (165, 46)),
    Sum.inr (Sum.inl (178, 35)),
    Sum.inr (Sum.inl (165, 14)),
    Sum.inr (Sum.inl (179, 34)),
    Sum.inr (Sum.inl (142, 44)),
    Sum.inr (Sum.inl (178, 11)),
    Sum.inr (Sum.inl (10, 29)),
    Sum.inr (Sum.inl (10, 45)),
    Sum.inr (Sum.inl (30, 49)),
    Sum.inr (Sum.inl (10, 13)),
    Sum.inr (Sum.inl (165, 44)),
    Sum.inr (Sum.inl (142, 14)),
    Sum.inr (Sum.inl (178, 20)),
    Sum.inr (Sum.inl (179, 13)),
    Sum.inr (Sum.inr (411, 13)),
    Sum.inr (Sum.inr (474, 22)),
    Sum.inr (Sum.inr (282, 9)),
    Sum.inr (Sum.inr (336, 3)),
    Sum.inr (Sum.inr (133, 6)),
    Sum.inr (Sum.inr (142, 5)),
    Sum.inr (Sum.inr (133, 4)),
    Sum.inr (Sum.inr (133, 18)),
    Sum.inr (Sum.inr (411, 23)),
    Sum.inr (Sum.inr (282, 2)),
    Sum.inr (Sum.inr (336, 10)),
    Sum.inr (Sum.inr (474, 15)),
    Sum.inr (Sum.inr (336, 12)),
    Sum.inr (Sum.inr (411, 0)),
    Sum.inr (Sum.inr (282, 21)),
    Sum.inr (Sum.inr (474, 11)),
    Sum.inr (Sum.inr (142, 16)),
    Sum.inr (Sum.inr (142, 17)),
    Sum.inr (Sum.inr (133, 7)),
    Sum.inr (Sum.inr (142, 19)),
    Sum.inr (Sum.inr (336, 20)),
    Sum.inr (Sum.inr (282, 14)),
    Sum.inr (Sum.inr (474, 1)),
    Sum.inr (Sum.inr (411, 8)),
    Sum.inr (Sum.inr (464, 23)),
    Sum.inr (Sum.inr (401, 15)),
    Sum.inr (Sum.inr (337, 2)),
    Sum.inr (Sum.inr (283, 10)),
    Sum.inr (Sum.inr (206, 6)),
    Sum.inr (Sum.inr (197, 5)),
    Sum.inr (Sum.inr (206, 4)),
    Sum.inr (Sum.inr (206, 18)),
    Sum.inr (Sum.inr (464, 13)),
    Sum.inr (Sum.inr (337, 9)),
    Sum.inr (Sum.inr (283, 3)),
    Sum.inr (Sum.inr (401, 22)),
    Sum.inr (Sum.inr (283, 20)),
    Sum.inr (Sum.inr (464, 8)),
    Sum.inr (Sum.inr (337, 14)),
    Sum.inr (Sum.inr (401, 1)),
    Sum.inr (Sum.inr (197, 16)),
    Sum.inr (Sum.inr (197, 17)),
    Sum.inr (Sum.inr (206, 7)),
    Sum.inr (Sum.inr (197, 19)),
    Sum.inr (Sum.inr (283, 12)),
    Sum.inr (Sum.inr (337, 21)),
    Sum.inr (Sum.inr (401, 11)),
    Sum.inr (Sum.inr (464, 0)),
    Sum.inr (Sum.inr (338, 0)),
    Sum.inr (Sum.inr (275, 11)),
    Sum.inr (Sum.inr (467, 21)),
    Sum.inr (Sum.inr (409, 12)),
    Sum.inr (Sum.inr (76, 6)),
    Sum.inr (Sum.inr (71, 5)),
    Sum.inr (Sum.inr (76, 4)),
    Sum.inr (Sum.inr (76, 18)),
    Sum.inr (Sum.inr (338, 8)),
    Sum.inr (Sum.inr (467, 14)),
    Sum.inr (Sum.inr (409, 20)),
    Sum.inr (Sum.inr (275, 1)),
    Sum.inr (Sum.inr (409, 3)),
    Sum.inr (Sum.inr (338, 13)),
    Sum.inr (Sum.inr (467, 9)),
    Sum.inr (Sum.inr (275, 22)),
    Sum.inr (Sum.inr (71, 16)),
    Sum.inr (Sum.inr (71, 17)),
    Sum.inr (Sum.inr (76, 7)),
    Sum.inr (Sum.inr (71, 19)),
    Sum.inr (Sum.inr (409, 10)),
    Sum.inr (Sum.inr (467, 2)),
    Sum.inr (Sum.inr (275, 15)),
    Sum.inr (Sum.inr (338, 23)),
    Sum.inr (Sum.inr (274, 8)),
    Sum.inr (Sum.inr (339, 1)),
    Sum.inr (Sum.inr (403, 14)),
    Sum.inr (Sum.inr (473, 20)),
    Sum.inr (Sum.inr (12, 6)),
    Sum.inr (Sum.inr (7, 5)),
    Sum.inr (Sum.inr (12, 4)),
    Sum.inr (Sum.inr (12, 18)),
    Sum.inr (Sum.inr (274, 0)),
    Sum.inr (Sum.inr (403, 21)),
    Sum.inr (Sum.inr (473, 12)),
    Sum.inr (Sum.inr (339, 11)),
    Sum.inr (Sum.inr (473, 10)),
    Sum.inr (Sum.inr (274, 23)),
    Sum.inr (Sum.inr (403, 2)),
    Sum.inr (Sum.inr (339, 15)),
    Sum.inr (Sum.inr (7, 16)),
    Sum.inr (Sum.inr (7, 17)),
    Sum.inr (Sum.inr (12, 7)),
    Sum.inr (Sum.inr (7, 19)),
    Sum.inr (Sum.inr (473, 3)),
    Sum.inr (Sum.inr (403, 9)),
    Sum.inr (Sum.inr (339, 22)),
    Sum.inr (Sum.inr (274, 13)),
    Sum.inr (Sum.inl (179, 63)),
    Sum.inr (Sum.inl (178, 63)),
    Sum.inr (Sum.inl (142, 63)),
    Sum.inr (Sum.inl (165, 0)),
    Sum.inr (Sum.inl (30, 61)),
    Sum.inr (Sum.inl (10, 15)),
    Sum.inr (Sum.inl (30, 55)),
    Sum.inr (Sum.inl (30, 53)),
    Sum.inr (Sum.inl (179, 16)),
    Sum.inr (Sum.inl (142, 29)),
    Sum.inr (Sum.inl (165, 34)),
    Sum.inr (Sum.inl (178, 32)),
    Sum.inr (Sum.inl (165, 2)),
    Sum.inr (Sum.inl (179, 46)),
    Sum.inr (Sum.inl (142, 32)),
    Sum.inr (Sum.inl (178, 8)),
    Sum.inr (Sum.inl (10, 47)),
    Sum.inr (Sum.inl (10, 31)),
    Sum.inr (Sum.inl (30, 63)),
    Sum.inr (Sum.inl (10, 63)),
    Sum.inr (Sum.inl (165, 32)),
    Sum.inr (Sum.inl (142, 2)),
    Sum.inr (Sum.inl (178, 23)),
    Sum.inr (Sum.inl (179, 1)),
    Sum.inr (Sum.inl (104, 32)),
    Sum.inr (Sum.inl (103, 32)),
    Sum.inr (Sum.inl (97, 18)),
    Sum.inr (Sum.inl (99, 45)),
    Sum.inr (Sum.inl (24, 61)),
    Sum.inr (Sum.inl (4, 15)),
    Sum.inr (Sum.inl (24, 55)),
    Sum.inr (Sum.inl (24, 53)),
    Sum.inr (Sum.inl (104, 63)),
    Sum.inr (Sum.inl (97, 0)),
    Sum.inr (Sum.inl (99, 63)),
    Sum.inr (Sum.inl (103, 63)),
    Sum.inr (Sum.inl (99, 61)),
    Sum.inr (Sum.inl (104, 27)),
    Sum.inr (Sum.inl (97, 47)),
    Sum.inr (Sum.inl (103, 2)),
    Sum.inr (Sum.inl (4, 47)),
    Sum.inr (Sum.inl (4, 31)),
    Sum.inr (Sum.inl (24, 63)),
    Sum.inr (Sum.inl (4, 63)),
    Sum.inr (Sum.inl (99, 47)),
    Sum.inr (Sum.inl (97, 61)),
    Sum.inr (Sum.inl (103, 29)),
    Sum.inr (Sum.inl (104, 4)),
    Sum.inr (Sum.inl (215, 1)),
    Sum.inr (Sum.inl (209, 31)),
    Sum.inr (Sum.inl (152, 59)),
    Sum.inr (Sum.inl (175, 45)),
    Sum.inr (Sum.inl (40, 61)),
    Sum.inr (Sum.inl (20, 15)),
    Sum.inr (Sum.inl (40, 55)),
    Sum.inr (Sum.inl (40, 53)),
    Sum.inr (Sum.inl (215, 16)),
    Sum.inr (Sum.inl (152, 43)),
    Sum.inr (Sum.inl (175, 61)),
    Sum.inr (Sum.inl (209, 62)),
    Sum.inr (Sum.inl (175, 63)),
    Sum.inr (Sum.inl (215, 0)),
    Sum.inr (Sum.inl (152, 63)),
    Sum.inr (Sum.inl (209, 63)),
    Sum.inr (Sum.inl (20, 47)),
    Sum.inr (Sum.inl (20, 31)),
    Sum.inr (Sum.inl (40, 63)),
    Sum.inr (Sum.inl (20, 63)),
    Sum.inr (Sum.inl (175, 47)),
    Sum.inr (Sum.inl (152, 47)),
    Sum.inr (Sum.inl (209, 30)),
    Sum.inr (Sum.inl (215, 17)),
    Sum.inr (Sum.inl (71, 13)),
    Sum.inr (Sum.inl (70, 19)),
    Sum.inr (Sum.inl (64, 50)),
    Sum.inr (Sum.inl (66, 36)),
    Sum.inr (Sum.inl (22, 51)),
    Sum.inr (Sum.inl (2, 61)),
    Sum.inr (Sum.inl (22, 57)),
    Sum.inr (Sum.inl (22, 59)),
    Sum.inr (Sum.inl (71, 28)),
    Sum.inr (Sum.inl (64, 18)),
    Sum.inr (Sum.inl (66, 52)),
    Sum.inr (Sum.inl (70, 50)),
    Sum.inr (Sum.inl (66, 44)),
    Sum.inr (Sum.inl (71, 34)),
    Sum.inr (Sum.inl (64, 19)),
    Sum.inr (Sum.inl (70, 45))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock075Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨19200 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock075InputMaskData : ℕ :=
  sixthHex% [
    "ae52ab845aabbb52abd15aab9262ab906aab9362abd16aab9d7aab9572ab",
    "997aabd172abe182abc18aabf182ab918aab9b12aaad12aab612aac012aa",
    "a7daaab9daaa9edaaac0daaabfbaaa95b2aaaabaaac0b2aa8382aa818aaa",
    "8282aac08aaa8c92aa849aaa8892aac09aaaf062aad06aaae062aa806aaa",
    "8f22a9b922a9a222a9d422a9b3eaa9adeaa98aeaa9d4eaa9ab82a9818aa9",
    "be82a9d48aa997baa995b2a996baa9d4b2a998a2a990aaa99ca2a9d4aaa9",
    "e452a9c45aa9f452a9945aa9decaa8e8caa8f3caa885caa8e202a8fc02a8",
    "db02a88502a8fa6aa8d062a8ef6aa88562a8c65aa8c452a8c75aa88552a8",
    "c94aa8c142a8cd4aa88542a8b5b2a895baa8a5b2a8c5baa88a32a7bc32a7",
    "a732a7d132a7b6faa7a8faa78ffaa7d1faa7ae92a7849aa7bb92a7d19aa7",
    "92a2a790aaa793a2a7d1aaa79dbaa795b2a799baa7d1b2a7e142a7c14aa7",
    "f142a7914aa79bdaa6addaa6b6daa6c0daa6a712a6b912a69e12a6c012a6",
    "bf7aa69572a6aa7aa6c072a68342a6814aa68242a6c04aa68c52a6845aa6",
    "8852a6c05aa6f0a2a6d0aaa6e0a2a680aaa68feaa5b9eaa5a2eaa5d4eaa5",
    "b322a5ad22a58a22a5d422a5ab42a5814aa5be42a5d44aa5977aa59572a5",
    "967aa5d472a59862a5906aa59c62a5d46aa5e492a5c49aa5f492a5949aa5",
    "de02a4e802a4f302a48502a4e2caa4fccaa4dbcaa485caa4faaaa4d0a2a4",
    "efaaa485a2a4c69aa4c492a4c79aa48592a4c98aa4c182a4cd8aa48582a4",
    "b572a4957aa4a572a4c57aa49a82a3ac82a3b782a3c182a3a642a3b842a3",
    "9f42a3c142a3be22a3942aa3ab22a3c12aa38212a3801aa38312a3c11aa3",
    "8d0aa38502a3890aa3c102a3f1faa3d1f2a3e1faa381f2a3cb6aa2fd6aa2",
    "e66aa2906aa2f7aaa2e9aaa2ceaaa290aaa2efcaa2c5c2a2facaa290c2a2",
    "d3f2a2d1faa2d2f2a290faa2dce2a2d4eaa2d8e2a290eaa2a01aa28012a2",
    "b01aa2d012a2df5aa1e95aa1f25aa1845aa1e39aa1fd9aa1da9aa1849aa1",
    "fbf2a1d1faa1eef2a184faa1c7caa1c5c2a1c6caa184c2a1c8d2a1c0daa1",
    "ccd2a184daa1b42aa19422a1a42aa1c422a1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock075InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock075InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock075OutputMaskData : ℕ :=
  sixthHex% [
    "3222a07ff1803663910eb0ba0e12a04f80ba1989802d1b917e8fdf07c7df",
    "4f8fd443c7df4f28ba3a21806df2a06dfb9104c2a12383902e18b07c598a",
    "63cee448ceef5acee404cee4406b900db8b0442aa17cf98a0d1b904c898a",
    "1a80b02e12a10cc6ef758eef3dc6e4318eef4c218a3928b06efb906ef2a1",
    "3f18b318598215c2a24783985814f67314fd6114f63f14f60af1824722a2",
    "0eb0b3366398478182061398501aa26488b3371cfd4e54fd061cf60a54fd",
    "77fb9802f2a25521825528b33851881f10b9128b9940caa35f5dcd745dc6",
    "665dcd385dcd0db8b9406b9909f988312aa33188b9701aa3261399128188",
    "3055c6491dc60155cd0d1dc601f2a374fb992328b9232188803c42a77d73",
    "aae653f8a769e73007cc300cde3007803007b5d573f80653b19442894769",
    "89e573c877699e7e53aaec42f9780c80300cc87807c4300cc8df69bdd653",
    "ea0573ea0c42f27572d53443d8af638aee59957937be793cac7937f27937",
    "c79c438a4f63c3dd72fb0e598aec43cb7e599d7763a9e5728b313cf2793c",
    "ba3137b6793ccbd659bedf63e90c43e90572c9af60eeee51e37571b1344b",
    "aea32585a32e97a325c9a3258d0651c0d571894760b1944bc0765181e44b",
    "d7ed71e37f60b0eb2ec9a32e81eb258da32ef00c4b850571d2d651d2df60",
    "cee65be9a76ae43c4ab67d70a9ea1e82ea1590ea1eceea1e8a4f6ac79c4a",
    "8e0e5bb6dd70b67f6af7ed70a1e44a95765bb7a215ceea1586a21e8aea15",
    "860570f30c4aa4df6aa4d65b3c59881b18b916839944c2a32a15cd0115c6",
    "1315cd4d15cd09b0b94463990df1883522a33580b97412a3221b99168988",
    "451dc63c55c6741dcd7855c605faa370f3992720b92729883b10b31c5182",
    "11caa2438b982d5cf6065cfd145cf64a5cf60ef982432aa20ab8b3326b98",
    "438982021b985412a26080b34254fd3b1cfd7354f67f1cfd73f39806faa2",
    "5129825120b300caa1278b902a10b078518a1686e43d86ef2f86e47186e4",
    "44639009b0b04022a178f18a09139048818a1e88b02a1aa1798eef00c6ef",
    "488ee444c6ef48298a3d20b06af3906afaa1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock075OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock075OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock075InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock075InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock075InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock075OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e18617df96175d7df8617df7df85f7e17e17e1",
    "86186196175d85f7e185f7e185f7e185f7e18617df96175d8617df7df7df",
    "85f7e185f85f85f7df95f75d86185f7df85f7df7e18617e185f86195f75d",
    "85f86185f8617df7e186185f7e18616e18e386185f8617e186185f8617e1",
    "7e17df6e18e385f8617e17df86185f86185f7df8616df8e37df861861861",
    "7e185f7e17e17df7df6df8e37e185f7e185f7e185f7e185f7df8616df8e3",
    "8617df8618617e185f85f85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock075OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock075OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block075_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock075Input a) =
      generatedSixthXiShortBlock075InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock075Output a) =
      generatedSixthXiShortBlock075OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock075Input a) =
      generatedSixthXiShortBlock075InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock075Output a) =
      generatedSixthXiShortBlock075OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block075_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock075InputMask a) =
      generatedSixthXiShortBlock075OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock075InputMask a)) *
      generatedSixthXiShortBlock075InputNumerator a =
        generatedSixthXiShortBlock075OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block075_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock075Input a
    let y := generatedSixthXiShortBlock075Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block075_cache a
  have hs := generatedSixth_xi_short_block075_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block075_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock075Input a
    let y := generatedSixthXiShortBlock075Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block075_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block075_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock075Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block075_certificate a).1
    (generatedSixth_xi_short_block075_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
