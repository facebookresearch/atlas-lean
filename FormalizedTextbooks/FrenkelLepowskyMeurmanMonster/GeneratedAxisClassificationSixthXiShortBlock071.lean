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
def generatedSixthXiShortBlock071Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (259, 0)),
    Sum.inr (Sum.inr (386, 9)),
    Sum.inr (Sum.inr (456, 20)),
    Sum.inr (Sum.inr (322, 15)),
    Sum.inr (Sum.inr (456, 3)),
    Sum.inr (Sum.inr (259, 23)),
    Sum.inr (Sum.inr (386, 14)),
    Sum.inr (Sum.inr (322, 11)),
    Sum.inr (Sum.inr (22, 16)),
    Sum.inr (Sum.inr (22, 17)),
    Sum.inr (Sum.inr (29, 6)),
    Sum.inr (Sum.inr (22, 19)),
    Sum.inr (Sum.inr (456, 10)),
    Sum.inr (Sum.inr (386, 21)),
    Sum.inr (Sum.inr (322, 1)),
    Sum.inr (Sum.inr (259, 13)),
    Sum.inr (Sum.inr (387, 0)),
    Sum.inr (Sum.inr (450, 15)),
    Sum.inr (Sum.inr (258, 9)),
    Sum.inr (Sum.inr (328, 20)),
    Sum.inr (Sum.inr (157, 7)),
    Sum.inr (Sum.inr (150, 5)),
    Sum.inr (Sum.inr (157, 18)),
    Sum.inr (Sum.inr (157, 4)),
    Sum.inr (Sum.inr (387, 8)),
    Sum.inr (Sum.inr (258, 2)),
    Sum.inr (Sum.inr (328, 12)),
    Sum.inr (Sum.inr (450, 22)),
    Sum.inr (Sum.inr (328, 10)),
    Sum.inr (Sum.inr (387, 13)),
    Sum.inr (Sum.inr (258, 21)),
    Sum.inr (Sum.inr (450, 1)),
    Sum.inr (Sum.inr (150, 16)),
    Sum.inr (Sum.inr (150, 17)),
    Sum.inr (Sum.inr (157, 6)),
    Sum.inr (Sum.inr (150, 19)),
    Sum.inr (Sum.inr (328, 3)),
    Sum.inr (Sum.inr (258, 14)),
    Sum.inr (Sum.inr (450, 11)),
    Sum.inr (Sum.inr (387, 23)),
    Sum.inr (Sum.inl (158, 57)),
    Sum.inr (Sum.inl (157, 41)),
    Sum.inr (Sum.inl (140, 11)),
    Sum.inr (Sum.inl (153, 9)),
    Sum.inr (Sum.inl (28, 52)),
    Sum.inr (Sum.inl (8, 12)),
    Sum.inr (Sum.inl (28, 60)),
    Sum.inr (Sum.inl (28, 62)),
    Sum.inr (Sum.inl (158, 22)),
    Sum.inr (Sum.inl (140, 36)),
    Sum.inr (Sum.inl (153, 43)),
    Sum.inr (Sum.inl (157, 11)),
    Sum.inr (Sum.inl (153, 11)),
    Sum.inr (Sum.inl (158, 2)),
    Sum.inr (Sum.inl (140, 25)),
    Sum.inr (Sum.inl (157, 54)),
    Sum.inr (Sum.inl (8, 44)),
    Sum.inr (Sum.inl (8, 28)),
    Sum.inr (Sum.inl (28, 54)),
    Sum.inr (Sum.inl (8, 60)),
    Sum.inr (Sum.inl (153, 41)),
    Sum.inr (Sum.inl (140, 54)),
    Sum.inr (Sum.inl (157, 20)),
    Sum.inr (Sum.inl (158, 45)),
    Sum.inr (Sum.inl (213, 43)),
    Sum.inr (Sum.inl (207, 27)),
    Sum.inr (Sum.inl (150, 38)),
    Sum.inr (Sum.inl (173, 59)),
    Sum.inr (Sum.inl (38, 27)),
    Sum.inr (Sum.inl (18, 55)),
    Sum.inr (Sum.inl (38, 19)),
    Sum.inr (Sum.inl (38, 17)),
    Sum.inr (Sum.inl (213, 52)),
    Sum.inr (Sum.inl (150, 6)),
    Sum.inr (Sum.inl (173, 25)),
    Sum.inr (Sum.inl (207, 58)),
    Sum.inr (Sum.inl (173, 27)),
    Sum.inr (Sum.inl (213, 10)),
    Sum.inr (Sum.inl (150, 46)),
    Sum.inr (Sum.inl (207, 37)),
    Sum.inr (Sum.inl (18, 23)),
    Sum.inr (Sum.inl (18, 39)),
    Sum.inr (Sum.inl (38, 25)),
    Sum.inr (Sum.inl (18, 7)),
    Sum.inr (Sum.inl (173, 57)),
    Sum.inr (Sum.inl (150, 14)),
    Sum.inr (Sum.inl (207, 4)),
    Sum.inr (Sum.inl (213, 21)),
    Sum.inr (Sum.inl (119, 9)),
    Sum.inr (Sum.inl (118, 61)),
    Sum.inr (Sum.inl (112, 55)),
    Sum.inr (Sum.inl (114, 26)),
    Sum.inr (Sum.inl (25, 10)),
    Sum.inr (Sum.inl (5, 50)),
    Sum.inr (Sum.inl (25, 2)),
    Sum.inr (Sum.inl (25, 0)),
    Sum.inr (Sum.inl (119, 24)),
    Sum.inr (Sum.inl (112, 37)),
    Sum.inr (Sum.inl (114, 10)),
    Sum.inr (Sum.inl (118, 34)),
    Sum.inr (Sum.inl (114, 8)),
    Sum.inr (Sum.inl (119, 38)),
    Sum.inr (Sum.inl (112, 10)),
    Sum.inr (Sum.inl (118, 10)),
    Sum.inr (Sum.inl (5, 18)),
    Sum.inr (Sum.inl (5, 34)),
    Sum.inr (Sum.inl (25, 8)),
    Sum.inr (Sum.inl (5, 2)),
    Sum.inr (Sum.inl (114, 24)),
    Sum.inr (Sum.inl (112, 24)),
    Sum.inr (Sum.inl (118, 21)),
    Sum.inr (Sum.inl (119, 55)),
    Sum.inr (Sum.inl (53, 37)),
    Sum.inr (Sum.inl (52, 58)),
    Sum.inr (Sum.inl (46, 27)),
    Sum.inr (Sum.inl (48, 34)),
    Sum.inr (Sum.inl (21, 43)),
    Sum.inr (Sum.inl (1, 59)),
    Sum.inr (Sum.inl (21, 35)),
    Sum.inr (Sum.inl (21, 33)),
    Sum.inr (Sum.inl (53, 52)),
    Sum.inr (Sum.inl (46, 10)),
    Sum.inr (Sum.inl (48, 50)),
    Sum.inr (Sum.inl (52, 26)),
    Sum.inr (Sum.inl (48, 38)),
    Sum.inr (Sum.inl (53, 36)),
    Sum.inr (Sum.inl (46, 11)),
    Sum.inr (Sum.inl (52, 27)),
    Sum.inr (Sum.inl (1, 27)),
    Sum.inr (Sum.inl (1, 43)),
    Sum.inr (Sum.inl (21, 41)),
    Sum.inr (Sum.inl (1, 11)),
    Sum.inr (Sum.inl (48, 54)),
    Sum.inr (Sum.inl (46, 26)),
    Sum.inr (Sum.inl (52, 59)),
    Sum.inr (Sum.inl (53, 53)),
    Sum.inr (Sum.inr (392, 0)),
    Sum.inr (Sum.inr (457, 15)),
    Sum.inr (Sum.inr (265, 9)),
    Sum.inr (Sum.inr (323, 20)),
    Sum.inr (Sum.inr (150, 7)),
    Sum.inr (Sum.inr (157, 5)),
    Sum.inr (Sum.inr (150, 18)),
    Sum.inr (Sum.inr (150, 4)),
    Sum.inr (Sum.inr (392, 8)),
    Sum.inr (Sum.inr (265, 2)),
    Sum.inr (Sum.inr (323, 12)),
    Sum.inr (Sum.inr (457, 22)),
    Sum.inr (Sum.inr (323, 10)),
    Sum.inr (Sum.inr (392, 13)),
    Sum.inr (Sum.inr (265, 21)),
    Sum.inr (Sum.inr (457, 1)),
    Sum.inr (Sum.inr (157, 16)),
    Sum.inr (Sum.inr (157, 17)),
    Sum.inr (Sum.inr (150, 6)),
    Sum.inr (Sum.inr (157, 19)),
    Sum.inr (Sum.inr (323, 3)),
    Sum.inr (Sum.inr (265, 14)),
    Sum.inr (Sum.inr (457, 11)),
    Sum.inr (Sum.inr (392, 23)),
    Sum.inr (Sum.inr (264, 8)),
    Sum.inr (Sum.inr (329, 22)),
    Sum.inr (Sum.inr (393, 2)),
    Sum.inr (Sum.inr (451, 12)),
    Sum.inr (Sum.inr (22, 7)),
    Sum.inr (Sum.inr (29, 5)),
    Sum.inr (Sum.inr (22, 18)),
    Sum.inr (Sum.inr (22, 4)),
    Sum.inr (Sum.inr (264, 0)),
    Sum.inr (Sum.inr (393, 9)),
    Sum.inr (Sum.inr (451, 20)),
    Sum.inr (Sum.inr (329, 15)),
    Sum.inr (Sum.inr (451, 3)),
    Sum.inr (Sum.inr (264, 23)),
    Sum.inr (Sum.inr (393, 14)),
    Sum.inr (Sum.inr (329, 11)),
    Sum.inr (Sum.inr (29, 16)),
    Sum.inr (Sum.inr (29, 17)),
    Sum.inr (Sum.inr (22, 6)),
    Sum.inr (Sum.inr (29, 19)),
    Sum.inr (Sum.inr (451, 10)),
    Sum.inr (Sum.inr (393, 21)),
    Sum.inr (Sum.inr (329, 1)),
    Sum.inr (Sum.inr (264, 13)),
    Sum.inr (Sum.inr (459, 13)),
    Sum.inr (Sum.inr (394, 1)),
    Sum.inr (Sum.inr (330, 21)),
    Sum.inr (Sum.inr (256, 10)),
    Sum.inr (Sum.inr (213, 7)),
    Sum.inr (Sum.inr (222, 5)),
    Sum.inr (Sum.inr (213, 18)),
    Sum.inr (Sum.inr (213, 4)),
    Sum.inr (Sum.inr (459, 23)),
    Sum.inr (Sum.inr (330, 14)),
    Sum.inr (Sum.inr (256, 3)),
    Sum.inr (Sum.inr (394, 11)),
    Sum.inr (Sum.inr (256, 20)),
    Sum.inr (Sum.inr (459, 0)),
    Sum.inr (Sum.inr (330, 9)),
    Sum.inr (Sum.inr (394, 15)),
    Sum.inr (Sum.inr (222, 16)),
    Sum.inr (Sum.inr (222, 17)),
    Sum.inr (Sum.inr (213, 6)),
    Sum.inr (Sum.inr (222, 19)),
    Sum.inr (Sum.inr (256, 12)),
    Sum.inr (Sum.inr (330, 2)),
    Sum.inr (Sum.inr (394, 22)),
    Sum.inr (Sum.inr (459, 8)),
    Sum.inr (Sum.inr (320, 23)),
    Sum.inr (Sum.inr (257, 11)),
    Sum.inr (Sum.inr (449, 14)),
    Sum.inr (Sum.inr (395, 3)),
    Sum.inr (Sum.inr (94, 7)),
    Sum.inr (Sum.inr (85, 5)),
    Sum.inr (Sum.inr (94, 18)),
    Sum.inr (Sum.inr (94, 4)),
    Sum.inr (Sum.inr (320, 13)),
    Sum.inr (Sum.inr (449, 21)),
    Sum.inr (Sum.inr (395, 10)),
    Sum.inr (Sum.inr (257, 1)),
    Sum.inr (Sum.inr (395, 12)),
    Sum.inr (Sum.inr (320, 8)),
    Sum.inr (Sum.inr (449, 2)),
    Sum.inr (Sum.inr (257, 22)),
    Sum.inr (Sum.inr (85, 16)),
    Sum.inr (Sum.inr (85, 17)),
    Sum.inr (Sum.inr (94, 6)),
    Sum.inr (Sum.inr (85, 19)),
    Sum.inr (Sum.inr (395, 20)),
    Sum.inr (Sum.inr (449, 9)),
    Sum.inr (Sum.inr (257, 15)),
    Sum.inr (Sum.inr (320, 0)),
    Sum.inr (Sum.inr (106, 8)),
    Sum.inr (Sum.inr (43, 11)),
    Sum.inr (Sum.inr (235, 9)),
    Sum.inr (Sum.inr (161, 10)),
    Sum.inr (Sum.inr (372, 4)),
    Sum.inr (Sum.inr (383, 5)),
    Sum.inr (Sum.inr (372, 6)),
    Sum.inr (Sum.inr (372, 7)),
    Sum.inr (Sum.inr (106, 0)),
    Sum.inr (Sum.inr (235, 2)),
    Sum.inr (Sum.inr (161, 3)),
    Sum.inr (Sum.inr (43, 1)),
    Sum.inr (Sum.inr (161, 20)),
    Sum.inr (Sum.inr (106, 23)),
    Sum.inr (Sum.inr (235, 21)),
    Sum.inr (Sum.inr (43, 22)),
    Sum.inr (Sum.inr (383, 16)),
    Sum.inr (Sum.inr (383, 17)),
    Sum.inr (Sum.inr (372, 18)),
    Sum.inr (Sum.inr (383, 19)),
    Sum.inr (Sum.inr (161, 12)),
    Sum.inr (Sum.inr (235, 14)),
    Sum.inr (Sum.inr (43, 15)),
    Sum.inr (Sum.inr (106, 13))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock071Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨18176 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock071InputMaskData : ℕ :=
  sixthHex% [
    "d73a10e13210fa3a108c3210ebf210f5f210d2f2108cf210f39210d99a10",
    "e69a108c9210cfaa10cdaa10cea2108ca210c0b210c8b210c4b2108cb210",
    "bc4a109c4210ac4a10cc4210dae1efece9eff7e1ef81e9efe629eff829ef",
    "df29ef8129effe49efd449efeb49ef8149efc271efc079efc371ef8179ef",
    "cd61efc569efc969ef8161efb199ef9199efa191efc191efbb09ee8d01ee",
    "9609eee001ee87c1ee99c1eebec1eee0c1ee9fa1eeb5a1ee8aa1eee0a1ee",
    "a391eea199eea291eee099eeac89eea481eea881eee089eed079eef079ee",
    "c071eea071eeba31ed8c39ed9731ede139ed86f9ed98f9edbff9ede1f9ed",
    "9e91edb491ed8b91ede191eda2a1eda0a9eda3a1ede1a9edadb1eda5b9ed",
    "a9b9ede1b1edd141edf141edc149eda149ed9bd9ecadd1ecb6d9ecc0d1ec",
    "a711ecb911ec9e11ecc011ecbf79ec9579ecaa79ecc079ec8341ec8149ec",
    "8241ecc049ec8c59ec8451ec8851ecc059ecf0a1ecd0a1ece0a9ec80a9ec",
    "ba51eb8c59eb9751ebe159eb8691eb9891ebbf91ebe191eb9ef9ebb4f9eb",
    "8bf9ebe1f9eba2c1eba0c9eba3c1ebe1c9ebadd1eba5d9eba9d9ebe1d1eb",
    "d121ebf121ebc129eba129eb9bb9eaadb1eab6b9eac0b1eaa779eab979ea",
    "9e79eac079eabf11ea9511eaaa11eac011ea8321ea8129ea8221eac029ea",
    "8c39ea8431ea8831eac039eaf0c1ead0c1eae0c9ea80c9ea9a81e9ac89e9",
    "b781e9c189e9a641e9b841e99f41e9c141e9be21e99421e9ab21e9c121e9",
    "8211e98019e98311e9c119e98d01e98509e98909e9c101e9f1f9e9d1f9e9",
    "e1f1e981f1e9fb69e8cd61e8d669e8a061e8c7a9e8d9a9e8fea9e8a0a9e8",
    "dfc9e8f5c9e8cac9e8a0c9e8e3f1e8e1f9e8e2f1e8a0f9e8ece9e8e4e1e8",
    "e8e1e8a0e9e89019e8b019e88011e8e011e89791e7a199e7ba91e7cc99e7",
    "ab51e7b551e79251e7cc51e7b331e79931e7a631e7cc31e78f09e78d01e7",
    "8e09e7cc01e78019e78811e78411e7cc19e7fce9e7dce9e7ece1e78ce1e7",
    "b679e68071e69b79e6ed71e68ab9e694b9e6b3b9e6edb9e692d9e6b8d9e6",
    "87d9e6edd9e6aee9e6ace1e6afe9e6ede1e6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock071InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock071InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock071OutputMaskData : ℕ :=
  sixthHex% [
    "8d218adb20bba7fb9b84faa1ea2dcfc12dc4d32dcf8d2dcfc988bb845b9b",
    "bc898a845aa184f8bbb42aa1e2239ba7f18af465c4fc6dc4c565cfb86dc4",
    "c5c2a1b0cb9be718bbe7118ae82d10be2c21c2f701e1f63b8f2155a4215e",
    "b62155e82155ac8421901701a8c510e1563be1f421a0663bf66f01c2fd10",
    "e0295e99615ea06955ac215ed18e3bd5c701821421f35d10c9f70b9ff63a",
    "e32d1ac02c20aefb4e85fb4597fb4ec9fb4e8d5e3ab1cd1a891f0bc08c20",
    "b16e3af0fc20a6f51a92670bc1f345b8bb4581b34e8dfb45811420855d1a",
    "d28e3aa3c70b872c28d12d19adf6398ef703e0206dcb2066d9206d87206d",
    "b2c5198e5639b68428ff17038ef519cf6703996e39adfc288f2866f66066",
    "cf686dc32066cfcf03cb86399c5519ed1c28d3f63885f709f92c29da2d13",
    "b4fa7d9ffa768dfa7dd3fa7de61f09da8c29e25e38abcd13ab6f09eafd13",
    "bcf429886638dbf276a2ba769bb27d97fa76ea5513ee1c29b9cf09c88638",
    "07dbf151dac02d01e00e00da1197b43a97bf2897b47697b44372c07fe1e0",
    "4733f10ea0da0e02c04f90da1999e02d0bf10fdfbf7697bf4f9fb443d7bf",
    "4f38da4b71e01ca2c06debf15301e10500d079dbf05adaca454da46e4daf",
    "7c4da4224da417a8d02b3bf013e9e15a7aca2b98d06a0aca3c03f00891e1",
    "5b05af224daf1b45a4170daf6aa2ca6eebf03938d04871e11ddac24bdbf3",
    "3700d31401e90b968720968c3296876c96872833f314a0d32c72c265e1e9",
    "1403f35591e90398d3370ac215de8c6c968c559e8759d68c2479e92030d3",
    "77e3f306aac23c00d96a01e816dac835dbf22a4c9c014c97134c9c4d4c9c",
    "09e9e8357ac80da8d9443bf24499e8050bf25302c86790d93404974d4c97",
    "74449c780c9774e3f270aac82779e85630d9aaf633fcf702802c22a32d18",
    "bcba7697ba7d85ba76dbba769f1f02a38c229b5e33d2cd18d26f0293fd18",
    "c5f422f16633d3b27daafa7d93f2769fba7d935518971c22c0cf02b18633",
    "fe2c23a82d12d4f632f7f708e86066c3606dd160668f6066cbc512f75632",
    "cf8423861708f7f512b66708e06e32d4fc23"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock071OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock071OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock071InputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock071InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock071InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock071OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df8616df8e38617df8618617e185f85f85f85f7e196175d8617df85f85f",
    "7df7df7e185f85f85f96175d85f7e17df8617df7df7e17e17e185f6df8e3",
    "8617df7e17e18618617e185f7e17e16df8e385f7e18617df8618617e17e1",
    "7df85f6e18e37df7e17e18617e186186185f86185f95f75d85f8617df7e1",
    "85f7df7df85f8617e195f75d7df7e185f7df85f7df86185f86185f95f75d",
    "7e17df7df7e185f7df8617e185f85f96175d7e185f7df8617df7df85f85f",
    "85f7e196175d7df86185f85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock071OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock071OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block071_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock071Input a) =
      generatedSixthXiShortBlock071InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock071Output a) =
      generatedSixthXiShortBlock071OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock071Input a) =
      generatedSixthXiShortBlock071InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock071Output a) =
      generatedSixthXiShortBlock071OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block071_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock071InputMask a) =
      generatedSixthXiShortBlock071OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock071InputMask a)) *
      generatedSixthXiShortBlock071InputNumerator a =
        generatedSixthXiShortBlock071OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block071_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock071Input a
    let y := generatedSixthXiShortBlock071Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block071_cache a
  have hs := generatedSixth_xi_short_block071_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block071_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock071Input a
    let y := generatedSixthXiShortBlock071Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block071_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block071_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock071Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block071_certificate a).1
    (generatedSixth_xi_short_block071_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
