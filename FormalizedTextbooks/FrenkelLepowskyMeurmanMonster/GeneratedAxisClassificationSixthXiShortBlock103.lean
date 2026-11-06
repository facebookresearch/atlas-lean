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
def generatedSixthXiShortBlock103Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (15, 24)),
    Sum.inr (Sum.inl (15, 40)),
    Sum.inr (Sum.inl (35, 36)),
    Sum.inr (Sum.inl (15, 8)),
    Sum.inr (Sum.inl (170, 48)),
    Sum.inr (Sum.inl (147, 16)),
    Sum.inr (Sum.inl (204, 29)),
    Sum.inr (Sum.inl (210, 36)),
    Sum.inr (Sum.inr (121, 23)),
    Sum.inr (Sum.inr (56, 1)),
    Sum.inr (Sum.inr (248, 9)),
    Sum.inr (Sum.inr (178, 12)),
    Sum.inr (Sum.inr (359, 18)),
    Sum.inr (Sum.inr (364, 5)),
    Sum.inr (Sum.inr (359, 7)),
    Sum.inr (Sum.inr (359, 6)),
    Sum.inr (Sum.inr (121, 13)),
    Sum.inr (Sum.inr (248, 2)),
    Sum.inr (Sum.inr (178, 20)),
    Sum.inr (Sum.inr (56, 11)),
    Sum.inr (Sum.inr (178, 3)),
    Sum.inr (Sum.inr (121, 8)),
    Sum.inr (Sum.inr (248, 21)),
    Sum.inr (Sum.inr (56, 15)),
    Sum.inr (Sum.inr (364, 16)),
    Sum.inr (Sum.inr (364, 17)),
    Sum.inr (Sum.inr (359, 4)),
    Sum.inr (Sum.inr (364, 19)),
    Sum.inr (Sum.inr (178, 10)),
    Sum.inr (Sum.inr (248, 14)),
    Sum.inr (Sum.inr (56, 22)),
    Sum.inr (Sum.inr (121, 0)),
    Sum.inr (Sum.inr (184, 13)),
    Sum.inr (Sum.inr (249, 11)),
    Sum.inr (Sum.inr (57, 2)),
    Sum.inr (Sum.inr (115, 20)),
    Sum.inr (Sum.inr (422, 18)),
    Sum.inr (Sum.inr (429, 5)),
    Sum.inr (Sum.inr (422, 7)),
    Sum.inr (Sum.inr (422, 6)),
    Sum.inr (Sum.inr (184, 23)),
    Sum.inr (Sum.inr (57, 9)),
    Sum.inr (Sum.inr (115, 12)),
    Sum.inr (Sum.inr (249, 1)),
    Sum.inr (Sum.inr (115, 10)),
    Sum.inr (Sum.inr (184, 0)),
    Sum.inr (Sum.inr (57, 14)),
    Sum.inr (Sum.inr (249, 22)),
    Sum.inr (Sum.inr (429, 16)),
    Sum.inr (Sum.inr (429, 17)),
    Sum.inr (Sum.inr (422, 4)),
    Sum.inr (Sum.inr (429, 19)),
    Sum.inr (Sum.inr (115, 3)),
    Sum.inr (Sum.inr (57, 21)),
    Sum.inr (Sum.inr (249, 15)),
    Sum.inr (Sum.inr (184, 8)),
    Sum.inr (Sum.inr (241, 8)),
    Sum.inr (Sum.inr (176, 15)),
    Sum.inr (Sum.inr (112, 21)),
    Sum.inr (Sum.inr (58, 3)),
    Sum.inr (Sum.inr (495, 18)),
    Sum.inr (Sum.inr (484, 5)),
    Sum.inr (Sum.inr (495, 7)),
    Sum.inr (Sum.inr (495, 6)),
    Sum.inr (Sum.inr (241, 0)),
    Sum.inr (Sum.inr (112, 14)),
    Sum.inr (Sum.inr (58, 10)),
    Sum.inr (Sum.inr (176, 22)),
    Sum.inr (Sum.inr (58, 12)),
    Sum.inr (Sum.inr (241, 23)),
    Sum.inr (Sum.inr (112, 9)),
    Sum.inr (Sum.inr (176, 1)),
    Sum.inr (Sum.inr (484, 16)),
    Sum.inr (Sum.inr (484, 17)),
    Sum.inr (Sum.inr (495, 4)),
    Sum.inr (Sum.inr (484, 19)),
    Sum.inr (Sum.inr (58, 20)),
    Sum.inr (Sum.inr (112, 2)),
    Sum.inr (Sum.inr (176, 11)),
    Sum.inr (Sum.inr (241, 13)),
    Sum.inr (Sum.inr (59, 0)),
    Sum.inr (Sum.inr (122, 22)),
    Sum.inr (Sum.inr (186, 14)),
    Sum.inr (Sum.inr (240, 10)),
    Sum.inr (Sum.inr (293, 18)),
    Sum.inr (Sum.inr (302, 5)),
    Sum.inr (Sum.inr (293, 7)),
    Sum.inr (Sum.inr (293, 6)),
    Sum.inr (Sum.inr (59, 8)),
    Sum.inr (Sum.inr (186, 21)),
    Sum.inr (Sum.inr (240, 3)),
    Sum.inr (Sum.inr (122, 15)),
    Sum.inr (Sum.inr (240, 20)),
    Sum.inr (Sum.inr (59, 13)),
    Sum.inr (Sum.inr (186, 2)),
    Sum.inr (Sum.inr (122, 11)),
    Sum.inr (Sum.inr (302, 16)),
    Sum.inr (Sum.inr (302, 17)),
    Sum.inr (Sum.inr (293, 4)),
    Sum.inr (Sum.inr (302, 19)),
    Sum.inr (Sum.inr (240, 12)),
    Sum.inr (Sum.inr (186, 9)),
    Sum.inr (Sum.inr (122, 1)),
    Sum.inr (Sum.inr (59, 23)),
    Sum.inr (Sum.inl (211, 51)),
    Sum.inr (Sum.inl (205, 56)),
    Sum.inr (Sum.inl (148, 23)),
    Sum.inr (Sum.inl (171, 8)),
    Sum.inr (Sum.inl (36, 41)),
    Sum.inr (Sum.inl (16, 9)),
    Sum.inr (Sum.inl (36, 44)),
    Sum.inr (Sum.inl (36, 32)),
    Sum.inr (Sum.inl (211, 44)),
    Sum.inr (Sum.inl (148, 8)),
    Sum.inr (Sum.inl (171, 23)),
    Sum.inr (Sum.inl (205, 39)),
    Sum.inr (Sum.inl (171, 41)),
    Sum.inr (Sum.inl (211, 18)),
    Sum.inr (Sum.inl (148, 54)),
    Sum.inr (Sum.inl (205, 25)),
    Sum.inr (Sum.inl (16, 22)),
    Sum.inr (Sum.inl (16, 38)),
    Sum.inr (Sum.inl (36, 37)),
    Sum.inr (Sum.inl (16, 57)),
    Sum.inr (Sum.inl (171, 54)),
    Sum.inr (Sum.inl (148, 41)),
    Sum.inr (Sum.inl (205, 6)),
    Sum.inr (Sum.inl (211, 13)),
    Sum.inr (Sum.inl (214, 32)),
    Sum.inr (Sum.inl (208, 63)),
    Sum.inr (Sum.inl (151, 16)),
    Sum.inr (Sum.inl (174, 15)),
    Sum.inr (Sum.inl (39, 47)),
    Sum.inr (Sum.inl (19, 15)),
    Sum.inr (Sum.inl (39, 63)),
    Sum.inr (Sum.inl (39, 0)),
    Sum.inr (Sum.inl (214, 63)),
    Sum.inr (Sum.inl (151, 15)),
    Sum.inr (Sum.inl (174, 16)),
    Sum.inr (Sum.inl (208, 32)),
    Sum.inr (Sum.inl (174, 32)),
    Sum.inr (Sum.inl (214, 15)),
    Sum.inr (Sum.inl (151, 63)),
    Sum.inr (Sum.inl (208, 16)),
    Sum.inr (Sum.inl (19, 16)),
    Sum.inr (Sum.inl (19, 32)),
    Sum.inr (Sum.inl (39, 16)),
    Sum.inr (Sum.inl (19, 63)),
    Sum.inr (Sum.inl (174, 63)),
    Sum.inr (Sum.inl (151, 32)),
    Sum.inr (Sum.inl (208, 15)),
    Sum.inr (Sum.inl (214, 16)),
    Sum.inr (Sum.inl (212, 25)),
    Sum.inr (Sum.inl (206, 46)),
    Sum.inr (Sum.inl (149, 42)),
    Sum.inr (Sum.inl (172, 2)),
    Sum.inr (Sum.inl (37, 22)),
    Sum.inr (Sum.inl (17, 16)),
    Sum.inr (Sum.inl (37, 19)),
    Sum.inr (Sum.inl (37, 31)),
    Sum.inr (Sum.inl (212, 28)),
    Sum.inr (Sum.inl (149, 47)),
    Sum.inr (Sum.inl (172, 7)),
    Sum.inr (Sum.inl (206, 43)),
    Sum.inr (Sum.inl (172, 11)),
    Sum.inr (Sum.inl (212, 16)),
    Sum.inr (Sum.inl (149, 35)),
    Sum.inr (Sum.inl (206, 39)),
    Sum.inr (Sum.inl (17, 26)),
    Sum.inr (Sum.inl (17, 25)),
    Sum.inr (Sum.inl (37, 26)),
    Sum.inr (Sum.inl (17, 19)),
    Sum.inr (Sum.inl (172, 14)),
    Sum.inr (Sum.inl (149, 38)),
    Sum.inr (Sum.inl (206, 34)),
    Sum.inr (Sum.inl (212, 21)),
    Sum.inr (Sum.inl (188, 51)),
    Sum.inr (Sum.inl (187, 28)),
    Sum.inr (Sum.inl (143, 39)),
    Sum.inr (Sum.inl (166, 8)),
    Sum.inr (Sum.inl (31, 57)),
    Sum.inr (Sum.inl (11, 12)),
    Sum.inr (Sum.inl (31, 60)),
    Sum.inr (Sum.inl (31, 48)),
    Sum.inr (Sum.inl (188, 54)),
    Sum.inr (Sum.inl (143, 34)),
    Sum.inr (Sum.inl (166, 13)),
    Sum.inr (Sum.inl (187, 25)),
    Sum.inr (Sum.inl (166, 51)),
    Sum.inr (Sum.inl (188, 8)),
    Sum.inr (Sum.inl (143, 28)),
    Sum.inr (Sum.inl (187, 39)),
    Sum.inr (Sum.inl (11, 19)),
    Sum.inr (Sum.inl (11, 35)),
    Sum.inr (Sum.inl (31, 53)),
    Sum.inr (Sum.inl (11, 60)),
    Sum.inr (Sum.inl (166, 54)),
    Sum.inr (Sum.inl (143, 25)),
    Sum.inr (Sum.inl (187, 34)),
    Sum.inr (Sum.inl (188, 13)),
    Sum.inr (Sum.inr (318, 8)),
    Sum.inr (Sum.inr (383, 11)),
    Sum.inr (Sum.inr (447, 9)),
    Sum.inr (Sum.inr (501, 10)),
    Sum.inr (Sum.inr (32, 4)),
    Sum.inr (Sum.inr (43, 5)),
    Sum.inr (Sum.inr (32, 6)),
    Sum.inr (Sum.inr (32, 7)),
    Sum.inr (Sum.inr (318, 0)),
    Sum.inr (Sum.inr (447, 2)),
    Sum.inr (Sum.inr (501, 3)),
    Sum.inr (Sum.inr (383, 1)),
    Sum.inr (Sum.inr (501, 20)),
    Sum.inr (Sum.inr (318, 23)),
    Sum.inr (Sum.inr (447, 21)),
    Sum.inr (Sum.inr (383, 22)),
    Sum.inr (Sum.inr (43, 16)),
    Sum.inr (Sum.inr (43, 17)),
    Sum.inr (Sum.inr (32, 18)),
    Sum.inr (Sum.inr (43, 19)),
    Sum.inr (Sum.inr (501, 12)),
    Sum.inr (Sum.inr (447, 14)),
    Sum.inr (Sum.inr (383, 15)),
    Sum.inr (Sum.inr (318, 13)),
    Sum.inr (Sum.inr (308, 0)),
    Sum.inr (Sum.inr (373, 1)),
    Sum.inr (Sum.inr (437, 2)),
    Sum.inr (Sum.inr (511, 3)),
    Sum.inr (Sum.inr (42, 4)),
    Sum.inr (Sum.inr (33, 5)),
    Sum.inr (Sum.inr (42, 6)),
    Sum.inr (Sum.inr (42, 7)),
    Sum.inr (Sum.inr (308, 8)),
    Sum.inr (Sum.inr (437, 9)),
    Sum.inr (Sum.inr (511, 10)),
    Sum.inr (Sum.inr (373, 11)),
    Sum.inr (Sum.inr (511, 12)),
    Sum.inr (Sum.inr (308, 13)),
    Sum.inr (Sum.inr (437, 14)),
    Sum.inr (Sum.inr (373, 15)),
    Sum.inr (Sum.inr (33, 16)),
    Sum.inr (Sum.inr (33, 17)),
    Sum.inr (Sum.inr (42, 18)),
    Sum.inr (Sum.inr (33, 19)),
    Sum.inr (Sum.inr (511, 20)),
    Sum.inr (Sum.inr (437, 21)),
    Sum.inr (Sum.inr (373, 22)),
    Sum.inr (Sum.inr (308, 23)),
    Sum.inr (Sum.inr (316, 23)),
    Sum.inr (Sum.inr (381, 22)),
    Sum.inr (Sum.inr (445, 21)),
    Sum.inr (Sum.inr (503, 20)),
    Sum.inr (Sum.inr (34, 4)),
    Sum.inr (Sum.inr (41, 5)),
    Sum.inr (Sum.inr (34, 6)),
    Sum.inr (Sum.inr (34, 7))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock103Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨26368 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock103InputMaskData : ℕ :=
  sixthHex% [
    "bc5766b45766b85f66f05766c0a766e0af66d0af66b0af66aad7659cd765",
    "87d765f1df65961765881f65af1765f117658e7765a477659b7765f17f65",
    "b24765b04f65b34765f14765bd5f65b55f65b95765f15f65c1af65e1a765",
    "d1a765b1a765dbd764edd764f6d76480df64e71764f91f64de1764801764",
    "ff7764d57764ea7764807f64c34f64c14764c24f64804f64cc5f64c45f64",
    "c85764805f64b0a76490af64a0af64c0af6493df63a5df63bedf63c8d763",
    "af1763b11f63961763c81763b777639d7763a27763c87f638b4f63894763",
    "8a4f63c84f638457638c5763805f63c85763f8a763d8af63e8af6388af63",
    "e2df62d4df62cfdf62b9d762de1762c01f62e71762b91762c67762ec7762",
    "d37762b97f62fa4762f84f62fb4762b94762f55762fd5762f15f62b95762",
    "89af62a9a76299a762f9a762e3d761d5d761ced761b8df61df1f61c11761",
    "e61f61b81f61c77761ed7761d27761b87f61fb4761f94f61fa4761b84761",
    "f45f61fc5f61f05761b85f6188a761a8af6198af61f8af61d2df60e4df60",
    "ffdf6089d760ee1760f01f60d71760891760f67f60dc7f60e37f60897760",
    "ca4760c84f60cb4760894760c55760cd5760c15f60895760b9a76099af60",
    "a9af60c9af60db670fed670ff66f0f80670fe7a70ff9af0fdea70f80a70f",
    "ffcf0fd5c70feac70f80c70fc3ff0fc1ff0fc2ff0f80f70fcce70fc4e70f",
    "c8e70f80ef0fb01f0f90170fa0170fc0170fab6f0e9d6f0e86670ef06f0e",
    "97af0e89a70eaeaf0ef0af0e8fc70ea5cf0e9acf0ef0cf0eb3ff0eb1ff0e",
    "b2ff0ef0f70ebcef0eb4ef0eb8ef0ef0e70ec01f0ee0170ed0170eb0170e",
    "94670da2670db96f0dcf670da8a70db6af0d91a70dcfa70db0c70d9acf0d",
    "a5cf0dcfcf0d8cff0d8eff0d8dff0dcff70d83e70d8be70d87e70dcfef0d",
    "ff170ddf1f0def1f0d8f1f0da4670c92670c896f0cff670c98a70c86af0c",
    "a1a70cffa70c80c70caacf0c95cf0cffcf0cbcf70cbef70cbdf70cffff0c",
    "b3e70cbbe70cb7e70cffef0ccf1f0cef170cdf170cbf170c92670ba4670b",
    "bf6f0bc9670baeaf0bb0a70b97af0bc9af0b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock103InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock103InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock103OutputMaskData : ℕ :=
  sixthHex% [
    "8698b28e90b2c6d8b9ca90b2c67fd7b376ed95e5cde4acfc92acf4b5edc5",
    "b876e59b77df84e0b1dea0babde0b1e3e0b1a745c59bd6e5a304f49bd7df",
    "9b75c5dae7df8ceee5c93cf4ebe8bae3e0baaba8b1a7e0baab0fdfde06e5",
    "f895c589dcf4d50cfef24dcfffd6efdcd7d5c340bb9900b0fa40bba440bb",
    "e0e5cfdc76efe4a4fedc77d5ad95cfec07d5ba0eefffdcfeac48b0a440b0",
    "ec08bbe040b09defd5e8e6efce75cfbf3cfe536c43742d7279b6525ab768",
    "3460066e200d0d600653600617c5722b56521384432b57685ab5721b2768",
    "4d2e5208fc432a280d22200d6a680666200d6acf681fc652395572481c43",
    "14cc49338d783e16581d176273c00c2980074ac00c14c00c5065786cf658",
    "5424496cf7626c55782dc7627bce583e1c496d88076580072dc80c218007",
    "5c2f622926580fb5787efc4979bc415efd7053665070676a1eb00444f00f",
    "27b00479b0044c557070c65048144170c76a70657031f76a67fe50222c41",
    "00f80f08f00f40b8044cf00f315f6a44565062c570138c413a5c401d1d71",
    "10865133876b5d500507100e6450053a50050fb5713326510bf44033276b",
    "42c57103576b555e51108c4043180e4b100e0358050f100e03ff6b76f651",
    "506571212c40c788dbe0c9ea9c12cabf13f0d1c49e8b8495e8c49eb6c49e",
    "8321eacef2caf620dbbfb3f0bf11ea8fc3f0a88aca9c18dbcf8c95c78495",
    "fe8c9ef2c495fe2bf08b22caadb1eadcf8dbe6f3f1c1b2c0bd69e09e68da",
    "f0bfb4aaffbfc9bfb497bfb4a25ac0ef89e0d75bf19ec8daef2ac0dff8da",
    "f8b1e0cc23f1eef7bfe6ffbfdff7b4d3bfbfae10dadb19e0fd8ac08cc3f1",
    "a4cac8838bf9ff50d9dc51e3b2868de8c6868b868dd5868d9123f9dcf0d9",
    "e422c8adb1e3dc53f9ec81e3cbc8d9ff5ac8acce86a4c6869dce8d918686",
    "ec29e39920d9bfb3f9cefac881f1e9a6b0d8da6bf8f96ac297bdaccdfda7",
    "aebdacf0bdacb418d8f9cbf8c119e9888ac28828d8b8fac29fb3f8ab21e9",
    "89f5a781fda7b8f5acb4bda7b852c2cd5bf8ebc8d89a81e92c986e0bd95f",
    "77027f5403454b942b11d42072942b2c942b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock103OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock103OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock103InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock103InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock103InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock103OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f7e17e17df7df6df8e385f7e17e185f7e185f85f7e18617df96175d",
    "7df8617df7df85f7e17e17e17e17df6e18e37e17df7e17df86185f7df7e1",
    "7e18616e18e37df7e18617e186185f7df85f7e17df6e18e385f8617e17df",
    "86185f86185f7e18616e18e386185f8617e186185f8617e17df7e16e18e3",
    "7e17df86185f7e18618617e17df85f6e18e37df7e17e18617e186186185f",
    "86185f95f75d7e17df7df7e185f7df8617e17df85f6e18e386185f7e1861",
    "7e18617df7e185f85f96175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock103OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock103OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block103_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock103Input a) =
      generatedSixthXiShortBlock103InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock103Output a) =
      generatedSixthXiShortBlock103OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock103Input a) =
      generatedSixthXiShortBlock103InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock103Output a) =
      generatedSixthXiShortBlock103OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block103_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock103InputMask a) =
      generatedSixthXiShortBlock103OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock103InputMask a)) *
      generatedSixthXiShortBlock103InputNumerator a =
        generatedSixthXiShortBlock103OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block103_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock103Input a
    let y := generatedSixthXiShortBlock103Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block103_cache a
  have hs := generatedSixth_xi_short_block103_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block103_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock103Input a
    let y := generatedSixthXiShortBlock103Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block103_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block103_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock103Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block103_certificate a).1
    (generatedSixth_xi_short_block103_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
