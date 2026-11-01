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
def generatedSixthXiShortBlock080Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (196, 5)),
    Sum.inr (Sum.inl (144, 38)),
    Sum.inr (Sum.inl (167, 4)),
    Sum.inr (Sum.inl (195, 33)),
    Sum.inr (Sum.inl (167, 6)),
    Sum.inr (Sum.inl (196, 42)),
    Sum.inr (Sum.inl (144, 36)),
    Sum.inr (Sum.inl (195, 9)),
    Sum.inr (Sum.inl (12, 18)),
    Sum.inr (Sum.inl (12, 34)),
    Sum.inr (Sum.inl (32, 8)),
    Sum.inr (Sum.inl (12, 2)),
    Sum.inr (Sum.inl (167, 36)),
    Sum.inr (Sum.inl (144, 4)),
    Sum.inr (Sum.inl (195, 41)),
    Sum.inr (Sum.inl (196, 59)),
    Sum.inr (Sum.inl (88, 7)),
    Sum.inr (Sum.inl (87, 38)),
    Sum.inr (Sum.inl (81, 30)),
    Sum.inr (Sum.inl (83, 5)),
    Sum.inr (Sum.inl (23, 58)),
    Sum.inr (Sum.inl (3, 12)),
    Sum.inr (Sum.inl (23, 50)),
    Sum.inr (Sum.inl (23, 62)),
    Sum.inr (Sum.inl (88, 22)),
    Sum.inr (Sum.inl (81, 1)),
    Sum.inr (Sum.inl (83, 23)),
    Sum.inr (Sum.inl (87, 57)),
    Sum.inr (Sum.inl (83, 7)),
    Sum.inr (Sum.inl (88, 40)),
    Sum.inr (Sum.inl (81, 37)),
    Sum.inr (Sum.inl (87, 7)),
    Sum.inr (Sum.inl (3, 44)),
    Sum.inr (Sum.inl (3, 28)),
    Sum.inr (Sum.inl (23, 54)),
    Sum.inr (Sum.inl (3, 60)),
    Sum.inr (Sum.inl (83, 21)),
    Sum.inr (Sum.inl (81, 58)),
    Sum.inr (Sum.inl (87, 24)),
    Sum.inr (Sum.inl (88, 57)),
    Sum.inr (Sum.inr (429, 13)),
    Sum.inr (Sum.inr (492, 11)),
    Sum.inr (Sum.inr (300, 2)),
    Sum.inr (Sum.inr (358, 20)),
    Sum.inr (Sum.inr (179, 18)),
    Sum.inr (Sum.inr (184, 5)),
    Sum.inr (Sum.inr (179, 7)),
    Sum.inr (Sum.inr (179, 6)),
    Sum.inr (Sum.inr (429, 23)),
    Sum.inr (Sum.inr (300, 9)),
    Sum.inr (Sum.inr (358, 12)),
    Sum.inr (Sum.inr (492, 1)),
    Sum.inr (Sum.inr (358, 10)),
    Sum.inr (Sum.inr (429, 0)),
    Sum.inr (Sum.inr (300, 14)),
    Sum.inr (Sum.inr (492, 22)),
    Sum.inr (Sum.inr (184, 16)),
    Sum.inr (Sum.inr (184, 17)),
    Sum.inr (Sum.inr (179, 4)),
    Sum.inr (Sum.inr (184, 19)),
    Sum.inr (Sum.inr (358, 3)),
    Sum.inr (Sum.inr (300, 21)),
    Sum.inr (Sum.inr (492, 15)),
    Sum.inr (Sum.inr (429, 8)),
    Sum.inr (Sum.inr (364, 23)),
    Sum.inr (Sum.inr (301, 1)),
    Sum.inr (Sum.inr (493, 9)),
    Sum.inr (Sum.inr (423, 12)),
    Sum.inr (Sum.inr (114, 18)),
    Sum.inr (Sum.inr (121, 5)),
    Sum.inr (Sum.inr (114, 7)),
    Sum.inr (Sum.inr (114, 6)),
    Sum.inr (Sum.inr (364, 13)),
    Sum.inr (Sum.inr (493, 2)),
    Sum.inr (Sum.inr (423, 20)),
    Sum.inr (Sum.inr (301, 11)),
    Sum.inr (Sum.inr (423, 3)),
    Sum.inr (Sum.inr (364, 8)),
    Sum.inr (Sum.inr (493, 21)),
    Sum.inr (Sum.inr (301, 15)),
    Sum.inr (Sum.inr (121, 16)),
    Sum.inr (Sum.inr (121, 17)),
    Sum.inr (Sum.inr (114, 4)),
    Sum.inr (Sum.inr (121, 19)),
    Sum.inr (Sum.inr (423, 10)),
    Sum.inr (Sum.inr (493, 14)),
    Sum.inr (Sum.inr (301, 22)),
    Sum.inr (Sum.inr (364, 0)),
    Sum.inr (Sum.inr (302, 0)),
    Sum.inr (Sum.inr (367, 22)),
    Sum.inr (Sum.inr (431, 14)),
    Sum.inr (Sum.inr (485, 10)),
    Sum.inr (Sum.inr (48, 18)),
    Sum.inr (Sum.inr (59, 5)),
    Sum.inr (Sum.inr (48, 7)),
    Sum.inr (Sum.inr (48, 6)),
    Sum.inr (Sum.inr (302, 8)),
    Sum.inr (Sum.inr (431, 21)),
    Sum.inr (Sum.inr (485, 3)),
    Sum.inr (Sum.inr (367, 15)),
    Sum.inr (Sum.inr (485, 20)),
    Sum.inr (Sum.inr (302, 13)),
    Sum.inr (Sum.inr (431, 2)),
    Sum.inr (Sum.inr (367, 11)),
    Sum.inr (Sum.inr (59, 16)),
    Sum.inr (Sum.inr (59, 17)),
    Sum.inr (Sum.inr (48, 4)),
    Sum.inr (Sum.inr (59, 19)),
    Sum.inr (Sum.inr (485, 12)),
    Sum.inr (Sum.inr (431, 9)),
    Sum.inr (Sum.inr (367, 1)),
    Sum.inr (Sum.inr (302, 23)),
    Sum.inr (Sum.inr (484, 8)),
    Sum.inr (Sum.inr (421, 15)),
    Sum.inr (Sum.inr (357, 21)),
    Sum.inr (Sum.inr (303, 3)),
    Sum.inr (Sum.inr (250, 18)),
    Sum.inr (Sum.inr (241, 5)),
    Sum.inr (Sum.inr (250, 7)),
    Sum.inr (Sum.inr (250, 6)),
    Sum.inr (Sum.inr (484, 0)),
    Sum.inr (Sum.inr (357, 14)),
    Sum.inr (Sum.inr (303, 10)),
    Sum.inr (Sum.inr (421, 22)),
    Sum.inr (Sum.inr (303, 12)),
    Sum.inr (Sum.inr (484, 23)),
    Sum.inr (Sum.inr (357, 9)),
    Sum.inr (Sum.inr (421, 1)),
    Sum.inr (Sum.inr (241, 16)),
    Sum.inr (Sum.inr (241, 17)),
    Sum.inr (Sum.inr (250, 4)),
    Sum.inr (Sum.inr (241, 19)),
    Sum.inr (Sum.inr (303, 20)),
    Sum.inr (Sum.inr (357, 2)),
    Sum.inr (Sum.inr (421, 11)),
    Sum.inr (Sum.inr (484, 13)),
    Sum.inr (Sum.inl (88, 11)),
    Sum.inr (Sum.inl (87, 42)),
    Sum.inr (Sum.inl (81, 29)),
    Sum.inr (Sum.inl (83, 9)),
    Sum.inr (Sum.inl (23, 52)),
    Sum.inr (Sum.inl (3, 62)),
    Sum.inr (Sum.inl (23, 60)),
    Sum.inr (Sum.inl (23, 48)),
    Sum.inr (Sum.inl (88, 26)),
    Sum.inr (Sum.inl (81, 2)),
    Sum.inr (Sum.inl (83, 27)),
    Sum.inr (Sum.inl (87, 53)),
    Sum.inr (Sum.inl (83, 11)),
    Sum.inr (Sum.inl (88, 36)),
    Sum.inr (Sum.inl (81, 38)),
    Sum.inr (Sum.inl (87, 11)),
    Sum.inr (Sum.inl (3, 30)),
    Sum.inr (Sum.inl (3, 46)),
    Sum.inr (Sum.inl (23, 56)),
    Sum.inr (Sum.inl (3, 14)),
    Sum.inr (Sum.inl (83, 25)),
    Sum.inr (Sum.inl (81, 57)),
    Sum.inr (Sum.inl (87, 20)),
    Sum.inr (Sum.inl (88, 53)),
    Sum.inr (Sum.inl (196, 24)),
    Sum.inr (Sum.inl (195, 2)),
    Sum.inr (Sum.inl (144, 10)),
    Sum.inr (Sum.inl (167, 42)),
    Sum.inr (Sum.inl (32, 10)),
    Sum.inr (Sum.inl (12, 0)),
    Sum.inr (Sum.inl (32, 2)),
    Sum.inr (Sum.inl (32, 14)),
    Sum.inr (Sum.inl (196, 9)),
    Sum.inr (Sum.inl (144, 42)),
    Sum.inr (Sum.inl (167, 8)),
    Sum.inr (Sum.inl (195, 34)),
    Sum.inr (Sum.inl (167, 10)),
    Sum.inr (Sum.inl (196, 38)),
    Sum.inr (Sum.inl (144, 40)),
    Sum.inr (Sum.inl (195, 10)),
    Sum.inr (Sum.inl (12, 32)),
    Sum.inr (Sum.inl (12, 16)),
    Sum.inr (Sum.inl (32, 6)),
    Sum.inr (Sum.inl (12, 48)),
    Sum.inr (Sum.inl (167, 40)),
    Sum.inr (Sum.inl (144, 8)),
    Sum.inr (Sum.inl (195, 42)),
    Sum.inr (Sum.inl (196, 55)),
    Sum.inr (Sum.inl (210, 25)),
    Sum.inr (Sum.inl (204, 11)),
    Sum.inr (Sum.inl (147, 27)),
    Sum.inr (Sum.inl (170, 59)),
    Sum.inr (Sum.inl (35, 43)),
    Sum.inr (Sum.inl (15, 9)),
    Sum.inr (Sum.inl (35, 35)),
    Sum.inr (Sum.inl (35, 47)),
    Sum.inr (Sum.inl (210, 54)),
    Sum.inr (Sum.inl (147, 9)),
    Sum.inr (Sum.inl (170, 43)),
    Sum.inr (Sum.inl (204, 41)),
    Sum.inr (Sum.inl (170, 41)),
    Sum.inr (Sum.inl (210, 34)),
    Sum.inr (Sum.inl (147, 11)),
    Sum.inr (Sum.inl (204, 54)),
    Sum.inr (Sum.inl (15, 41)),
    Sum.inr (Sum.inl (15, 25)),
    Sum.inr (Sum.inl (35, 39)),
    Sum.inr (Sum.inl (15, 57)),
    Sum.inr (Sum.inl (170, 57)),
    Sum.inr (Sum.inl (147, 25)),
    Sum.inr (Sum.inl (204, 20)),
    Sum.inr (Sum.inl (210, 13)),
    Sum.inr (Sum.inl (133, 27)),
    Sum.inr (Sum.inl (132, 58)),
    Sum.inr (Sum.inl (126, 26)),
    Sum.inr (Sum.inl (128, 6)),
    Sum.inr (Sum.inl (26, 27)),
    Sum.inr (Sum.inl (6, 5)),
    Sum.inr (Sum.inl (26, 19)),
    Sum.inr (Sum.inl (26, 31)),
    Sum.inr (Sum.inl (133, 52)),
    Sum.inr (Sum.inl (126, 59)),
    Sum.inr (Sum.inl (128, 22)),
    Sum.inr (Sum.inl (132, 27)),
    Sum.inr (Sum.inl (128, 14)),
    Sum.inr (Sum.inl (133, 10)),
    Sum.inr (Sum.inl (126, 27)),
    Sum.inr (Sum.inl (132, 37)),
    Sum.inr (Sum.inl (6, 37)),
    Sum.inr (Sum.inl (6, 21)),
    Sum.inr (Sum.inl (26, 23)),
    Sum.inr (Sum.inl (6, 53)),
    Sum.inr (Sum.inl (128, 30)),
    Sum.inr (Sum.inl (126, 58)),
    Sum.inr (Sum.inl (132, 4)),
    Sum.inr (Sum.inl (133, 37)),
    Sum.inr (Sum.inl (215, 35)),
    Sum.inr (Sum.inl (209, 13)),
    Sum.inr (Sum.inl (152, 39)),
    Sum.inr (Sum.inl (175, 62)),
    Sum.inr (Sum.inl (40, 44)),
    Sum.inr (Sum.inl (20, 10)),
    Sum.inr (Sum.inl (40, 38)),
    Sum.inr (Sum.inl (40, 36)),
    Sum.inr (Sum.inl (215, 50)),
    Sum.inr (Sum.inl (152, 55)),
    Sum.inr (Sum.inl (175, 46)),
    Sum.inr (Sum.inl (209, 44)),
    Sum.inr (Sum.inl (175, 44)),
    Sum.inr (Sum.inl (215, 34)),
    Sum.inr (Sum.inl (152, 35)),
    Sum.inr (Sum.inl (209, 45)),
    Sum.inr (Sum.inl (20, 42)),
    Sum.inr (Sum.inl (20, 26)),
    Sum.inr (Sum.inl (40, 46)),
    Sum.inr (Sum.inl (20, 58)),
    Sum.inr (Sum.inl (175, 60)),
    Sum.inr (Sum.inl (152, 51)),
    Sum.inr (Sum.inl (209, 12)),
    Sum.inr (Sum.inl (215, 51))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock080Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨20480 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock080InputMaskData : ℕ :=
  sixthHex% [
    "ed1b90db1b90c01390b61390d1d390cfd390e8d390b6d390c9b390e3b390",
    "dcb390b6b390f58b90f78b90f48390b68390fa9b90f29390fe9b90b69390",
    "866390a66b90966b90f66390e2d34fd4db4fcfd34fb9db4fde1b4fc01b4f",
    "e71b4fb91b4fc6734fec7b4fd3734fb97b4ffa4b4ff84b4ffb4b4fb94b4f",
    "f55b4ffd5b4ff1534fb9534f89a34fa9ab4f99ab4ff9a34f92334ea43b4e",
    "bf334ec93b4eaefb4eb0fb4e97fb4ec9fb4eb6934e9c9b4ea3934ec99b4e",
    "8aa34e88a34e8ba34ec9a34e85bb4e8dbb4e81b34ec9b34ef94b4ed9434e",
    "e9434e894b4e870b4db1034daa0b4ddc034dbbc34da5c34d82c34ddcc34d",
    "a3a34d89ab4db6a34ddcab4d9f934d9d934d9e934ddc934d90834d98834d",
    "948b4ddc8b4dec734dcc7b4dfc7b4d9c734db7eb4c81e34c9aeb4cece34c",
    "8b234c95234cb2234cec234c93434cb94b4c86434cec4b4caf7b4cad7b4c",
    "ae7b4cec7b4ca0634ca8634ca46b4cec6b4cdc9b4cfc934ccc934cac9b4c",
    "92634ba46b4bbf634bc96b4baea34bb0a34b97a34bc9a34bb6c34b9ccb4b",
    "a3c34bc9cb4b8afb4b88fb4b8bfb4bc9fb4b85eb4b8deb4b81e34bc9e34b",
    "f91b4bd9134be9134b891b4ba2834a948b4a8f834af98b4a9e434a80434a",
    "a7434af9434a86234aac2b4a93234af92b4aba134ab8134abb134af9134a",
    "b50b4abd0b4ab1034af9034ac9f34ae9fb4ad9fb4ab9f34ab7bb4981b349",
    "9abb49ecb3498b7b49957b49b27b49ec7b49931349b91b49861349ec1b49",
    "af2349ad2349ae2349ec2349a03349a83349a43b49ec3b49dccb49fcc349",
    "ccc349accb49c75b48f15348ea5b489c5348fb9b48e59b48c29b489c9b48",
    "e3f348c9fb48f6f3489cfb48dfcb48ddcb48decb489ccb48d0d348d8d348",
    "d4db489cdb48ac23488c2b48bc2b48dc2348bfa34789ab4792a347e4ab47",
    "8363479d6347ba6347e463479b0b47b103478e0b47e40347a73347a53347",
    "a63347e43347a82347a02347ac2b47e42b47d4d347f4db47c4db47a4d347",
    "8f4346b94b46a24346d44b46b38346ad83468a8346d48346abeb4681e346",
    "beeb46d4e34697db4695db4696db46d4db46"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock080InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock080InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock080OutputMaskData : ℕ :=
  sixthHex% [
    "552aa1726b900eb0b05cf18a3226e41926ef0b26e45526e41183902d10b0",
    "15c2a15c518a5cf3906c218a3a28b07ffaa15d2eef2466ef6c2ee46066ef",
    "6c898a1980b03f13903f1aa130fb4f66fa7e1a215e39206457f70a7cf701",
    "6ef70a30f70a05127e48c15e01534f39806448627e78b0645ff95e1a2b4f",
    "49bf0141b70109ff0a74f7017818640d115e2b827e2b8b4f55206e03215f",
    "7ffa7f5cfb45322c2b192c200b2c2b552c2b60c95f2d1a7f64886e5c5b45",
    "5cf95f6c2b454b627f0eb06e2c6420246c206c242b112c206c8345198a7f",
    "3f195f3f106e08215c5e206d22fb4d01fa776f2d19442d12562d19082d19",
    "4c886d015b4d48c95c701a7770b86d406a7767234d22f15c716512796d12",
    "3125194c2d12318277448b4d62186d62115c18fa764efb4732206711215d",
    "7ff63354f63846f63318f6335c534711806758127660c15d11234721f15d",
    "06b867436a7661be3869b63821fe335cf63850195d251067038347038a76",
    "fdd7b4abd685d70da5f40c9feb9bf1c09bfad29bf18c9bf1c83e8585eda5",
    "cc7fb4f4ac9f854e85b59c9f92d5a5d707b48493fa8c9bfac4d3f1b9dbfa",
    "c4749fb17da597ee8597e7b4ed0c9ebb0dafc7d68fe4d7b5fb40dbd040d0",
    "c240db9c40dbd8e5af95368fdca49ee477b5e4d5afd407b5f34e8fb69c9e",
    "9448d09c40d0d408dba900d0a5efb5d0e68ff675aff67c9eb00dace60c9d",
    "9ad7bdb9d687a641e98d41e29f41e9c141e9f4a49db977bdf0e5acc83687",
    "c8949df84687df0fbd9addacc949e2c141e28909e9f401e2f8ee878de7bd",
    "ab749dab7dacd5d68d83d7bcff0c9cdc0da6c39ac8e89ac3fa9ac8a49ac8",
    "917fbcdcac9c953e8dadeda6dc0fbcecdda6cb949c8e468dac92c3a49ac3",
    "ecd2c891dac3ec75a6997c9cbfefbcbfe68d50fa7606fb477a206759215d",
    "46b6336db6387fb63321b63314534759806710127628c15d59234769f15d",
    "4eb8670b6a7658fe3850f63818be3365b63818195d6d10674b83474b8a76",
    "40215c16206d6afb4d49fa77566d197d6d126f6d19316d1904886d495b4d",
    "00c95c381a7738b86d086a772f234d6af15c"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock080OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock080OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock080InputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock080InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock080InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock080OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df96175d7df8617df7df85f7e17e17e185f7e196175d8617df85f85f",
    "7df7df7e185f85f85f96175d85f7e17df8617df7df7e17e17e185f6df8e3",
    "8617df7e17e18618617e185f85f85f96175d7e185f7df8617df7df85f85f",
    "7df85f6e18e37df7e17e18617e186186185f7df7e16e18e37e17df86185f",
    "7e18618617e18617e195f75d7df7e185f7df85f7df86185f86185f95f75d",
    "7e17df7df7e185f7df8617e185f85f96175d7e185f7df8617df7df85f85f",
    "7e185f6df8e38617df7e17e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock080OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock080OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block080_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock080Input a) =
      generatedSixthXiShortBlock080InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock080Output a) =
      generatedSixthXiShortBlock080OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock080Input a) =
      generatedSixthXiShortBlock080InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock080Output a) =
      generatedSixthXiShortBlock080OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block080_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock080InputMask a) =
      generatedSixthXiShortBlock080OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock080InputMask a)) *
      generatedSixthXiShortBlock080InputNumerator a =
        generatedSixthXiShortBlock080OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block080_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock080Input a
    let y := generatedSixthXiShortBlock080Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block080_cache a
  have hs := generatedSixth_xi_short_block080_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block080_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock080Input a
    let y := generatedSixthXiShortBlock080Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block080_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block080_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock080Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block080_certificate a).1
    (generatedSixth_xi_short_block080_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
