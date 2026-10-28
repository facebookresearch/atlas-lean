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
def generatedSixthXiShortBlock045Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (305, 10)),
    Sum.inr (Sum.inr (228, 3)),
    Sum.inr (Sum.inr (314, 10)),
    Sum.inr (Sum.inr (239, 3)),
    Sum.inr (Sum.inr (47, 10)),
    Sum.inr (Sum.inr (506, 3)),
    Sum.inr (Sum.inr (36, 10)),
    Sum.inr (Sum.inr (497, 3)),
    Sum.inr (Sum.inr (36, 12)),
    Sum.inr (Sum.inr (497, 20)),
    Sum.inr (Sum.inr (47, 12)),
    Sum.inr (Sum.inr (506, 20)),
    Sum.inr (Sum.inr (314, 12)),
    Sum.inr (Sum.inr (239, 20)),
    Sum.inr (Sum.inr (305, 12)),
    Sum.inr (Sum.inr (228, 20)),
    Sum.inr (Sum.inr (443, 12)),
    Sum.inr (Sum.inr (110, 20)),
    Sum.inr (Sum.inr (432, 12)),
    Sum.inr (Sum.inr (101, 20)),
    Sum.inr (Sum.inr (165, 12)),
    Sum.inr (Sum.inr (368, 20)),
    Sum.inr (Sum.inr (174, 12)),
    Sum.inr (Sum.inr (379, 20)),
    Sum.inr (Sum.inr (379, 12)),
    Sum.inr (Sum.inr (174, 20)),
    Sum.inr (Sum.inr (368, 12)),
    Sum.inr (Sum.inr (165, 20)),
    Sum.inr (Sum.inr (101, 12)),
    Sum.inr (Sum.inr (432, 20)),
    Sum.inr (Sum.inr (110, 12)),
    Sum.inr (Sum.inr (443, 20)),
    Sum.inr (Sum.inr (228, 12)),
    Sum.inr (Sum.inr (305, 20)),
    Sum.inr (Sum.inr (239, 12)),
    Sum.inr (Sum.inr (314, 20)),
    Sum.inr (Sum.inr (506, 12)),
    Sum.inr (Sum.inr (47, 20)),
    Sum.inr (Sum.inr (497, 12)),
    Sum.inr (Sum.inr (36, 20)),
    Sum.inr (Sum.inr (504, 20)),
    Sum.inr (Sum.inr (370, 3)),
    Sum.inr (Sum.inr (172, 20)),
    Sum.inr (Sum.inr (38, 3)),
    Sum.inr (Sum.inr (370, 10)),
    Sum.inr (Sum.inr (504, 12)),
    Sum.inr (Sum.inr (38, 10)),
    Sum.inr (Sum.inr (172, 12)),
    Sum.inr (Sum.inr (370, 12)),
    Sum.inr (Sum.inr (504, 10)),
    Sum.inr (Sum.inr (38, 12)),
    Sum.inr (Sum.inr (172, 10)),
    Sum.inr (Sum.inr (504, 3)),
    Sum.inr (Sum.inr (370, 20)),
    Sum.inr (Sum.inr (172, 3)),
    Sum.inr (Sum.inr (38, 20)),
    Sum.inr (Sum.inr (167, 20)),
    Sum.inr (Sum.inr (45, 3)),
    Sum.inr (Sum.inr (499, 20)),
    Sum.inr (Sum.inr (377, 3)),
    Sum.inr (Sum.inr (45, 10)),
    Sum.inr (Sum.inr (167, 12)),
    Sum.inr (Sum.inr (377, 10)),
    Sum.inr (Sum.inr (499, 12)),
    Sum.inr (Sum.inr (45, 12)),
    Sum.inr (Sum.inr (167, 10)),
    Sum.inr (Sum.inr (377, 12)),
    Sum.inr (Sum.inr (499, 10)),
    Sum.inr (Sum.inr (167, 3)),
    Sum.inr (Sum.inr (45, 20)),
    Sum.inr (Sum.inr (499, 3)),
    Sum.inr (Sum.inr (377, 20)),
    Sum.inr (Sum.inr (312, 20)),
    Sum.inr (Sum.inr (434, 3)),
    Sum.inr (Sum.inr (108, 20)),
    Sum.inr (Sum.inr (230, 3)),
    Sum.inr (Sum.inr (434, 10)),
    Sum.inr (Sum.inr (312, 12)),
    Sum.inr (Sum.inr (230, 10)),
    Sum.inr (Sum.inr (108, 12)),
    Sum.inr (Sum.inr (434, 12)),
    Sum.inr (Sum.inr (312, 10)),
    Sum.inr (Sum.inr (230, 12)),
    Sum.inr (Sum.inr (108, 10)),
    Sum.inr (Sum.inr (312, 3)),
    Sum.inr (Sum.inr (434, 20)),
    Sum.inr (Sum.inr (108, 3)),
    Sum.inr (Sum.inr (230, 20)),
    Sum.inr (Sum.inr (103, 20)),
    Sum.inr (Sum.inr (237, 3)),
    Sum.inr (Sum.inr (307, 20)),
    Sum.inr (Sum.inr (441, 3)),
    Sum.inr (Sum.inr (237, 10)),
    Sum.inr (Sum.inr (103, 12)),
    Sum.inr (Sum.inr (441, 10)),
    Sum.inr (Sum.inr (307, 12)),
    Sum.inr (Sum.inr (237, 12)),
    Sum.inr (Sum.inr (103, 10)),
    Sum.inr (Sum.inr (441, 12)),
    Sum.inr (Sum.inr (307, 10)),
    Sum.inr (Sum.inr (103, 3)),
    Sum.inr (Sum.inr (237, 20)),
    Sum.inr (Sum.inr (307, 3)),
    Sum.inr (Sum.inr (441, 20)),
    Sum.inr (Sum.inr (83, 12)),
    Sum.inr (Sum.inr (25, 20)),
    Sum.inr (Sum.inr (83, 10)),
    Sum.inr (Sum.inr (25, 3)),
    Sum.inr (Sum.inr (397, 20)),
    Sum.inr (Sum.inr (455, 12)),
    Sum.inr (Sum.inr (397, 3)),
    Sum.inr (Sum.inr (455, 10)),
    Sum.inr (Sum.inr (390, 20)),
    Sum.inr (Sum.inr (460, 12)),
    Sum.inr (Sum.inr (390, 3)),
    Sum.inr (Sum.inr (460, 10)),
    Sum.inr (Sum.inr (88, 12)),
    Sum.inr (Sum.inr (18, 20)),
    Sum.inr (Sum.inr (88, 10)),
    Sum.inr (Sum.inr (18, 3)),
    Sum.inr (Sum.inr (152, 20)),
    Sum.inr (Sum.inr (210, 12)),
    Sum.inr (Sum.inr (152, 3)),
    Sum.inr (Sum.inr (210, 10)),
    Sum.inr (Sum.inr (326, 12)),
    Sum.inr (Sum.inr (268, 20)),
    Sum.inr (Sum.inr (326, 10)),
    Sum.inr (Sum.inr (268, 3)),
    Sum.inr (Sum.inr (333, 12)),
    Sum.inr (Sum.inr (263, 20)),
    Sum.inr (Sum.inr (333, 10)),
    Sum.inr (Sum.inr (263, 3)),
    Sum.inr (Sum.inr (147, 20)),
    Sum.inr (Sum.inr (217, 12)),
    Sum.inr (Sum.inr (147, 3)),
    Sum.inr (Sum.inr (217, 10)),
    Sum.inr (Sum.inr (83, 3)),
    Sum.inr (Sum.inr (25, 10)),
    Sum.inr (Sum.inr (83, 20)),
    Sum.inr (Sum.inr (25, 12)),
    Sum.inr (Sum.inr (397, 10)),
    Sum.inr (Sum.inr (455, 3)),
    Sum.inr (Sum.inr (397, 12)),
    Sum.inr (Sum.inr (455, 20)),
    Sum.inr (Sum.inr (390, 10)),
    Sum.inr (Sum.inr (460, 3)),
    Sum.inr (Sum.inr (390, 12)),
    Sum.inr (Sum.inr (460, 20)),
    Sum.inr (Sum.inr (88, 3)),
    Sum.inr (Sum.inr (18, 10)),
    Sum.inr (Sum.inr (88, 20)),
    Sum.inr (Sum.inr (18, 12)),
    Sum.inr (Sum.inr (152, 10)),
    Sum.inr (Sum.inr (210, 3)),
    Sum.inr (Sum.inr (152, 12)),
    Sum.inr (Sum.inr (210, 20)),
    Sum.inr (Sum.inr (326, 3)),
    Sum.inr (Sum.inr (268, 10)),
    Sum.inr (Sum.inr (326, 20)),
    Sum.inr (Sum.inr (268, 12)),
    Sum.inr (Sum.inr (333, 3)),
    Sum.inr (Sum.inr (263, 10)),
    Sum.inr (Sum.inr (333, 20)),
    Sum.inr (Sum.inr (263, 12)),
    Sum.inr (Sum.inr (147, 10)),
    Sum.inr (Sum.inr (217, 3)),
    Sum.inr (Sum.inr (147, 12)),
    Sum.inr (Sum.inr (217, 20)),
    Sum.inr (Sum.inr (496, 3)),
    Sum.inr (Sum.inr (238, 3)),
    Sum.inr (Sum.inr (175, 3)),
    Sum.inr (Sum.inr (433, 3)),
    Sum.inr (Sum.inr (111, 3)),
    Sum.inr (Sum.inr (369, 3)),
    Sum.inr (Sum.inr (304, 3)),
    Sum.inr (Sum.inr (46, 3)),
    Sum.inr (Sum.inr (507, 3)),
    Sum.inr (Sum.inr (229, 3)),
    Sum.inr (Sum.inr (164, 3)),
    Sum.inr (Sum.inr (442, 3)),
    Sum.inr (Sum.inr (100, 3)),
    Sum.inr (Sum.inr (378, 3)),
    Sum.inr (Sum.inr (315, 3)),
    Sum.inr (Sum.inr (37, 3)),
    Sum.inr (Sum.inr (37, 10)),
    Sum.inr (Sum.inr (315, 10)),
    Sum.inr (Sum.inr (378, 10)),
    Sum.inr (Sum.inr (100, 10)),
    Sum.inr (Sum.inr (442, 10)),
    Sum.inr (Sum.inr (164, 10)),
    Sum.inr (Sum.inr (229, 10)),
    Sum.inr (Sum.inr (507, 10)),
    Sum.inr (Sum.inr (46, 10)),
    Sum.inr (Sum.inr (304, 10)),
    Sum.inr (Sum.inr (369, 10)),
    Sum.inr (Sum.inr (111, 10)),
    Sum.inr (Sum.inr (433, 10)),
    Sum.inr (Sum.inr (175, 10)),
    Sum.inr (Sum.inr (238, 10)),
    Sum.inr (Sum.inr (496, 10)),
    Sum.inr (Sum.inr (37, 12)),
    Sum.inr (Sum.inr (315, 12)),
    Sum.inr (Sum.inr (378, 12)),
    Sum.inr (Sum.inr (100, 12)),
    Sum.inr (Sum.inr (442, 12)),
    Sum.inr (Sum.inr (164, 12)),
    Sum.inr (Sum.inr (229, 12)),
    Sum.inr (Sum.inr (507, 12)),
    Sum.inr (Sum.inr (46, 12)),
    Sum.inr (Sum.inr (304, 12)),
    Sum.inr (Sum.inr (369, 12)),
    Sum.inr (Sum.inr (111, 12)),
    Sum.inr (Sum.inr (433, 12)),
    Sum.inr (Sum.inr (175, 12)),
    Sum.inr (Sum.inr (238, 12)),
    Sum.inr (Sum.inr (496, 12)),
    Sum.inr (Sum.inr (496, 20)),
    Sum.inr (Sum.inr (238, 20)),
    Sum.inr (Sum.inr (175, 20)),
    Sum.inr (Sum.inr (433, 20)),
    Sum.inr (Sum.inr (111, 20)),
    Sum.inr (Sum.inr (369, 20)),
    Sum.inr (Sum.inr (304, 20)),
    Sum.inr (Sum.inr (46, 20)),
    Sum.inr (Sum.inr (507, 20)),
    Sum.inr (Sum.inr (229, 20)),
    Sum.inr (Sum.inr (164, 20)),
    Sum.inr (Sum.inr (442, 20)),
    Sum.inr (Sum.inr (100, 20)),
    Sum.inr (Sum.inr (378, 20)),
    Sum.inr (Sum.inr (315, 20)),
    Sum.inr (Sum.inr (37, 20)),
    Sum.inr (Sum.inr (64, 10)),
    Sum.inr (Sum.inr (10, 20)),
    Sum.inr (Sum.inr (64, 12)),
    Sum.inr (Sum.inr (10, 3)),
    Sum.inr (Sum.inr (414, 20)),
    Sum.inr (Sum.inr (468, 10)),
    Sum.inr (Sum.inr (414, 3)),
    Sum.inr (Sum.inr (468, 12)),
    Sum.inr (Sum.inr (405, 20)),
    Sum.inr (Sum.inr (479, 10)),
    Sum.inr (Sum.inr (405, 3)),
    Sum.inr (Sum.inr (479, 12)),
    Sum.inr (Sum.inr (75, 10)),
    Sum.inr (Sum.inr (1, 20)),
    Sum.inr (Sum.inr (75, 12)),
    Sum.inr (Sum.inr (1, 3)),
    Sum.inr (Sum.inr (64, 3)),
    Sum.inr (Sum.inr (10, 12)),
    Sum.inr (Sum.inr (64, 20)),
    Sum.inr (Sum.inr (10, 10)),
    Sum.inr (Sum.inr (414, 12)),
    Sum.inr (Sum.inr (468, 3)),
    Sum.inr (Sum.inr (414, 10)),
    Sum.inr (Sum.inr (468, 20))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock045Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨11520 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock045InputMaskData : ℕ :=
  sixthHex% [
    "4fd18a5fa18a7fa18a6fd98a07518a17298a37298a27598a03f18a13818a",
    "33818a23f98a4b718a5b098a7b098a6b798a4f718a5f098a7f098a6f798a",
    "07f98a17898a37898a27f18a70676a49d76a29d76a106f6a19d76a206f6a",
    "406f6a79df6a41276a789f6a189f6a212f6a289f6a112f6a712f6a48976a",
    "48376a718f6a118f6a283f6a218f6a183f6a783f6a41876a797f6a40cf6a",
    "20cf6a19776a10cf6a29776a49776a70c76a09076a30bf6a50bf6a690f6a",
    "60bf6a590f6a390f6a00b76a384f6a01ff6a61ff6a58476a51ff6a68476a",
    "08476a31f76a315f6a08ef6a68ef6a51576a58ef6a61576a01576a38e76a",
    "001f6a39a76a59a76a60176a69a76a50176a30176a09af6a6cf9e97c89e9",
    "5c89e94cf1e92479e93401e91401e90471e92879e93801e91801e90871e9",
    "60f1e97081e95081e940f9e96c69e97c11e95c11e94c61e924e1e93491e9",
    "1491e904e9e928e1e93891e91891e908e9e96061e97019e95019e94069e9",
    "2d69e93d11e91d11e90d61e965e1e97591e95591e945e9e969e1e97991e9",
    "5991e949e9e92161e93119e91119e90169e92df1e93d81e91d81e90df9e9",
    "6571e97509e95509e94579e96971e97909e95909e94979e921f9e93189e9",
    "1189e901f1e94faf6212df626a2f62375762633f623e476246b7621bc762",
    "220f627f77620787625af7620e976253e7622b1762766f625b6f62061762",
    "7ee76223976277f7622a87625277620f0f6236c7626bb7621347624e3f62",
    "1a5762472f623fdf6262af6254af6209d7627127622c5762783762254762",
    "5db76200cf623907626477621c876241ff6215976248ef62301f626d6f62",
    "4067621d176265e762389f626cf762318f62497f62140f622dc76270bf62",
    "084f62553f62015f625c2f6224df6279a762416f6b08df6b702f6b39976b",
    "383f6b71876b09776b40c76b7a3f6b33876b4b776b02c76b03676b4ad76b",
    "32276b7b9f6b7b3f6b32876b4a776b03c76b02676b4bd76b33276b7a9f6b",
    "40676b09d76b71276b389f6b39376b708f6b087f6b41cf6b380f6b71b76b",
    "09476b40f76b41576b08e76b70176b39af6b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock045InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock045InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock045OutputMaskData : ℕ :=
  sixthHex% [
    "80df64b4ee5eb0a764f5d65ec1400a84313080780ab44930f0e001c4d13b",
    "c0980185e93bb17f6ff40e55f0476fc47655807f64c50e5ec14764f5765e",
    "b0a00a84913080d80ac5a930a398b585a4fbf4edcaa39184d27eea8502a4",
    "f44b95d277dba7d0bef0acf081e5c1a7d98fa776e1814aaff0039ea77fd0",
    "a7dfd0f0a39e81eaafa7d6e1a7798f8145c1f00cf0a770bed2d7dbf4eb95",
    "85a2a4d2deeaa33184f44dca8504fba338b5e6efd0b1939ec0daafe6e6e1",
    "e6498fc075c1b13cf0e640be93e7dbb5db95c492a493eeeae20184b57dca",
    "c434fbe208b593e8b5b5d4fbc49dca93e184e20eeab572a4c43b95e207db",
    "97a0bec0dcf0b195c197a98f9706e1b13aafc0739e970fd0ecb349d88273",
    "dccb4999ba73ad2c27e85d1dec1427d8251d94242cd15516d51c2ce12d16",
    "a4fb4290ca78948342d1f278cfb8628ac9588e8062bab158ff670ccb5636",
    "cf1f0c8a6e36c66f07f25e3df61707b3663d87f069c28153c6c869f2f953",
    "ad2349e85273ec1b49d82a739dfc27a9cd1dad8427e8f51da4f42c90c516",
    "948c2cd1fd16e56b42a01a78a45342906278ff6862cb5958cf10628a6158",
    "bef70cfb8636ffcf0ccbfe3687ff07c28e3dc6c707f2f63db72069831153",
    "875869c22953ec7ee983dcf3f23b9decd987f234f3ecd6e99d3187f2939d",
    "b304f3ade6e9dc0187b3a39ddc0ee9b3acf3c24b9ddca987f67396e8918c",
    "9976e2f6d4f899798cf6db96873cf899dee2d8498cb7eb96c60cf8d8eee2",
    "c60396d8e18ca906e2c6a4f8e1e5c9ff07d38ee0bde142a78eefd3e14dc9",
    "90aaa78e48bdcfdfd3a07dc9d19aa7cf78bdd195c9cf77d3be90bdd132a7",
    "8aa8b6e50aac94edc28a0fd894e2ac8a00b6fbe7d89445c2d5d2accb30b6",
    "bad7d8d575c2bad8b6d57aaca49dc2ba7fd8e078b495d7d1e430bfe0dfda",
    "86a4fa824b9ff3acf1860394c376ebc7998eb67ee0c3d185d4eaa5a145c0",
    "d0a2aed44dcbd4edcbd002aea1e5c0d44aa5c37185b6dee0c7398ec3d6eb",
    "86a394f30cf182eb9f8604fae07fdae490bf9577d1e0d8b4a50fd1a1e0b4",
    "d007daa5a8bfb2939fc73cfab6db94b234f1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock045OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock045OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock045InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df7df7e185f7df7df7e17df7e17e18617e17df7df85f7df85f85f861",
    "7df85f85f86185f8618617e17df85f85f86185f8618617e185f8618617e1",
    "8617e17e17df7e186186185f7df7e17e186186185f85f7df7e186186185f",
    "86185f85f7df7e186186185f85f7df7df7e186185f85f7df7df7e17e1861",
    "7e186186185f7e186186185f86185f85f7df7e186186185f86185f85f7df",
    "86185f85f7df85f7df7df7e186185f85f7df7e186186185f85f7df7df7e1",
    "86185f85f7df85f7df7df7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock045InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock045InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock045OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df86185f85f7df86185f7df7e185f7df7e186186185f86185f85f7df",
    "86185f85f7df85f7df7df7e186185f85f7df85f7df7df7e185f7df7df7e1",
    "7df7e17e18617df85f85f8617e17df7df85f7e17df7df85f8617e17e17df",
    "85f8618617e17df85f85f8617df85f85f8617e17df7df85f7e186186185f",
    "86185f85f7df7df7e17e18617e186186185f86185f85f7df85f7df7df7e1",
    "7e186186185f86185f85f7df7df85f7e17df85f8617df85f85f8617df85f",
    "8617e185f8617e17df8617e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock045OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock045OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block045_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock045Input a) =
      generatedSixthXiShortBlock045InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock045Output a) =
      generatedSixthXiShortBlock045OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock045Input a) =
      generatedSixthXiShortBlock045InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock045Output a) =
      generatedSixthXiShortBlock045OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block045_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock045InputMask a) =
      generatedSixthXiShortBlock045OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock045InputMask a)) *
      generatedSixthXiShortBlock045InputNumerator a =
        generatedSixthXiShortBlock045OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block045_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock045Input a
    let y := generatedSixthXiShortBlock045Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block045_cache a
  have hs := generatedSixth_xi_short_block045_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block045_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock045Input a
    let y := generatedSixthXiShortBlock045Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block045_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block045_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock045Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block045_certificate a).1
    (generatedSixth_xi_short_block045_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
