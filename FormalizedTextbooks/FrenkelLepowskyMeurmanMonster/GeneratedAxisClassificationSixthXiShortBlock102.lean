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
def generatedSixthXiShortBlock102Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (133, 49)),
    Sum.inr (Sum.inl (132, 46)),
    Sum.inr (Sum.inl (126, 14)),
    Sum.inr (Sum.inl (128, 3)),
    Sum.inr (Sum.inl (26, 7)),
    Sum.inr (Sum.inl (6, 3)),
    Sum.inr (Sum.inl (26, 15)),
    Sum.inr (Sum.inl (26, 3)),
    Sum.inr (Sum.inl (133, 30)),
    Sum.inr (Sum.inl (126, 47)),
    Sum.inr (Sum.inl (128, 19)),
    Sum.inr (Sum.inl (132, 15)),
    Sum.inr (Sum.inl (128, 11)),
    Sum.inr (Sum.inl (133, 32)),
    Sum.inr (Sum.inl (126, 15)),
    Sum.inr (Sum.inl (132, 49)),
    Sum.inr (Sum.inl (6, 35)),
    Sum.inr (Sum.inl (6, 19)),
    Sum.inr (Sum.inl (26, 11)),
    Sum.inr (Sum.inl (6, 51)),
    Sum.inr (Sum.inl (128, 27)),
    Sum.inr (Sum.inl (126, 46)),
    Sum.inr (Sum.inl (132, 16)),
    Sum.inr (Sum.inl (133, 15)),
    Sum.inr (Sum.inl (88, 33)),
    Sum.inr (Sum.inl (87, 62)),
    Sum.inr (Sum.inl (81, 12)),
    Sum.inr (Sum.inl (83, 50)),
    Sum.inr (Sum.inl (23, 24)),
    Sum.inr (Sum.inl (3, 52)),
    Sum.inr (Sum.inl (23, 16)),
    Sum.inr (Sum.inl (23, 28)),
    Sum.inr (Sum.inl (88, 48)),
    Sum.inr (Sum.inl (81, 19)),
    Sum.inr (Sum.inl (83, 32)),
    Sum.inr (Sum.inl (87, 33)),
    Sum.inr (Sum.inl (83, 48)),
    Sum.inr (Sum.inl (88, 14)),
    Sum.inr (Sum.inl (81, 55)),
    Sum.inr (Sum.inl (87, 31)),
    Sum.inr (Sum.inl (3, 20)),
    Sum.inr (Sum.inl (3, 36)),
    Sum.inr (Sum.inl (23, 20)),
    Sum.inr (Sum.inl (3, 4)),
    Sum.inr (Sum.inl (83, 34)),
    Sum.inr (Sum.inl (81, 40)),
    Sum.inr (Sum.inl (87, 0)),
    Sum.inr (Sum.inl (88, 31)),
    Sum.inr (Sum.inl (196, 50)),
    Sum.inr (Sum.inl (195, 60)),
    Sum.inr (Sum.inl (144, 49)),
    Sum.inr (Sum.inl (167, 17)),
    Sum.inr (Sum.inl (32, 57)),
    Sum.inr (Sum.inl (12, 61)),
    Sum.inr (Sum.inl (32, 49)),
    Sum.inr (Sum.inl (32, 61)),
    Sum.inr (Sum.inl (196, 35)),
    Sum.inr (Sum.inl (144, 17)),
    Sum.inr (Sum.inl (167, 51)),
    Sum.inr (Sum.inl (195, 28)),
    Sum.inr (Sum.inl (167, 49)),
    Sum.inr (Sum.inl (196, 12)),
    Sum.inr (Sum.inl (144, 19)),
    Sum.inr (Sum.inl (195, 52)),
    Sum.inr (Sum.inl (12, 29)),
    Sum.inr (Sum.inl (12, 45)),
    Sum.inr (Sum.inl (32, 53)),
    Sum.inr (Sum.inl (12, 13)),
    Sum.inr (Sum.inl (167, 19)),
    Sum.inr (Sum.inl (144, 51)),
    Sum.inr (Sum.inl (195, 20)),
    Sum.inr (Sum.inl (196, 29)),
    Sum.inr (Sum.inr (48, 0)),
    Sum.inr (Sum.inr (113, 22)),
    Sum.inr (Sum.inr (177, 14)),
    Sum.inr (Sum.inr (251, 10)),
    Sum.inr (Sum.inr (302, 18)),
    Sum.inr (Sum.inr (293, 5)),
    Sum.inr (Sum.inr (302, 7)),
    Sum.inr (Sum.inr (302, 6)),
    Sum.inr (Sum.inr (48, 8)),
    Sum.inr (Sum.inr (177, 21)),
    Sum.inr (Sum.inr (251, 3)),
    Sum.inr (Sum.inr (113, 15)),
    Sum.inr (Sum.inr (251, 20)),
    Sum.inr (Sum.inr (48, 13)),
    Sum.inr (Sum.inr (177, 2)),
    Sum.inr (Sum.inr (113, 11)),
    Sum.inr (Sum.inr (293, 16)),
    Sum.inr (Sum.inr (293, 17)),
    Sum.inr (Sum.inr (302, 4)),
    Sum.inr (Sum.inr (293, 19)),
    Sum.inr (Sum.inr (251, 12)),
    Sum.inr (Sum.inr (177, 9)),
    Sum.inr (Sum.inr (113, 1)),
    Sum.inr (Sum.inr (48, 23)),
    Sum.inr (Sum.inr (250, 8)),
    Sum.inr (Sum.inr (187, 15)),
    Sum.inr (Sum.inr (123, 21)),
    Sum.inr (Sum.inr (49, 3)),
    Sum.inr (Sum.inr (484, 18)),
    Sum.inr (Sum.inr (495, 5)),
    Sum.inr (Sum.inr (484, 7)),
    Sum.inr (Sum.inr (484, 6)),
    Sum.inr (Sum.inr (250, 0)),
    Sum.inr (Sum.inr (123, 14)),
    Sum.inr (Sum.inr (49, 10)),
    Sum.inr (Sum.inr (187, 22)),
    Sum.inr (Sum.inr (49, 12)),
    Sum.inr (Sum.inr (250, 23)),
    Sum.inr (Sum.inr (123, 9)),
    Sum.inr (Sum.inr (187, 1)),
    Sum.inr (Sum.inr (495, 16)),
    Sum.inr (Sum.inr (495, 17)),
    Sum.inr (Sum.inr (484, 4)),
    Sum.inr (Sum.inr (495, 19)),
    Sum.inr (Sum.inr (49, 20)),
    Sum.inr (Sum.inr (123, 2)),
    Sum.inr (Sum.inr (187, 11)),
    Sum.inr (Sum.inr (250, 13)),
    Sum.inr (Sum.inr (179, 13)),
    Sum.inr (Sum.inr (242, 11)),
    Sum.inr (Sum.inr (50, 2)),
    Sum.inr (Sum.inr (120, 20)),
    Sum.inr (Sum.inr (429, 18)),
    Sum.inr (Sum.inr (422, 5)),
    Sum.inr (Sum.inr (429, 7)),
    Sum.inr (Sum.inr (429, 6)),
    Sum.inr (Sum.inr (179, 23)),
    Sum.inr (Sum.inr (50, 9)),
    Sum.inr (Sum.inr (120, 12)),
    Sum.inr (Sum.inr (242, 1)),
    Sum.inr (Sum.inr (120, 10)),
    Sum.inr (Sum.inr (179, 0)),
    Sum.inr (Sum.inr (50, 14)),
    Sum.inr (Sum.inr (242, 22)),
    Sum.inr (Sum.inr (422, 16)),
    Sum.inr (Sum.inr (422, 17)),
    Sum.inr (Sum.inr (429, 4)),
    Sum.inr (Sum.inr (422, 19)),
    Sum.inr (Sum.inr (120, 3)),
    Sum.inr (Sum.inr (50, 21)),
    Sum.inr (Sum.inr (242, 15)),
    Sum.inr (Sum.inr (179, 8)),
    Sum.inr (Sum.inr (114, 23)),
    Sum.inr (Sum.inr (51, 1)),
    Sum.inr (Sum.inr (243, 9)),
    Sum.inr (Sum.inr (185, 12)),
    Sum.inr (Sum.inr (364, 18)),
    Sum.inr (Sum.inr (359, 5)),
    Sum.inr (Sum.inr (364, 7)),
    Sum.inr (Sum.inr (364, 6)),
    Sum.inr (Sum.inr (114, 13)),
    Sum.inr (Sum.inr (243, 2)),
    Sum.inr (Sum.inr (185, 20)),
    Sum.inr (Sum.inr (51, 11)),
    Sum.inr (Sum.inr (185, 3)),
    Sum.inr (Sum.inr (114, 8)),
    Sum.inr (Sum.inr (243, 21)),
    Sum.inr (Sum.inr (51, 15)),
    Sum.inr (Sum.inr (359, 16)),
    Sum.inr (Sum.inr (359, 17)),
    Sum.inr (Sum.inr (364, 4)),
    Sum.inr (Sum.inr (359, 19)),
    Sum.inr (Sum.inr (185, 10)),
    Sum.inr (Sum.inr (243, 14)),
    Sum.inr (Sum.inr (51, 22)),
    Sum.inr (Sum.inr (114, 0)),
    Sum.inr (Sum.inl (196, 62)),
    Sum.inr (Sum.inl (195, 63)),
    Sum.inr (Sum.inl (144, 61)),
    Sum.inr (Sum.inl (167, 29)),
    Sum.inr (Sum.inl (32, 55)),
    Sum.inr (Sum.inl (12, 15)),
    Sum.inr (Sum.inl (32, 63)),
    Sum.inr (Sum.inl (32, 51)),
    Sum.inr (Sum.inl (196, 47)),
    Sum.inr (Sum.inl (144, 29)),
    Sum.inr (Sum.inl (167, 63)),
    Sum.inr (Sum.inl (195, 31)),
    Sum.inr (Sum.inl (167, 61)),
    Sum.inr (Sum.inl (196, 0)),
    Sum.inr (Sum.inl (144, 31)),
    Sum.inr (Sum.inl (195, 55)),
    Sum.inr (Sum.inl (12, 47)),
    Sum.inr (Sum.inl (12, 31)),
    Sum.inr (Sum.inl (32, 59)),
    Sum.inr (Sum.inl (12, 63)),
    Sum.inr (Sum.inl (167, 31)),
    Sum.inr (Sum.inl (144, 63)),
    Sum.inr (Sum.inl (195, 23)),
    Sum.inr (Sum.inl (196, 17)),
    Sum.inr (Sum.inl (88, 45)),
    Sum.inr (Sum.inl (87, 50)),
    Sum.inr (Sum.inl (81, 15)),
    Sum.inr (Sum.inl (83, 62)),
    Sum.inr (Sum.inl (23, 22)),
    Sum.inr (Sum.inl (3, 6)),
    Sum.inr (Sum.inl (23, 30)),
    Sum.inr (Sum.inl (23, 18)),
    Sum.inr (Sum.inl (88, 60)),
    Sum.inr (Sum.inl (81, 16)),
    Sum.inr (Sum.inl (83, 44)),
    Sum.inr (Sum.inl (87, 45)),
    Sum.inr (Sum.inl (83, 60)),
    Sum.inr (Sum.inl (88, 2)),
    Sum.inr (Sum.inl (81, 52)),
    Sum.inr (Sum.inl (87, 19)),
    Sum.inr (Sum.inl (3, 38)),
    Sum.inr (Sum.inl (3, 22)),
    Sum.inr (Sum.inl (23, 26)),
    Sum.inr (Sum.inl (3, 54)),
    Sum.inr (Sum.inl (83, 46)),
    Sum.inr (Sum.inl (81, 43)),
    Sum.inr (Sum.inl (87, 12)),
    Sum.inr (Sum.inl (88, 19)),
    Sum.inr (Sum.inl (133, 61)),
    Sum.inr (Sum.inl (132, 34)),
    Sum.inr (Sum.inl (126, 2)),
    Sum.inr (Sum.inl (128, 0)),
    Sum.inr (Sum.inl (26, 9)),
    Sum.inr (Sum.inl (6, 49)),
    Sum.inr (Sum.inl (26, 1)),
    Sum.inr (Sum.inl (26, 13)),
    Sum.inr (Sum.inl (133, 18)),
    Sum.inr (Sum.inl (126, 35)),
    Sum.inr (Sum.inl (128, 16)),
    Sum.inr (Sum.inl (132, 3)),
    Sum.inr (Sum.inl (128, 8)),
    Sum.inr (Sum.inl (133, 44)),
    Sum.inr (Sum.inl (126, 3)),
    Sum.inr (Sum.inl (132, 61)),
    Sum.inr (Sum.inl (6, 17)),
    Sum.inr (Sum.inl (6, 33)),
    Sum.inr (Sum.inl (26, 5)),
    Sum.inr (Sum.inl (6, 1)),
    Sum.inr (Sum.inl (128, 24)),
    Sum.inr (Sum.inl (126, 34)),
    Sum.inr (Sum.inl (132, 28)),
    Sum.inr (Sum.inl (133, 3)),
    Sum.inr (Sum.inl (210, 48)),
    Sum.inr (Sum.inl (204, 2)),
    Sum.inr (Sum.inl (147, 18)),
    Sum.inr (Sum.inl (170, 50)),
    Sum.inr (Sum.inl (35, 40)),
    Sum.inr (Sum.inl (15, 56)),
    Sum.inr (Sum.inl (35, 32)),
    Sum.inr (Sum.inl (35, 44)),
    Sum.inr (Sum.inl (210, 31)),
    Sum.inr (Sum.inl (147, 0)),
    Sum.inr (Sum.inl (170, 34)),
    Sum.inr (Sum.inl (204, 32)),
    Sum.inr (Sum.inl (170, 32)),
    Sum.inr (Sum.inl (210, 11)),
    Sum.inr (Sum.inl (147, 2)),
    Sum.inr (Sum.inl (204, 63))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock102Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨26112 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock102InputMaskData : ℕ :=
  sixthHex% [
    "b6cf0b9cc70ba3c70bc9c70b8aff0b88ff0b8bff0bc9f70b85e70b8de70b",
    "81e70bc9ef0bf9170bd91f0be91f0b891f0ba2670a94670a8f6f0af9670a",
    "9eaf0a80a70aa7af0af9af0a86cf0aacc70a93c70af9c70abaf70ab8f70a",
    "bbf70af9ff0ab5e70abde70ab1e70af9ef0ac91f0ae9170ad9170ab9170a",
    "9d6f09ab6f09b06709c66f09a1a709bfaf0998a709c6a709b9cf0993c709",
    "acc709c6c70985f70987f70984f709c6ff098aef0982ef098eef09c6e709",
    "f61709d61f09e61f09861f09ed6708db6708c06f08b66708d1af08cfa708",
    "e8af08b6af08c9c708e3cf08dccf08b6cf08f5f708f7f708f4f708b6ff08",
    "fae708f2e708fee708b6ef08861708a61f08961f08f61f089d6f07ab6f07",
    "b06707c66f07a1a707bfaf0798a707c6a707b9cf0793c707acc707c6c707",
    "85ff0787ff0784ff07c6f7078ae70782e7078ee707c6ef07f61707d61f07",
    "e61f07861f07ad6f069b6f06806706f66f0691a7068faf06a8a706f6a706",
    "89cf06a3c7069cc706f6c706b5f706b7f706b4f706f6ff06bae706b2e706",
    "bee706f6ef06c61f06e61706d61706b61706926705a46705bf6f05c96705",
    "aeaf05b0a70597af05c9af05b6cf059cc705a3c705c9c7058af70588f705",
    "8bf705c9ff0585ef058def0581ef05c9e705f91705d91f05e91f05891f05",
    "e26f04d46f04cf6704b96f04dea704c0af04e7a704b9a704c6c704eccf04",
    "d3cf04b9cf04faf704f8f704fbf704b9ff04f5e704fde704f1e704b9ef04",
    "891704a91f04991f04f91f04946703a26703b96f03cf6703a8a703b6af03",
    "91a703cfa703b0c7039acf03a5cf03cfcf038cf7038ef7038df703cfff03",
    "83ef038bef0387ef03cfe703ff1703df1f03ef1f038f1f03e46f02d26f02",
    "c96702bf6f02d8af02c6a702e1af02bfaf02c0cf02eac702d5c702bfc702",
    "fcf702fef702fdf702bfff02f3e702fbe702f7e702bfef028f1702af1f02",
    "9f1f02ff1f02db6701ed6701f66f01806701e7a701f9af01dea70180a701",
    "ffcf01d5c701eac70180c701c3f701c1f701c2f70180ff01ccef01c4ef01",
    "c8ef0180e701b01f01901701a01701c01701"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock102InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock102InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock102OutputMaskData : ℕ :=
  sixthHex% [
    "68315f25e27f1d306e54a34554015f64d345439a7f77086e249c202c9420",
    "159c2b19d420647b4511727f37e15f46a86e09a34f2ee27e52395e713864",
    "6eaf0a34ef0157af0a09af0a4d0a7e00d95e380b4f719864007a7e30a864",
    "17e15e23734f01a70109af0130a70a3cef0130006445095e639a7e12d34f",
    "4b9a766cdb4710006733015d2c963376d6381596334b96337e734733a067",
    "0b727642e15d33034703d15d249867100a76439e384b9638729e337ed638",
    "72395d07306721a34750ea766ae15c4da06d317b4d127a770ded1957ad12",
    "34ed196aed195f086d12db4d2a095c639a7763386d53ea7774a34d40315c",
    "62e5126aed1253e5195fad12220277570b4d71986d00d15ccdb9e2eaf8d3",
    "9623f3b522c9aab5a7f0f5ac93b5a7cdb5a7f850d3b583f38d51e2c4c2c9",
    "c460d3f4b2c9d3fbf3e769e2b4fdacbcf5ac85fda789b5acf41ac98113f3",
    "a780d3d6c9e2e882c3cfc3f2b318d29019e88f8e86d5ce8db68e86e88e86",
    "dd6bf290b8d2a86ac3e1f9e8901bf2a0c9e88780d2b312c391c68d99ce8d",
    "a0c686ac8e8da061e8d568d2f3fbf282b2c3aabbfa8dfacbf121ebd220d1",
    "cdb7bf97f7b4f4b7bfaab7bfee12cba3c1eb9b13fad280d1a362cb93b0d1",
    "b4f9eb806bfad3ffb4dbf7b4e2ffbfeeb7b4e258d19751ebb1c2cbc08bfa",
    "8bc0d0ac81e1d05ac1f35bfbeccc95b68c9ed5cc958bcc95cf69e182bac1",
    "ba68d0f3fbfbf359e1c38bfbe4c2c1d050d0f2849efa8c9ec38495cfcc9e",
    "b263fbc76ac1e1f9e190b0d022e95c05a86d79734d5a727734a5196ee512",
    "0da51953a51917006d5ad34d62015c2b92772b306d1be2773cab4d08395c",
    "5bad1253a5126aad1966e5126a0a771f034d39906d48d95c03927624d347",
    "5808677b095d15de334f9e382cde3372de33367b477ba867437a760ae95d",
    "7b0b474bd95d6c90675802767ad63872de384bd633479e383a315d4f3867",
    "69ab4718e27641ab4f66ea7e1a315e39306457e70a0da7016ee70a30e70a",
    "05027e48d15e70034f39906448727e78a0645fe95e6b7b4f38ef0130e701",
    "09ef0a05a7017808640d015e2b927e5adb4f"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock102OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock102OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock102InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock102InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock102InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock102OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17df8617df7df7e17e17e185f6df8e37df8617e17e186186185f7e1",
    "85f85f96175d7e185f7df8617df7df85f85f7e185f6df8e38617df7e17e1",
    "8618617e185f8617e195f75d7df7e185f7df85f7df86185f7df7e16e18e3",
    "85f86186185f7e18617df85f8617e195f75d86185f85f7df85f7df7df7e1",
    "86185f95f75d85f8617df7e185f7df7df85f85f7e196175d7df86185f85f",
    "7df7df85f7e17e17e16df8e385f7e18617df8618617e17e185f7e196175d",
    "8617df85f85f7df7df7e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock102OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock102OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block102_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock102Input a) =
      generatedSixthXiShortBlock102InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock102Output a) =
      generatedSixthXiShortBlock102OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock102Input a) =
      generatedSixthXiShortBlock102InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock102Output a) =
      generatedSixthXiShortBlock102OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block102_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock102InputMask a) =
      generatedSixthXiShortBlock102OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock102InputMask a)) *
      generatedSixthXiShortBlock102InputNumerator a =
        generatedSixthXiShortBlock102OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block102_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock102Input a
    let y := generatedSixthXiShortBlock102Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block102_cache a
  have hs := generatedSixth_xi_short_block102_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block102_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock102Input a
    let y := generatedSixthXiShortBlock102Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block102_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block102_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock102Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block102_certificate a).1
    (generatedSixth_xi_short_block102_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
