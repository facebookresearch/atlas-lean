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
def generatedSixthXiShortBlock090Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (210, 56)),
    Sum.inr (Sum.inl (204, 15)),
    Sum.inr (Sum.inl (147, 13)),
    Sum.inr (Sum.inl (170, 31)),
    Sum.inr (Sum.inl (35, 7)),
    Sum.inr (Sum.inl (15, 3)),
    Sum.inr (Sum.inl (35, 15)),
    Sum.inr (Sum.inl (35, 3)),
    Sum.inr (Sum.inl (210, 23)),
    Sum.inr (Sum.inl (147, 31)),
    Sum.inr (Sum.inl (170, 15)),
    Sum.inr (Sum.inl (204, 45)),
    Sum.inr (Sum.inl (170, 13)),
    Sum.inr (Sum.inl (210, 3)),
    Sum.inr (Sum.inl (147, 29)),
    Sum.inr (Sum.inl (204, 50)),
    Sum.inr (Sum.inl (15, 35)),
    Sum.inr (Sum.inl (15, 19)),
    Sum.inr (Sum.inl (35, 11)),
    Sum.inr (Sum.inl (15, 51)),
    Sum.inr (Sum.inl (170, 29)),
    Sum.inr (Sum.inl (147, 15)),
    Sum.inr (Sum.inl (204, 16)),
    Sum.inr (Sum.inl (210, 44)),
    Sum.inr (Sum.inl (196, 60)),
    Sum.inr (Sum.inl (195, 7)),
    Sum.inr (Sum.inl (144, 44)),
    Sum.inr (Sum.inl (167, 62)),
    Sum.inr (Sum.inl (32, 22)),
    Sum.inr (Sum.inl (12, 6)),
    Sum.inr (Sum.inl (32, 30)),
    Sum.inr (Sum.inl (32, 18)),
    Sum.inr (Sum.inl (196, 45)),
    Sum.inr (Sum.inl (144, 12)),
    Sum.inr (Sum.inl (167, 28)),
    Sum.inr (Sum.inl (195, 39)),
    Sum.inr (Sum.inl (167, 30)),
    Sum.inr (Sum.inl (196, 2)),
    Sum.inr (Sum.inl (144, 14)),
    Sum.inr (Sum.inl (195, 15)),
    Sum.inr (Sum.inl (12, 38)),
    Sum.inr (Sum.inl (12, 22)),
    Sum.inr (Sum.inl (32, 26)),
    Sum.inr (Sum.inl (12, 54)),
    Sum.inr (Sum.inl (167, 60)),
    Sum.inr (Sum.inl (144, 46)),
    Sum.inr (Sum.inl (195, 47)),
    Sum.inr (Sum.inl (196, 19)),
    Sum.inr (Sum.inl (88, 13)),
    Sum.inr (Sum.inl (87, 44)),
    Sum.inr (Sum.inl (81, 7)),
    Sum.inr (Sum.inl (83, 12)),
    Sum.inr (Sum.inl (23, 57)),
    Sum.inr (Sum.inl (3, 61)),
    Sum.inr (Sum.inl (23, 49)),
    Sum.inr (Sum.inl (23, 61)),
    Sum.inr (Sum.inl (88, 28)),
    Sum.inr (Sum.inl (81, 24)),
    Sum.inr (Sum.inl (83, 30)),
    Sum.inr (Sum.inl (87, 51)),
    Sum.inr (Sum.inl (83, 14)),
    Sum.inr (Sum.inl (88, 34)),
    Sum.inr (Sum.inl (81, 60)),
    Sum.inr (Sum.inl (87, 13)),
    Sum.inr (Sum.inl (3, 29)),
    Sum.inr (Sum.inl (3, 45)),
    Sum.inr (Sum.inl (23, 53)),
    Sum.inr (Sum.inl (3, 13)),
    Sum.inr (Sum.inl (83, 28)),
    Sum.inr (Sum.inl (81, 35)),
    Sum.inr (Sum.inl (87, 18)),
    Sum.inr (Sum.inl (88, 51)),
    Sum.inr (Sum.inr (123, 8)),
    Sum.inr (Sum.inr (58, 15)),
    Sum.inr (Sum.inr (250, 21)),
    Sum.inr (Sum.inr (176, 3)),
    Sum.inr (Sum.inr (357, 18)),
    Sum.inr (Sum.inr (366, 5)),
    Sum.inr (Sum.inr (357, 7)),
    Sum.inr (Sum.inr (357, 6)),
    Sum.inr (Sum.inr (123, 0)),
    Sum.inr (Sum.inr (250, 14)),
    Sum.inr (Sum.inr (176, 10)),
    Sum.inr (Sum.inr (58, 22)),
    Sum.inr (Sum.inr (176, 12)),
    Sum.inr (Sum.inr (123, 23)),
    Sum.inr (Sum.inr (250, 9)),
    Sum.inr (Sum.inr (58, 1)),
    Sum.inr (Sum.inr (366, 16)),
    Sum.inr (Sum.inr (366, 17)),
    Sum.inr (Sum.inr (357, 4)),
    Sum.inr (Sum.inr (366, 19)),
    Sum.inr (Sum.inr (176, 20)),
    Sum.inr (Sum.inr (250, 2)),
    Sum.inr (Sum.inr (58, 11)),
    Sum.inr (Sum.inr (123, 13)),
    Sum.inr (Sum.inr (177, 0)),
    Sum.inr (Sum.inr (240, 22)),
    Sum.inr (Sum.inr (48, 14)),
    Sum.inr (Sum.inr (122, 10)),
    Sum.inr (Sum.inr (431, 18)),
    Sum.inr (Sum.inr (420, 5)),
    Sum.inr (Sum.inr (431, 7)),
    Sum.inr (Sum.inr (431, 6)),
    Sum.inr (Sum.inr (177, 8)),
    Sum.inr (Sum.inr (48, 21)),
    Sum.inr (Sum.inr (122, 3)),
    Sum.inr (Sum.inr (240, 15)),
    Sum.inr (Sum.inr (122, 20)),
    Sum.inr (Sum.inr (177, 13)),
    Sum.inr (Sum.inr (48, 2)),
    Sum.inr (Sum.inr (240, 11)),
    Sum.inr (Sum.inr (420, 16)),
    Sum.inr (Sum.inr (420, 17)),
    Sum.inr (Sum.inr (431, 4)),
    Sum.inr (Sum.inr (420, 19)),
    Sum.inr (Sum.inr (122, 12)),
    Sum.inr (Sum.inr (48, 9)),
    Sum.inr (Sum.inr (240, 1)),
    Sum.inr (Sum.inr (177, 23)),
    Sum.inr (Sum.inr (243, 23)),
    Sum.inr (Sum.inr (178, 1)),
    Sum.inr (Sum.inr (114, 9)),
    Sum.inr (Sum.inr (56, 12)),
    Sum.inr (Sum.inr (493, 18)),
    Sum.inr (Sum.inr (486, 5)),
    Sum.inr (Sum.inr (493, 7)),
    Sum.inr (Sum.inr (493, 6)),
    Sum.inr (Sum.inr (243, 13)),
    Sum.inr (Sum.inr (114, 2)),
    Sum.inr (Sum.inr (56, 20)),
    Sum.inr (Sum.inr (178, 11)),
    Sum.inr (Sum.inr (56, 3)),
    Sum.inr (Sum.inr (243, 8)),
    Sum.inr (Sum.inr (114, 21)),
    Sum.inr (Sum.inr (178, 15)),
    Sum.inr (Sum.inr (486, 16)),
    Sum.inr (Sum.inr (486, 17)),
    Sum.inr (Sum.inr (493, 4)),
    Sum.inr (Sum.inr (486, 19)),
    Sum.inr (Sum.inr (56, 10)),
    Sum.inr (Sum.inr (114, 14)),
    Sum.inr (Sum.inr (178, 22)),
    Sum.inr (Sum.inr (243, 0)),
    Sum.inr (Sum.inr (50, 13)),
    Sum.inr (Sum.inr (115, 11)),
    Sum.inr (Sum.inr (179, 2)),
    Sum.inr (Sum.inr (249, 20)),
    Sum.inr (Sum.inr (300, 18)),
    Sum.inr (Sum.inr (295, 5)),
    Sum.inr (Sum.inr (300, 7)),
    Sum.inr (Sum.inr (300, 6)),
    Sum.inr (Sum.inr (50, 23)),
    Sum.inr (Sum.inr (179, 9)),
    Sum.inr (Sum.inr (249, 12)),
    Sum.inr (Sum.inr (115, 1)),
    Sum.inr (Sum.inr (249, 10)),
    Sum.inr (Sum.inr (50, 0)),
    Sum.inr (Sum.inr (179, 14)),
    Sum.inr (Sum.inr (115, 22)),
    Sum.inr (Sum.inr (295, 16)),
    Sum.inr (Sum.inr (295, 17)),
    Sum.inr (Sum.inr (300, 4)),
    Sum.inr (Sum.inr (295, 19)),
    Sum.inr (Sum.inr (249, 3)),
    Sum.inr (Sum.inr (179, 21)),
    Sum.inr (Sum.inr (115, 15)),
    Sum.inr (Sum.inr (50, 8)),
    Sum.inr (Sum.inl (88, 1)),
    Sum.inr (Sum.inl (87, 32)),
    Sum.inr (Sum.inl (81, 4)),
    Sum.inr (Sum.inl (83, 0)),
    Sum.inr (Sum.inl (23, 55)),
    Sum.inr (Sum.inl (3, 15)),
    Sum.inr (Sum.inl (23, 63)),
    Sum.inr (Sum.inl (23, 51)),
    Sum.inr (Sum.inl (88, 16)),
    Sum.inr (Sum.inl (81, 27)),
    Sum.inr (Sum.inl (83, 18)),
    Sum.inr (Sum.inl (87, 63)),
    Sum.inr (Sum.inl (83, 2)),
    Sum.inr (Sum.inl (88, 46)),
    Sum.inr (Sum.inl (81, 63)),
    Sum.inr (Sum.inl (87, 1)),
    Sum.inr (Sum.inl (3, 47)),
    Sum.inr (Sum.inl (3, 31)),
    Sum.inr (Sum.inl (23, 59)),
    Sum.inr (Sum.inl (3, 63)),
    Sum.inr (Sum.inl (83, 16)),
    Sum.inr (Sum.inl (81, 32)),
    Sum.inr (Sum.inl (87, 30)),
    Sum.inr (Sum.inl (88, 63)),
    Sum.inr (Sum.inl (196, 48)),
    Sum.inr (Sum.inl (195, 4)),
    Sum.inr (Sum.inl (144, 32)),
    Sum.inr (Sum.inl (167, 50)),
    Sum.inr (Sum.inl (32, 24)),
    Sum.inr (Sum.inl (12, 52)),
    Sum.inr (Sum.inl (32, 16)),
    Sum.inr (Sum.inl (32, 28)),
    Sum.inr (Sum.inl (196, 33)),
    Sum.inr (Sum.inl (144, 0)),
    Sum.inr (Sum.inl (167, 16)),
    Sum.inr (Sum.inl (195, 36)),
    Sum.inr (Sum.inl (167, 18)),
    Sum.inr (Sum.inl (196, 14)),
    Sum.inr (Sum.inl (144, 2)),
    Sum.inr (Sum.inl (195, 12)),
    Sum.inr (Sum.inl (12, 20)),
    Sum.inr (Sum.inl (12, 36)),
    Sum.inr (Sum.inl (32, 20)),
    Sum.inr (Sum.inl (12, 4)),
    Sum.inr (Sum.inl (167, 48)),
    Sum.inr (Sum.inl (144, 34)),
    Sum.inr (Sum.inl (195, 44)),
    Sum.inr (Sum.inl (196, 31)),
    Sum.inr (Sum.inl (210, 59)),
    Sum.inr (Sum.inl (204, 3)),
    Sum.inr (Sum.inl (147, 1)),
    Sum.inr (Sum.inl (170, 19)),
    Sum.inr (Sum.inl (35, 9)),
    Sum.inr (Sum.inl (15, 49)),
    Sum.inr (Sum.inl (35, 1)),
    Sum.inr (Sum.inl (35, 13)),
    Sum.inr (Sum.inl (210, 20)),
    Sum.inr (Sum.inl (147, 19)),
    Sum.inr (Sum.inl (170, 3)),
    Sum.inr (Sum.inl (204, 33)),
    Sum.inr (Sum.inl (170, 1)),
    Sum.inr (Sum.inl (210, 0)),
    Sum.inr (Sum.inl (147, 17)),
    Sum.inr (Sum.inl (204, 62)),
    Sum.inr (Sum.inl (15, 17)),
    Sum.inr (Sum.inl (15, 33)),
    Sum.inr (Sum.inl (35, 5)),
    Sum.inr (Sum.inl (15, 1)),
    Sum.inr (Sum.inl (170, 17)),
    Sum.inr (Sum.inl (147, 3)),
    Sum.inr (Sum.inl (204, 28)),
    Sum.inr (Sum.inl (210, 47)),
    Sum.inr (Sum.inl (133, 19)),
    Sum.inr (Sum.inl (132, 50)),
    Sum.inr (Sum.inl (126, 51)),
    Sum.inr (Sum.inl (128, 59)),
    Sum.inr (Sum.inl (26, 38)),
    Sum.inr (Sum.inl (6, 10)),
    Sum.inr (Sum.inl (26, 46)),
    Sum.inr (Sum.inl (26, 34)),
    Sum.inr (Sum.inl (133, 60)),
    Sum.inr (Sum.inl (126, 18)),
    Sum.inr (Sum.inl (128, 43)),
    Sum.inr (Sum.inl (132, 19)),
    Sum.inr (Sum.inl (128, 51)),
    Sum.inr (Sum.inl (133, 2)),
    Sum.inr (Sum.inl (126, 50)),
    Sum.inr (Sum.inl (132, 45))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock090Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨23040 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock090InputMaskData : ℕ :=
  sixthHex% [
    "aefd1b84fd1bbbfd1bd1f51b92c51b90c51b93cd1bd1c51b9dd51b95d51b",
    "99d51bd1dd1be12d1bc12d1bf1251b912d1ba8551a9e5d1a855d1af35d1a",
    "94951a8a9d1aad951af3951a8cf51aa6f51a99f51af3fd1ab0c51ab2c51a",
    "b1cd1af3c51abfdd1ab7dd1abbdd1af3d51ac32d1ae32d1ad3251ab32d1a",
    "aa5d199c5519875519f15519969d19889519af9d19f19d198ef519a4f519",
    "9bf519f1fd19b2c519b0c519b3cd19f1c519bdd519b5d519b9d519f1dd19",
    "c12519e12519d12d19b12519c85d18fe5518e55518935518f49d18ea9518",
    "cd9d18939d18ecf518c6f518f9f51893fd18d0cd18d2cd18d1c51893cd18",
    "dfd518d7d518dbd51893dd18a32d18832d18b32518d32d18a855179e5d17",
    "855d17f35d179495178a9d17ad9517f395178cfd17a6fd1799fd17f3f517",
    "b0c517b2c517b1cd17f3c517bfd517b7d517bbd517f3dd17c32d17e32d17",
    "d32517b32d178a5d16bc5516a75516d15516b69d16a895168f9d16d19d16",
    "aef51684f516bbf516d1fd1692c51690c51693cd16d1c5169ddd1695dd16",
    "99dd16d1d516e12d16c12d16f12516912d16885515be5d15a55d15d35d15",
    "b49515aa9d158d9515d39515acf51586f515b9f515d3fd1590c51592c515",
    "91cd15d3c5159fd51597d5159bd515d3dd15e32515c32515f32d15932515",
    "ea5514dc5d14c75d14b15d14d69514c89d14ef9514b19514cef514e4f514",
    "dbf514b1fd14f2cd14f0cd14f3c514b1cd14fdd514f5d514f9d514b1dd14",
    "812d14a12d14912514f12d14b15d138755139c5513ea55138d9513939d13",
    "b49513ea951395f513bff51380f513eafd13a9cd13abcd13a8c513eacd13",
    "a6dd13aedd13a2dd13ead513da2d13fa2d13ca2513aa2d13d35d12e55512",
    "fe5512885512ef9512f19d12d69512889512f7f512ddf512e2f51288fd12",
    "cbc512c9c512cacd1288c512c4dd12ccdd12c0dd1288d512b82512982512",
    "a82d12c82512d15511e75d11fc5d118a5d11ed9d11f39511d49d118a9d11",
    "f5f511dff511e0f5118afd11c9c511cbc511c8cd118ac511c6d511ced511",
    "c2d5118add11ba2d119a2d11aa2511ca2d11"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock090InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock090InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock090OutputMaskData : ℕ :=
  sixthHex% [
    "3b927e07015e3fd34f07006476e27e46306410395e24ab4f773f017f3701",
    "463f0a4a770146986442d15e15027e150b4f48086e1e095f13927f41d345",
    "5e442b04042067442b39442b7de15f41727f79a06e41734541d15f710345",
    "270a7f13986e314c20394420004c2b0c042071ab4575e27f22315f22386e",
    "02315c54306d59ab4d0bea77147d194e3d122d7d19737d1946986d7a0b4d",
    "42d95c7a0a777aa86d4a7a771c734d28e15c7b7512737d124a7519463d12",
    "3b92773fdb4d68086d68015c4002761603471b986749d95d564e330c0e38",
    "6f4e33314e3304ab4738386700ea7638395d49db4779095d2f00671b9276",
    "394638314e38084633040e3808e15d0ca8675b7b475b7276c580d29381e3",
    "9e1ac3cc5bf9d3cc97898c9ceacc97b4cc978129e3bdbac38568d2bdbbf9",
    "cc59e3fc8bf9aa82c39e10d2cd849cc58c9cfc8497f0cc9cfc23f9f86ac3",
    "afb9e3afb0d283f3f3d5f2c2d869e28a28d895bfb6cfffbdacbfb6f2bfb6",
    "c75ac2fbc9e2c31bf3fbc8d8fb6ac2cbb8d89db1e2a923f38bf7bd83ffbd",
    "baf7b6b6bfbdcb10d8cf59e2988ac29883f3c9cac19fcbf09250d0c011ea",
    "df868485c68fe68684b88684fc23f0c0b0d0f862c1c0b1eac013f0f0c1ea",
    "a6c8d0925ac1c1ce8fc9c68ff0ce84fc868f8129ea8560d0d2b3f0d2bac1",
    "8bf9ebddf8dad063fa8222c09db5aec7f5a5a4b5aefab5aebe10da8283fa",
    "ba51eb8282c0f360dac3b2c095bbfaa129eb83fda58bf5a5b2fdaebeb5a5",
    "b25ac0b613fae1c0dae1c9eb080a765e0b4753906701d15d6f0633354638",
    "5606330806334ca34770306748e27670315d01d34731015d670867539a76",
    "000e38080638310e333d463840e95d44a067137347137a764a395c1c386d",
    "11a34d43e2772d35197775121435194a35190e906d32034d0ad15c320277",
    "32a06d027277547b4d60e95c423d124a3512733d197f7512739a7777d34d",
    "20006d20095c00006e56015f5b9a7f09db45670c2b3d4c205e0c2b000c2b",
    "35e95f097a7f31a86e097b4509d95f390b456f027f5b906e080420000c20",
    "39042b354c2039a3453dea7f6a395f6a306e"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock090OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock090OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock090InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock090InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock090InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock090OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df85f85f7df7df7e185f7e17e16df8e37e185f8617df86186185f85f",
    "85f7e196175d7df86185f85f7df7df85f7e17e17e16df8e385f7e18617df",
    "8618617e17e17df7e16e18e385f86186185f7e18617df85f8617e195f75d",
    "7df7e185f7df85f7df86185f7df7e16e18e37e17df86185f7e18618617e1",
    "7df85f6e18e37df7e17e18617e186186185f85f85f96175d7e185f7df861",
    "7df7df85f85f7e185f6df8e38617df7e17e18618617e185f85f85f96175d",
    "85f7e17df8617df7df7e17e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock090OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock090OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block090_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock090Input a) =
      generatedSixthXiShortBlock090InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock090Output a) =
      generatedSixthXiShortBlock090OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock090Input a) =
      generatedSixthXiShortBlock090InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock090Output a) =
      generatedSixthXiShortBlock090OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block090_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock090InputMask a) =
      generatedSixthXiShortBlock090OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock090InputMask a)) *
      generatedSixthXiShortBlock090InputNumerator a =
        generatedSixthXiShortBlock090OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block090_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock090Input a
    let y := generatedSixthXiShortBlock090Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block090_cache a
  have hs := generatedSixth_xi_short_block090_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block090_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock090Input a
    let y := generatedSixthXiShortBlock090Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block090_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block090_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock090Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block090_certificate a).1
    (generatedSixth_xi_short_block090_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
