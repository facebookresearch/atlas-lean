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
def generatedSixthXiShortBlock069Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (215, 48)),
    Sum.inr (Sum.inl (209, 48)),
    Sum.inr (Sum.inl (152, 12)),
    Sum.inr (Sum.inl (175, 0)),
    Sum.inr (Sum.inl (40, 18)),
    Sum.inr (Sum.inl (20, 52)),
    Sum.inr (Sum.inl (40, 24)),
    Sum.inr (Sum.inl (40, 26)),
    Sum.inr (Sum.inl (215, 33)),
    Sum.inr (Sum.inl (152, 28)),
    Sum.inr (Sum.inl (175, 16)),
    Sum.inr (Sum.inl (209, 17)),
    Sum.inr (Sum.inl (175, 18)),
    Sum.inr (Sum.inl (215, 49)),
    Sum.inr (Sum.inl (152, 8)),
    Sum.inr (Sum.inl (209, 16)),
    Sum.inr (Sum.inl (20, 20)),
    Sum.inr (Sum.inl (20, 36)),
    Sum.inr (Sum.inl (40, 16)),
    Sum.inr (Sum.inl (20, 4)),
    Sum.inr (Sum.inl (175, 2)),
    Sum.inr (Sum.inl (152, 24)),
    Sum.inr (Sum.inl (209, 49)),
    Sum.inr (Sum.inl (215, 32)),
    Sum.inr (Sum.inl (104, 43)),
    Sum.inr (Sum.inl (103, 49)),
    Sum.inr (Sum.inl (97, 19)),
    Sum.inr (Sum.inl (99, 62)),
    Sum.inr (Sum.inl (24, 28)),
    Sum.inr (Sum.inl (4, 6)),
    Sum.inr (Sum.inl (24, 22)),
    Sum.inr (Sum.inl (24, 20)),
    Sum.inr (Sum.inl (104, 52)),
    Sum.inr (Sum.inl (97, 1)),
    Sum.inr (Sum.inl (99, 44)),
    Sum.inr (Sum.inl (103, 46)),
    Sum.inr (Sum.inl (99, 46)),
    Sum.inr (Sum.inl (104, 16)),
    Sum.inr (Sum.inl (97, 46)),
    Sum.inr (Sum.inl (103, 19)),
    Sum.inr (Sum.inl (4, 38)),
    Sum.inr (Sum.inl (4, 22)),
    Sum.inr (Sum.inl (24, 30)),
    Sum.inr (Sum.inl (4, 54)),
    Sum.inr (Sum.inl (99, 60)),
    Sum.inr (Sum.inl (97, 60)),
    Sum.inr (Sum.inl (103, 12)),
    Sum.inr (Sum.inl (104, 15)),
    Sum.inr (Sum.inl (179, 17)),
    Sum.inr (Sum.inl (178, 59)),
    Sum.inr (Sum.inl (142, 47)),
    Sum.inr (Sum.inl (165, 50)),
    Sum.inr (Sum.inl (30, 18)),
    Sum.inr (Sum.inl (10, 52)),
    Sum.inr (Sum.inl (30, 24)),
    Sum.inr (Sum.inl (30, 26)),
    Sum.inr (Sum.inl (179, 62)),
    Sum.inr (Sum.inl (142, 13)),
    Sum.inr (Sum.inl (165, 16)),
    Sum.inr (Sum.inl (178, 36)),
    Sum.inr (Sum.inl (165, 48)),
    Sum.inr (Sum.inl (179, 0)),
    Sum.inr (Sum.inl (142, 48)),
    Sum.inr (Sum.inl (178, 12)),
    Sum.inr (Sum.inl (10, 20)),
    Sum.inr (Sum.inl (10, 36)),
    Sum.inr (Sum.inl (30, 16)),
    Sum.inr (Sum.inl (10, 4)),
    Sum.inr (Sum.inl (165, 18)),
    Sum.inr (Sum.inl (142, 18)),
    Sum.inr (Sum.inl (178, 19)),
    Sum.inr (Sum.inl (179, 47)),
    Sum.inr (Sum.inr (347, 13)),
    Sum.inr (Sum.inr (282, 22)),
    Sum.inr (Sum.inr (474, 9)),
    Sum.inr (Sum.inr (400, 3)),
    Sum.inr (Sum.inr (69, 6)),
    Sum.inr (Sum.inr (78, 5)),
    Sum.inr (Sum.inr (69, 4)),
    Sum.inr (Sum.inr (69, 18)),
    Sum.inr (Sum.inr (347, 23)),
    Sum.inr (Sum.inr (474, 2)),
    Sum.inr (Sum.inr (400, 10)),
    Sum.inr (Sum.inr (282, 15)),
    Sum.inr (Sum.inr (400, 12)),
    Sum.inr (Sum.inr (347, 0)),
    Sum.inr (Sum.inr (474, 21)),
    Sum.inr (Sum.inr (282, 11)),
    Sum.inr (Sum.inr (78, 16)),
    Sum.inr (Sum.inr (78, 17)),
    Sum.inr (Sum.inr (69, 7)),
    Sum.inr (Sum.inr (78, 19)),
    Sum.inr (Sum.inr (400, 20)),
    Sum.inr (Sum.inr (474, 14)),
    Sum.inr (Sum.inr (282, 1)),
    Sum.inr (Sum.inr (347, 8)),
    Sum.inr (Sum.inr (272, 23)),
    Sum.inr (Sum.inr (337, 15)),
    Sum.inr (Sum.inr (401, 2)),
    Sum.inr (Sum.inr (475, 10)),
    Sum.inr (Sum.inr (14, 6)),
    Sum.inr (Sum.inr (5, 5)),
    Sum.inr (Sum.inr (14, 4)),
    Sum.inr (Sum.inr (14, 18)),
    Sum.inr (Sum.inr (272, 13)),
    Sum.inr (Sum.inr (401, 9)),
    Sum.inr (Sum.inr (475, 3)),
    Sum.inr (Sum.inr (337, 22)),
    Sum.inr (Sum.inr (475, 20)),
    Sum.inr (Sum.inr (272, 8)),
    Sum.inr (Sum.inr (401, 14)),
    Sum.inr (Sum.inr (337, 1)),
    Sum.inr (Sum.inr (5, 16)),
    Sum.inr (Sum.inr (5, 17)),
    Sum.inr (Sum.inr (14, 7)),
    Sum.inr (Sum.inr (5, 19)),
    Sum.inr (Sum.inr (475, 12)),
    Sum.inr (Sum.inr (401, 21)),
    Sum.inr (Sum.inr (337, 11)),
    Sum.inr (Sum.inr (272, 0)),
    Sum.inr (Sum.inr (402, 0)),
    Sum.inr (Sum.inr (467, 11)),
    Sum.inr (Sum.inr (275, 21)),
    Sum.inr (Sum.inr (345, 12)),
    Sum.inr (Sum.inr (140, 6)),
    Sum.inr (Sum.inr (135, 5)),
    Sum.inr (Sum.inr (140, 4)),
    Sum.inr (Sum.inr (140, 18)),
    Sum.inr (Sum.inr (402, 8)),
    Sum.inr (Sum.inr (275, 14)),
    Sum.inr (Sum.inr (345, 20)),
    Sum.inr (Sum.inr (467, 1)),
    Sum.inr (Sum.inr (345, 3)),
    Sum.inr (Sum.inr (402, 13)),
    Sum.inr (Sum.inr (275, 9)),
    Sum.inr (Sum.inr (467, 22)),
    Sum.inr (Sum.inr (135, 16)),
    Sum.inr (Sum.inr (135, 17)),
    Sum.inr (Sum.inr (140, 7)),
    Sum.inr (Sum.inr (135, 19)),
    Sum.inr (Sum.inr (345, 10)),
    Sum.inr (Sum.inr (275, 2)),
    Sum.inr (Sum.inr (467, 15)),
    Sum.inr (Sum.inr (402, 23)),
    Sum.inr (Sum.inr (466, 8)),
    Sum.inr (Sum.inr (403, 1)),
    Sum.inr (Sum.inr (339, 14)),
    Sum.inr (Sum.inr (281, 20)),
    Sum.inr (Sum.inr (204, 6)),
    Sum.inr (Sum.inr (199, 5)),
    Sum.inr (Sum.inr (204, 4)),
    Sum.inr (Sum.inr (204, 18)),
    Sum.inr (Sum.inr (466, 0)),
    Sum.inr (Sum.inr (339, 21)),
    Sum.inr (Sum.inr (281, 12)),
    Sum.inr (Sum.inr (403, 11)),
    Sum.inr (Sum.inr (281, 10)),
    Sum.inr (Sum.inr (466, 23)),
    Sum.inr (Sum.inr (339, 2)),
    Sum.inr (Sum.inr (403, 15)),
    Sum.inr (Sum.inr (199, 16)),
    Sum.inr (Sum.inr (199, 17)),
    Sum.inr (Sum.inr (204, 7)),
    Sum.inr (Sum.inr (199, 19)),
    Sum.inr (Sum.inr (281, 3)),
    Sum.inr (Sum.inr (339, 9)),
    Sum.inr (Sum.inr (403, 22)),
    Sum.inr (Sum.inr (466, 13)),
    Sum.inr (Sum.inl (179, 29)),
    Sum.inr (Sum.inl (178, 56)),
    Sum.inr (Sum.inl (142, 35)),
    Sum.inr (Sum.inl (165, 62)),
    Sum.inr (Sum.inl (30, 28)),
    Sum.inr (Sum.inl (10, 6)),
    Sum.inr (Sum.inl (30, 22)),
    Sum.inr (Sum.inl (30, 20)),
    Sum.inr (Sum.inl (179, 50)),
    Sum.inr (Sum.inl (142, 1)),
    Sum.inr (Sum.inl (165, 28)),
    Sum.inr (Sum.inl (178, 39)),
    Sum.inr (Sum.inl (165, 60)),
    Sum.inr (Sum.inl (179, 12)),
    Sum.inr (Sum.inl (142, 60)),
    Sum.inr (Sum.inl (178, 15)),
    Sum.inr (Sum.inl (10, 38)),
    Sum.inr (Sum.inl (10, 22)),
    Sum.inr (Sum.inl (30, 30)),
    Sum.inr (Sum.inl (10, 54)),
    Sum.inr (Sum.inl (165, 30)),
    Sum.inr (Sum.inl (142, 30)),
    Sum.inr (Sum.inl (178, 16)),
    Sum.inr (Sum.inl (179, 35)),
    Sum.inr (Sum.inl (104, 40)),
    Sum.inr (Sum.inl (103, 61)),
    Sum.inr (Sum.inl (97, 31)),
    Sum.inr (Sum.inl (99, 50)),
    Sum.inr (Sum.inl (24, 18)),
    Sum.inr (Sum.inl (4, 52)),
    Sum.inr (Sum.inl (24, 24)),
    Sum.inr (Sum.inl (24, 26)),
    Sum.inr (Sum.inl (104, 55)),
    Sum.inr (Sum.inl (97, 13)),
    Sum.inr (Sum.inl (99, 32)),
    Sum.inr (Sum.inl (103, 34)),
    Sum.inr (Sum.inl (99, 34)),
    Sum.inr (Sum.inl (104, 19)),
    Sum.inr (Sum.inl (97, 34)),
    Sum.inr (Sum.inl (103, 31)),
    Sum.inr (Sum.inl (4, 20)),
    Sum.inr (Sum.inl (4, 36)),
    Sum.inr (Sum.inl (24, 16)),
    Sum.inr (Sum.inl (4, 4)),
    Sum.inr (Sum.inl (99, 48)),
    Sum.inr (Sum.inl (97, 48)),
    Sum.inr (Sum.inl (103, 0)),
    Sum.inr (Sum.inl (104, 12)),
    Sum.inr (Sum.inl (215, 60)),
    Sum.inr (Sum.inl (209, 60)),
    Sum.inr (Sum.inl (152, 15)),
    Sum.inr (Sum.inl (175, 12)),
    Sum.inr (Sum.inl (40, 28)),
    Sum.inr (Sum.inl (20, 6)),
    Sum.inr (Sum.inl (40, 22)),
    Sum.inr (Sum.inl (40, 20)),
    Sum.inr (Sum.inl (215, 45)),
    Sum.inr (Sum.inl (152, 31)),
    Sum.inr (Sum.inl (175, 28)),
    Sum.inr (Sum.inl (209, 29)),
    Sum.inr (Sum.inl (175, 30)),
    Sum.inr (Sum.inl (215, 61)),
    Sum.inr (Sum.inl (152, 11)),
    Sum.inr (Sum.inl (209, 28)),
    Sum.inr (Sum.inl (20, 38)),
    Sum.inr (Sum.inl (20, 22)),
    Sum.inr (Sum.inl (40, 30)),
    Sum.inr (Sum.inl (20, 54)),
    Sum.inr (Sum.inl (175, 14)),
    Sum.inr (Sum.inl (152, 27)),
    Sum.inr (Sum.inl (209, 61)),
    Sum.inr (Sum.inl (215, 44)),
    Sum.inr (Sum.inl (71, 45)),
    Sum.inr (Sum.inl (70, 29)),
    Sum.inr (Sum.inl (64, 44)),
    Sum.inr (Sum.inl (66, 31)),
    Sum.inr (Sum.inl (22, 28)),
    Sum.inr (Sum.inl (2, 6)),
    Sum.inr (Sum.inl (22, 22)),
    Sum.inr (Sum.inl (22, 20)),
    Sum.inr (Sum.inl (71, 60)),
    Sum.inr (Sum.inl (64, 12)),
    Sum.inr (Sum.inl (66, 15)),
    Sum.inr (Sum.inl (70, 60)),
    Sum.inr (Sum.inl (66, 23)),
    Sum.inr (Sum.inl (71, 2)),
    Sum.inr (Sum.inl (64, 13)),
    Sum.inr (Sum.inl (70, 35))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock069Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨17664 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock069InputMaskData : ℕ :=
  sixthHex% [
    "b8c98b92c18badc18bc7c98b84f98b86f98b85f98bc7f98b8be98b83e18b",
    "8fe98bc7e18bf7118bd7118be7198b87198bbc898a8a818a91818ae7898a",
    "80418a9e418ab9418ae7418a98298ab2218a8d218ae7298aa4118aa6118a",
    "a5118ae7118aab098aa3018aaf098ae7018ad7f98af7f98ac7f18aa7f18a",
    "83b189b5b989aeb989d8b189bf7989a17989867989d87989a719898d1189",
    "b21189d819899b21899921899a2189d821899431899c3989903189d83989",
    "e8c189c8c189f8c98998c989e35188d55988ce5988b85188df9988c19988",
    "e69988b89988c7f988edf188d2f188b8f988fbc988f9c988fac988b8c988",
    "f4d188fcd988f0d188b8d988882988a82988982188f8218887a987b1a187",
    "aaa187dca987bb6187a56187826187dc6187a30187890987b60987dc0187",
    "9f31879d31879e3187dc3187902187982987942187dc2987ecd987ccd987",
    "fcd1879cd187a749869141868a4186fc49869b8186858186a28186fc8186",
    "83e186a9e98696e986fce186bfd986bdd986bed986fcd986b0c186b8c986",
    "b4c186fcc986cc3186ec3186dc3986bc3986987185ae7985b57985c37185",
    "a4b985bab9859db985c3b985bcd18596d985a9d985c3d18580e98582e985",
    "81e985c3e9858ff98587f1858bf985c3f185f30985d30985e30185830185",
    "f89184ce9984d59984a39184c45984da5984fd5984a35984dc3184f63984",
    "c93984a33184e00184e20184e10184a30184ef1984e71184eb1984a31184",
    "93e184b3e18483e984e3e984a719839111838a1183fc19839bd98385d983",
    "a2d983fcd98383b183a9b98396b983fcb183bf8183bd8183be8183fc8183",
    "b09183b89983b49183fc9983cc6183ec6183dc6983bc6983c7f982f1f182",
    "eaf1829cf982fb3982e53982c239829c3982e35182c95982f659829c5182",
    "df6982dd6982de69829c6982d07182d87982d471829c7982ac89828c8982",
    "bc8182dc8182f8c181cec981d5c981a3c181c40181da0181fd0181a30181",
    "dc6181f66981c96981a36181e05981e25981e15981a35981ef4981e74181",
    "eb4981a3418193b181b3b18183b981e3b981"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock069InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock069InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock069OutputMaskData : ℕ :=
  sixthHex% [
    "6cf2a021218019f3912120ba50c2a06010ba475980028b91511fdf2857df",
    "601fd46c57df60b8ba64f1803322a0426b916b1aa13d1b903080b013818a",
    "0c16e42716ef3516e46b16e45ef3901320b02bf2a113218a13839023518a",
    "0418b041caa1631eef1a56ef521ee45e56ef23f98a27b0b0706390012aa1",
    "0a88b35c89825112a27213986d84f64684fd5484f60a84f64e218203f2a2",
    "3b20b303f39803518233839814caa25118b3028cfd7bc4fd338cf63fc4fd",
    "426b984622a211f18260b8b34d89881b88b91613993512a32a85cd0185c6",
    "1385cd4d85cd0920b944f3997c218844f2a33510b905c2a3228b99675988",
    "458dc63cc5c6748dcd78c5c6742aa370639927b0b956f988d37762857653",
    "88ed73abec49b47b279f7b2c8d7b27d37b2797de53da0d73e2df62da0c49",
    "abee539b3c49bc7573f9a762aa332cd37b2c9b3327977b2c9b94499fdd73",
    "c80e53b94762e17652b77763baec4399ed79867a17ad7a1cbf7a17e17a17",
    "a5df63e80c43d0de52e80d79e8af63d87d79ff3443bae65298321ce17a1c",
    "a93217a57a1cd8d579dc9c438b4f63fa065280e440d6e571db7e51f87f6b",
    "e7e805cce80edee80580e805b50d71f8de51c00c40f8df6bf87d71c8af6b",
    "efe651aa3440f9a00e80e80ec8a005c4e80eb9476bbd0e51eadd719b9440",
    "c7e57b91e44a9c7f6abf7e50a0e93e8be93599e93ec7e93ef20c4abfdf6a",
    "870d7bbfde50ce3c4afeee50d9a76a9c757bbea135c7e9358fa13e83e935",
    "8f06508b4f6adc9c4aadd57b4981881f80b9121b99311aa35fcdcd74cdc6",
    "66cdcd38cdcd0d28b940fb9978298840faa33118b901caa3268399635188",
    "30c5c6498dc601c5cd0d8dc67022a3746b9923b8b952f1880e80b3588182",
    "551aa2761b9818ccf633ccfd21ccf67fccf64a298207faa23f28b307fb98",
    "075982378b9810c2a25510b377c4fd0e8cfd46c4f64a8cfd466398422aa2",
    "15f98264b0b36f12a13913903488b017898a795ee4525eef405ee41e5ee4",
    "5afb901728b02ffaa117298a178b9027598a0010b045c2a11656ef6f1eef",
    "2756e42b1eef27f18a23b8b0746b900522a1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock069OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock069OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock069InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock069InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock069InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock069OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f8617df96175d7df8617df7df85f7e17e17e1",
    "86186196175d85f7e185f7e185f7e185f7e17df8616df8e37df861861861",
    "7e185f7e17e17e18616e18e37df7e18617e186185f7df85f85f86195f75d",
    "85f86185f8617df7e186185f7e18616e18e386185f8617e186185f8617e1",
    "85f86195f75d7e17df85f8617df7e17df7e18617df96175d8617df7df7df",
    "85f7e185f85f7df7df6df8e37e185f7e185f7e185f7e185f7df8616df8e3",
    "8617df8618617e185f85f85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock069OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock069OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block069_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock069Input a) =
      generatedSixthXiShortBlock069InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock069Output a) =
      generatedSixthXiShortBlock069OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock069Input a) =
      generatedSixthXiShortBlock069InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock069Output a) =
      generatedSixthXiShortBlock069OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block069_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock069InputMask a) =
      generatedSixthXiShortBlock069OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock069InputMask a)) *
      generatedSixthXiShortBlock069InputNumerator a =
        generatedSixthXiShortBlock069OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block069_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock069Input a
    let y := generatedSixthXiShortBlock069Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block069_cache a
  have hs := generatedSixth_xi_short_block069_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block069_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock069Input a
    let y := generatedSixthXiShortBlock069Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block069_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block069_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock069Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block069_certificate a).1
    (generatedSixth_xi_short_block069_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
