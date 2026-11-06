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
def generatedSixthXiShortBlock048Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (98, 7)),
    Sum.inr (Sum.inl (62, 60)),
    Sum.inr (Sum.inl (59, 28)),
    Sum.inr (Sum.inl (183, 44)),
    Sum.inr (Sum.inl (135, 14)),
    Sum.inr (Sum.inl (199, 54)),
    Sum.inr (Sum.inl (85, 45)),
    Sum.inr (Sum.inl (219, 56)),
    Sum.inr (Sum.inl (85, 9)),
    Sum.inr (Sum.inl (219, 6)),
    Sum.inr (Sum.inl (135, 62)),
    Sum.inr (Sum.inl (199, 8)),
    Sum.inr (Sum.inl (59, 3)),
    Sum.inr (Sum.inl (183, 18)),
    Sum.inr (Sum.inl (98, 47)),
    Sum.inr (Sum.inl (62, 2)),
    Sum.inr (Sum.inl (59, 15)),
    Sum.inr (Sum.inl (183, 30)),
    Sum.inr (Sum.inl (98, 44)),
    Sum.inr (Sum.inl (62, 14)),
    Sum.inr (Sum.inl (85, 11)),
    Sum.inr (Sum.inl (219, 14)),
    Sum.inr (Sum.inl (135, 60)),
    Sum.inr (Sum.inl (199, 26)),
    Sum.inr (Sum.inl (85, 62)),
    Sum.inr (Sum.inl (219, 18)),
    Sum.inr (Sum.inl (135, 55)),
    Sum.inr (Sum.inl (199, 32)),
    Sum.inr (Sum.inl (59, 17)),
    Sum.inr (Sum.inl (183, 2)),
    Sum.inr (Sum.inl (98, 63)),
    Sum.inr (Sum.inl (62, 32)),
    Sum.inr (Sum.inl (59, 29)),
    Sum.inr (Sum.inl (183, 14)),
    Sum.inr (Sum.inl (98, 60)),
    Sum.inr (Sum.inl (62, 44)),
    Sum.inr (Sum.inl (85, 60)),
    Sum.inr (Sum.inl (219, 26)),
    Sum.inr (Sum.inl (135, 53)),
    Sum.inr (Sum.inl (199, 50)),
    Sum.inr (Sum.inl (117, 36)),
    Sum.inr (Sum.inl (106, 12)),
    Sum.inr (Sum.inl (194, 48)),
    Sum.inr (Sum.inl (218, 47)),
    Sum.inr (Sum.inl (74, 45)),
    Sum.inr (Sum.inl (127, 50)),
    Sum.inr (Sum.inl (42, 50)),
    Sum.inr (Sum.inl (184, 11)),
    Sum.inr (Sum.inl (117, 39)),
    Sum.inr (Sum.inl (106, 14)),
    Sum.inr (Sum.inl (194, 50)),
    Sum.inr (Sum.inl (218, 35)),
    Sum.inr (Sum.inl (74, 63)),
    Sum.inr (Sum.inl (127, 62)),
    Sum.inr (Sum.inl (42, 62)),
    Sum.inr (Sum.inl (184, 3)),
    Sum.inr (Sum.inl (106, 9)),
    Sum.inr (Sum.inl (117, 59)),
    Sum.inr (Sum.inl (218, 62)),
    Sum.inr (Sum.inl (194, 31)),
    Sum.inr (Sum.inl (127, 35)),
    Sum.inr (Sum.inl (74, 26)),
    Sum.inr (Sum.inl (184, 26)),
    Sum.inr (Sum.inl (42, 29)),
    Sum.inr (Sum.inl (106, 11)),
    Sum.inr (Sum.inl (117, 56)),
    Sum.inr (Sum.inl (218, 50)),
    Sum.inr (Sum.inl (194, 29)),
    Sum.inr (Sum.inl (127, 47)),
    Sum.inr (Sum.inl (74, 8)),
    Sum.inr (Sum.inl (184, 18)),
    Sum.inr (Sum.inl (42, 17)),
    Sum.inr (Sum.inl (194, 17)),
    Sum.inr (Sum.inl (218, 18)),
    Sum.inr (Sum.inl (117, 32)),
    Sum.inr (Sum.inl (106, 59)),
    Sum.inr (Sum.inl (42, 19)),
    Sum.inr (Sum.inl (184, 41)),
    Sum.inr (Sum.inl (74, 41)),
    Sum.inr (Sum.inl (127, 45)),
    Sum.inr (Sum.inl (194, 19)),
    Sum.inr (Sum.inl (218, 30)),
    Sum.inr (Sum.inl (117, 35)),
    Sum.inr (Sum.inl (106, 57)),
    Sum.inr (Sum.inl (42, 31)),
    Sum.inr (Sum.inl (184, 33)),
    Sum.inr (Sum.inl (74, 59)),
    Sum.inr (Sum.inl (127, 33)),
    Sum.inr (Sum.inl (218, 3)),
    Sum.inr (Sum.inl (194, 62)),
    Sum.inr (Sum.inl (106, 62)),
    Sum.inr (Sum.inl (117, 63)),
    Sum.inr (Sum.inl (184, 56)),
    Sum.inr (Sum.inl (42, 60)),
    Sum.inr (Sum.inl (127, 60)),
    Sum.inr (Sum.inl (74, 30)),
    Sum.inr (Sum.inl (218, 15)),
    Sum.inr (Sum.inl (194, 60)),
    Sum.inr (Sum.inl (106, 60)),
    Sum.inr (Sum.inl (117, 60)),
    Sum.inr (Sum.inl (184, 48)),
    Sum.inr (Sum.inl (42, 48)),
    Sum.inr (Sum.inl (127, 48)),
    Sum.inr (Sum.inl (74, 12)),
    Sum.inr (Sum.inl (61, 25)),
    Sum.inr (Sum.inl (113, 60)),
    Sum.inr (Sum.inl (89, 11)),
    Sum.inr (Sum.inl (193, 23)),
    Sum.inr (Sum.inl (221, 57)),
    Sum.inr (Sum.inl (131, 21)),
    Sum.inr (Sum.inl (57, 29)),
    Sum.inr (Sum.inl (185, 7)),
    Sum.inr (Sum.inl (61, 11)),
    Sum.inr (Sum.inl (113, 52)),
    Sum.inr (Sum.inl (89, 15)),
    Sum.inr (Sum.inl (193, 15)),
    Sum.inr (Sum.inl (221, 45)),
    Sum.inr (Sum.inl (131, 7)),
    Sum.inr (Sum.inl (57, 15)),
    Sum.inr (Sum.inl (185, 15)),
    Sum.inr (Sum.inl (89, 41)),
    Sum.inr (Sum.inl (193, 19)),
    Sum.inr (Sum.inl (61, 29)),
    Sum.inr (Sum.inl (113, 7)),
    Sum.inr (Sum.inl (57, 60)),
    Sum.inr (Sum.inl (185, 21)),
    Sum.inr (Sum.inl (221, 27)),
    Sum.inr (Sum.inl (131, 29)),
    Sum.inr (Sum.inl (89, 45)),
    Sum.inr (Sum.inl (193, 11)),
    Sum.inr (Sum.inl (61, 15)),
    Sum.inr (Sum.inl (113, 15)),
    Sum.inr (Sum.inl (57, 46)),
    Sum.inr (Sum.inl (185, 29)),
    Sum.inr (Sum.inl (221, 15)),
    Sum.inr (Sum.inl (131, 15)),
    Sum.inr (Sum.inl (113, 30)),
    Sum.inr (Sum.inl (61, 46)),
    Sum.inr (Sum.inl (193, 42)),
    Sum.inr (Sum.inl (89, 60)),
    Sum.inr (Sum.inl (131, 52)),
    Sum.inr (Sum.inl (221, 49)),
    Sum.inr (Sum.inl (185, 38)),
    Sum.inr (Sum.inl (57, 21)),
    Sum.inr (Sum.inl (113, 22)),
    Sum.inr (Sum.inl (61, 60)),
    Sum.inr (Sum.inl (193, 50)),
    Sum.inr (Sum.inl (89, 56)),
    Sum.inr (Sum.inl (131, 38)),
    Sum.inr (Sum.inl (221, 37)),
    Sum.inr (Sum.inl (185, 46)),
    Sum.inr (Sum.inl (57, 7)),
    Sum.inr (Sum.inl (193, 46)),
    Sum.inr (Sum.inl (89, 30)),
    Sum.inr (Sum.inl (113, 37)),
    Sum.inr (Sum.inl (61, 42)),
    Sum.inr (Sum.inl (185, 52)),
    Sum.inr (Sum.inl (57, 52)),
    Sum.inr (Sum.inl (131, 60)),
    Sum.inr (Sum.inl (221, 19)),
    Sum.inr (Sum.inl (193, 54)),
    Sum.inr (Sum.inl (89, 26)),
    Sum.inr (Sum.inl (113, 45)),
    Sum.inr (Sum.inl (61, 56)),
    Sum.inr (Sum.inl (185, 60)),
    Sum.inr (Sum.inl (57, 38)),
    Sum.inr (Sum.inl (131, 46)),
    Sum.inr (Sum.inl (221, 7)),
    Sum.inr (Sum.inl (108, 55)),
    Sum.inr (Sum.inl (138, 40)),
    Sum.inr (Sum.inl (108, 59)),
    Sum.inr (Sum.inl (138, 32)),
    Sum.inr (Sum.inl (216, 21)),
    Sum.inr (Sum.inl (154, 23)),
    Sum.inr (Sum.inl (216, 23)),
    Sum.inr (Sum.inl (154, 27)),
    Sum.inr (Sum.inl (91, 53)),
    Sum.inr (Sum.inl (125, 7)),
    Sum.inr (Sum.inl (91, 39)),
    Sum.inr (Sum.inl (125, 11)),
    Sum.inr (Sum.inl (41, 9)),
    Sum.inr (Sum.inl (186, 1)),
    Sum.inr (Sum.inl (41, 10)),
    Sum.inr (Sum.inl (186, 3)),
    Sum.inr (Sum.inl (216, 61)),
    Sum.inr (Sum.inl (154, 55)),
    Sum.inr (Sum.inl (216, 63)),
    Sum.inr (Sum.inl (154, 59)),
    Sum.inr (Sum.inl (108, 53)),
    Sum.inr (Sum.inl (138, 19)),
    Sum.inr (Sum.inl (108, 57)),
    Sum.inr (Sum.inl (138, 27)),
    Sum.inr (Sum.inl (41, 45)),
    Sum.inr (Sum.inl (186, 21)),
    Sum.inr (Sum.inl (41, 46)),
    Sum.inr (Sum.inl (186, 23)),
    Sum.inr (Sum.inl (91, 20)),
    Sum.inr (Sum.inl (125, 5)),
    Sum.inr (Sum.inl (91, 6)),
    Sum.inr (Sum.inl (125, 9)),
    Sum.inr (Sum.inl (138, 10)),
    Sum.inr (Sum.inl (108, 40)),
    Sum.inr (Sum.inl (138, 2)),
    Sum.inr (Sum.inl (108, 36)),
    Sum.inr (Sum.inl (154, 42)),
    Sum.inr (Sum.inl (216, 58)),
    Sum.inr (Sum.inl (154, 38)),
    Sum.inr (Sum.inl (216, 56)),
    Sum.inr (Sum.inl (125, 38)),
    Sum.inr (Sum.inl (91, 49)),
    Sum.inr (Sum.inl (125, 42)),
    Sum.inr (Sum.inl (91, 35)),
    Sum.inr (Sum.inl (186, 32)),
    Sum.inr (Sum.inl (41, 1)),
    Sum.inr (Sum.inl (186, 34)),
    Sum.inr (Sum.inl (41, 2)),
    Sum.inr (Sum.inl (154, 10)),
    Sum.inr (Sum.inl (216, 18)),
    Sum.inr (Sum.inl (154, 6)),
    Sum.inr (Sum.inl (216, 16)),
    Sum.inr (Sum.inl (138, 49)),
    Sum.inr (Sum.inl (108, 42)),
    Sum.inr (Sum.inl (138, 57)),
    Sum.inr (Sum.inl (108, 38)),
    Sum.inr (Sum.inl (186, 52)),
    Sum.inr (Sum.inl (41, 37)),
    Sum.inr (Sum.inl (186, 54)),
    Sum.inr (Sum.inl (41, 38)),
    Sum.inr (Sum.inl (125, 36)),
    Sum.inr (Sum.inl (91, 16)),
    Sum.inr (Sum.inl (125, 40)),
    Sum.inr (Sum.inl (91, 2)),
    Sum.inr (Sum.inr (498, 15)),
    Sum.inr (Sum.inr (173, 1)),
    Sum.inr (Sum.inr (505, 15)),
    Sum.inr (Sum.inr (166, 1)),
    Sum.inr (Sum.inr (173, 11)),
    Sum.inr (Sum.inr (498, 22)),
    Sum.inr (Sum.inr (166, 11)),
    Sum.inr (Sum.inr (505, 22)),
    Sum.inr (Sum.inr (39, 15)),
    Sum.inr (Sum.inr (376, 1)),
    Sum.inr (Sum.inr (44, 15)),
    Sum.inr (Sum.inr (371, 1)),
    Sum.inr (Sum.inr (376, 11)),
    Sum.inr (Sum.inr (39, 22)),
    Sum.inr (Sum.inr (371, 11)),
    Sum.inr (Sum.inr (44, 22)),
    Sum.inr (Sum.inr (236, 15)),
    Sum.inr (Sum.inr (435, 1)),
    Sum.inr (Sum.inr (231, 15)),
    Sum.inr (Sum.inr (440, 1)),
    Sum.inr (Sum.inr (435, 11)),
    Sum.inr (Sum.inr (236, 22)),
    Sum.inr (Sum.inr (440, 11)),
    Sum.inr (Sum.inr (231, 22))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock048Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨12288 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock048InputMaskData : ℕ :=
  sixthHex% [
    "28c572717572198572403d721295724b2d7223dd727a6d7242c5721b7572",
    "7385722a3d72789572212d7249dd72106d723ba572621d720aed72535d72",
    "01fd72584d7230bd726905726aed1f335d1f13ad1f4a151f51bd1f08051f",
    "28f51f71451f798d1f20351f00c51f59751f42d51f1b651f3b951f622d1f",
    "468d1f1f351f3fc51f66751f7dd51f24651f04951f5d2d1f55e51f0c551f",
    "2ca51f751d1f6eb51f370d1f17fd1f4e4d1f6c8d1f35351f15c51f4c751f",
    "57d51f0e651f2e951f772d1f7fe51f26551f06a51f5f1d1f44b51f1d0d1f",
    "3dfd1f644d1f40e51f19551f39a51f601d1f7bb51f220d1f02fd1f5b4d1f",
    "53851f0a3d1f2acd1f737d1f68dd1f316d1f119d1f48251f49db2969ab29",
    "59ab2979d329494b29693329593329794329084b29283329183329384329",
    "08d32928a32918a32938db291c7b293c03290c03292c73291ce3293c9329",
    "0c93292ceb295de3297d93294d93296deb295d73297d0b294d0b296d7b29",
    "367b2916032926032906732936e32916932926932906eb2977e329579329",
    "67932947eb29777329570b29670b29477b2963d32943a32973a32953db29",
    "634329433b29733b29534b29224329023b29323b29124b2922db2902ab29",
    "32ab2912d3295855c961e5c931e5c9085dc911e5c9285dc9785dc941edc9",
    "6d15c954adc904adc93d1dc924adc91d1dc94d1dc974a5c92105c918bdc9",
    "48bdc9710dc968bdc9510dc9010dc938b5c9144dc92dfdc97dfdc94445c9",
    "5dfdc96445c93445c90df5c97435c94d8dc91d8dc9243dc93d8dc9043dc9",
    "543dc96d85c9417dc978cdc928cdc91175c908cdc93175c96175c958c5c9",
    "0d6dc934ddc964ddc95d65c944ddc97d65c92d65c914d5c9382dc90195c9",
    "5195c96825c97195c94825c91825c9219dc954fb4a748b4a448b4a64f34a",
    "107b4a30034a00034a20734a187b4a38034a08034a28734a5cf34a7c834a",
    "4c834a6cfb4a545b4a74234a44234a64534a10d34a30a34a00a34a20db4a",
    "18d34a38a34a08a34a28db4a5c534a7c2b4a4c2b4a6c5b4a015b4a21234a",
    "11234a31534a45d34a65a34a55a34a75db4a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock048InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock048InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock048OutputMaskData : ℕ :=
  sixthHex% [
    "a99397fee6e8addb9c8beee39d06e8bb3397e80ee3bf7b9ce000bcb775c3",
    "e448b7c27dc8d495c3f2a0bca19dc8f6e8b7a577d98342a6d07fd2870aad",
    "e0a2a6b7d7d9e4eaadc2dfd2250e3f727b405c4e3f7a7b4006006020351f",
    "0e006059751f29ea710fdf0e21ea71769f0e7ba42e2cd15102e42e24d151",
    "113860370d1f1938604e4d1f43763f1403403a363f1c03406c9c2e3be951",
    "15dc2e33e9514f927169a70e47927110e70e2dab400b9e3f25ab4072de3f",
    "7fe51f28906006a51f209060500f0e077a71294f0e0f7a7173015155342e",
    "7b01512c742e68dd1f3fa860119d1f37a8604bd3406de63f43d34014a63f",
    "643951420c2e6c39513b4c2e36770e6102714f370e6902712e00093ca213",
    "1a313379d3290d0b226ee938487a185ad8026f90090c72132ae133384329",
    "3ddb222f793809ea186a08025fe1333c03291a90090832130daa181f0802",
    "399b225a79386f31337d93295b000938e2134c3a182fd802094b221be938",
    "63721300900926032934a133313938239b2205080266ea1853a213410009",
    "67932904713370a938134b2235d802277a1863d32971713357e213340009",
    "40d802233a1805a938170b2222432941a13367321375900970080262aa18",
    "44393827db22523fd874039623d98774a5c92790bd70ecf32736e2010aac",
    "6777d8300b9667d18741edc96398bd45a4f3127ee24502ac34e396639fd8",
    "3445c9127987300cf31630bd41eaac1696e270eb9656d7d8010dc9567187",
    "0544f35238bd05e2ac23dee26609873175c966afd840939662e6e244daac",
    "1300bd447cf3220187043dc953e7d8049b9657aee200d2ac5708bd7134f3",
    "7195c957a987007396570fd8043aac5346e2049cf322a0bd44ddc913a187",
    "447b966247d84032ac660ee231d4f366a8bd1c65150ec70f28542f4bb635",
    "64f27007106a21834a3321506cfa700f186a298b4a3b2950652d15778f0f",
    "511c2f32fe351cc5157f270f59b42f4b163515127007b06a21234a42c150",
    "1d1a700fb86a292b4a4ac950658d15066f0f20fc2f325e356d842f0e6635",
    "28f5153a570f64534a76f15050627033806a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock048OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock048OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock048InputNumeratorData : ℕ :=
  sixthHex% [
    "7e17df8617e185f8617df85f7df85f7e17df85f7df86185f86185f7e1861",
    "86185f7e18617e18617df7e17df7e185f7df85f7df86185f85f7df86185f",
    "86185f7e18618617e185f86185f8617df85f85f8617df85f7df85f7e17df",
    "85f8617df85f7df85f7e17df7df85f7e17df7e17df8617e17e17df8617e1",
    "8617e185f8618617e185f86185f8617df85f8617e185f86185f8617df85f",
    "85f8617df85f7df85f7e17df7df85f7e17df7e17df8617e17e17df8617e1",
    "8617e185f8617e17df8617e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock048InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock048InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock048OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df7df7e17e186186185f86185f85f7df8617e17e17df85f8618617e1",
    "85f8618617e17df85f85f86185f8618617e17df85f85f8617df85f85f861",
    "7e17df7df85f8617e185f86185f8617df85f85f8617df85f7df85f7e17df",
    "85f8617df85f7df85f7e17df7df85f7e17df7e17df8617e185f8618617e1",
    "8617e17e17df7df85f85f86185f8618617e17df85f85f86185f8618617e1",
    "7e17df7df85f7df85f85f86186185f7e186185f7df86185f85f7df86185f",
    "7df7e185f7df7e18617df7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock048OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock048OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block048_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock048Input a) =
      generatedSixthXiShortBlock048InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock048Output a) =
      generatedSixthXiShortBlock048OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock048Input a) =
      generatedSixthXiShortBlock048InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock048Output a) =
      generatedSixthXiShortBlock048OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block048_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock048InputMask a) =
      generatedSixthXiShortBlock048OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock048InputMask a)) *
      generatedSixthXiShortBlock048InputNumerator a =
        generatedSixthXiShortBlock048OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block048_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock048Input a
    let y := generatedSixthXiShortBlock048Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block048_cache a
  have hs := generatedSixth_xi_short_block048_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block048_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock048Input a
    let y := generatedSixthXiShortBlock048Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block048_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block048_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock048Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block048_certificate a).1
    (generatedSixth_xi_short_block048_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
