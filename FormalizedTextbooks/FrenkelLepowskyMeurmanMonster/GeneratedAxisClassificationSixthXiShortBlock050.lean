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
def generatedSixthXiShortBlock050Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (162, 24)),
    Sum.inr (Sum.inl (223, 29)),
    Sum.inr (Sum.inl (86, 2)),
    Sum.inr (Sum.inl (77, 35)),
    Sum.inr (Sum.inl (100, 37)),
    Sum.inr (Sum.inl (134, 8)),
    Sum.inr (Sum.inl (191, 28)),
    Sum.inr (Sum.inl (44, 34)),
    Sum.inr (Sum.inl (134, 13)),
    Sum.inr (Sum.inl (100, 32)),
    Sum.inr (Sum.inl (44, 13)),
    Sum.inr (Sum.inl (191, 33)),
    Sum.inr (Sum.inl (223, 12)),
    Sum.inr (Sum.inl (162, 29)),
    Sum.inr (Sum.inl (77, 12)),
    Sum.inr (Sum.inl (86, 29)),
    Sum.inr (Sum.inl (134, 18)),
    Sum.inr (Sum.inl (100, 42)),
    Sum.inr (Sum.inl (44, 4)),
    Sum.inr (Sum.inl (191, 41)),
    Sum.inr (Sum.inl (223, 49)),
    Sum.inr (Sum.inl (162, 2)),
    Sum.inr (Sum.inl (77, 44)),
    Sum.inr (Sum.inl (86, 20)),
    Sum.inr (Sum.inl (100, 48)),
    Sum.inr (Sum.inl (134, 7)),
    Sum.inr (Sum.inl (191, 48)),
    Sum.inr (Sum.inl (44, 11)),
    Sum.inr (Sum.inl (162, 13)),
    Sum.inr (Sum.inl (223, 4)),
    Sum.inr (Sum.inl (86, 13)),
    Sum.inr (Sum.inl (77, 6)),
    Sum.inr (Sum.inl (100, 58)),
    Sum.inr (Sum.inl (134, 24)),
    Sum.inr (Sum.inl (191, 56)),
    Sum.inr (Sum.inl (44, 2)),
    Sum.inr (Sum.inl (162, 18)),
    Sum.inr (Sum.inl (223, 57)),
    Sum.inr (Sum.inl (86, 4)),
    Sum.inr (Sum.inl (77, 38)),
    Sum.inr (Sum.inl (102, 24)),
    Sum.inr (Sum.inl (58, 40)),
    Sum.inr (Sum.inl (102, 20)),
    Sum.inr (Sum.inl (58, 32)),
    Sum.inr (Sum.inl (121, 10)),
    Sum.inr (Sum.inl (84, 55)),
    Sum.inr (Sum.inl (121, 8)),
    Sum.inr (Sum.inl (84, 59)),
    Sum.inr (Sum.inl (121, 46)),
    Sum.inr (Sum.inl (84, 39)),
    Sum.inr (Sum.inl (121, 44)),
    Sum.inr (Sum.inl (84, 43)),
    Sum.inr (Sum.inl (102, 38)),
    Sum.inr (Sum.inl (58, 22)),
    Sum.inr (Sum.inl (102, 42)),
    Sum.inr (Sum.inl (58, 30)),
    Sum.inr (Sum.inl (58, 12)),
    Sum.inr (Sum.inl (102, 8)),
    Sum.inr (Sum.inl (58, 4)),
    Sum.inr (Sum.inl (102, 4)),
    Sum.inr (Sum.inl (84, 10)),
    Sum.inr (Sum.inl (121, 61)),
    Sum.inr (Sum.inl (84, 6)),
    Sum.inr (Sum.inl (121, 63)),
    Sum.inr (Sum.inl (84, 26)),
    Sum.inr (Sum.inl (121, 25)),
    Sum.inr (Sum.inl (84, 22)),
    Sum.inr (Sum.inl (121, 27)),
    Sum.inr (Sum.inl (58, 50)),
    Sum.inr (Sum.inl (102, 54)),
    Sum.inr (Sum.inl (58, 58)),
    Sum.inr (Sum.inl (102, 58)),
    Sum.inr (Sum.inl (161, 6)),
    Sum.inr (Sum.inl (220, 24)),
    Sum.inr (Sum.inl (161, 20)),
    Sum.inr (Sum.inl (220, 20)),
    Sum.inr (Sum.inl (63, 10)),
    Sum.inr (Sum.inl (192, 18)),
    Sum.inr (Sum.inl (63, 9)),
    Sum.inr (Sum.inl (192, 16)),
    Sum.inr (Sum.inl (63, 30)),
    Sum.inr (Sum.inl (192, 30)),
    Sum.inr (Sum.inl (63, 29)),
    Sum.inr (Sum.inl (192, 28)),
    Sum.inr (Sum.inl (161, 56)),
    Sum.inr (Sum.inl (220, 38)),
    Sum.inr (Sum.inl (161, 42)),
    Sum.inr (Sum.inl (220, 42)),
    Sum.inr (Sum.inl (220, 10)),
    Sum.inr (Sum.inl (161, 34)),
    Sum.inr (Sum.inl (220, 6)),
    Sum.inr (Sum.inl (161, 48)),
    Sum.inr (Sum.inl (192, 3)),
    Sum.inr (Sum.inl (63, 2)),
    Sum.inr (Sum.inl (192, 1)),
    Sum.inr (Sum.inl (63, 1)),
    Sum.inr (Sum.inl (192, 15)),
    Sum.inr (Sum.inl (63, 22)),
    Sum.inr (Sum.inl (192, 13)),
    Sum.inr (Sum.inl (63, 21)),
    Sum.inr (Sum.inl (220, 52)),
    Sum.inr (Sum.inl (161, 28)),
    Sum.inr (Sum.inl (220, 56)),
    Sum.inr (Sum.inl (161, 14)),
    Sum.inr (Sum.inl (221, 2)),
    Sum.inr (Sum.inl (89, 61)),
    Sum.inr (Sum.inl (185, 34)),
    Sum.inr (Sum.inl (113, 36)),
    Sum.inr (Sum.inl (221, 32)),
    Sum.inr (Sum.inl (89, 31)),
    Sum.inr (Sum.inl (185, 48)),
    Sum.inr (Sum.inl (113, 31)),
    Sum.inr (Sum.inl (57, 19)),
    Sum.inr (Sum.inl (61, 41)),
    Sum.inr (Sum.inl (131, 58)),
    Sum.inr (Sum.inl (193, 35)),
    Sum.inr (Sum.inl (57, 50)),
    Sum.inr (Sum.inl (61, 45)),
    Sum.inr (Sum.inl (131, 50)),
    Sum.inr (Sum.inl (193, 39)),
    Sum.inr (Sum.inl (57, 1)),
    Sum.inr (Sum.inl (61, 59)),
    Sum.inr (Sum.inl (131, 40)),
    Sum.inr (Sum.inl (193, 59)),
    Sum.inr (Sum.inl (57, 32)),
    Sum.inr (Sum.inl (61, 63)),
    Sum.inr (Sum.inl (131, 32)),
    Sum.inr (Sum.inl (193, 63)),
    Sum.inr (Sum.inl (221, 22)),
    Sum.inr (Sum.inl (89, 57)),
    Sum.inr (Sum.inl (185, 42)),
    Sum.inr (Sum.inl (113, 44)),
    Sum.inr (Sum.inl (221, 52)),
    Sum.inr (Sum.inl (89, 27)),
    Sum.inr (Sum.inl (185, 56)),
    Sum.inr (Sum.inl (113, 23)),
    Sum.inr (Sum.inl (89, 44)),
    Sum.inr (Sum.inl (221, 60)),
    Sum.inr (Sum.inl (113, 53)),
    Sum.inr (Sum.inl (185, 25)),
    Sum.inr (Sum.inl (89, 14)),
    Sum.inr (Sum.inl (221, 30)),
    Sum.inr (Sum.inl (113, 14)),
    Sum.inr (Sum.inl (185, 11)),
    Sum.inr (Sum.inl (61, 8)),
    Sum.inr (Sum.inl (57, 40)),
    Sum.inr (Sum.inl (193, 2)),
    Sum.inr (Sum.inl (131, 1)),
    Sum.inr (Sum.inl (61, 12)),
    Sum.inr (Sum.inl (57, 9)),
    Sum.inr (Sum.inl (193, 6)),
    Sum.inr (Sum.inl (131, 9)),
    Sum.inr (Sum.inl (61, 26)),
    Sum.inr (Sum.inl (57, 58)),
    Sum.inr (Sum.inl (193, 26)),
    Sum.inr (Sum.inl (131, 19)),
    Sum.inr (Sum.inl (61, 30)),
    Sum.inr (Sum.inl (57, 27)),
    Sum.inr (Sum.inl (193, 30)),
    Sum.inr (Sum.inl (131, 27)),
    Sum.inr (Sum.inl (89, 40)),
    Sum.inr (Sum.inl (221, 40)),
    Sum.inr (Sum.inl (113, 61)),
    Sum.inr (Sum.inl (185, 17)),
    Sum.inr (Sum.inl (89, 10)),
    Sum.inr (Sum.inl (221, 10)),
    Sum.inr (Sum.inl (113, 6)),
    Sum.inr (Sum.inl (185, 3)),
    Sum.inr (Sum.inl (127, 34)),
    Sum.inr (Sum.inl (184, 36)),
    Sum.inr (Sum.inl (127, 46)),
    Sum.inr (Sum.inl (184, 44)),
    Sum.inr (Sum.inl (106, 40)),
    Sum.inr (Sum.inl (218, 63)),
    Sum.inr (Sum.inl (106, 42)),
    Sum.inr (Sum.inl (218, 51)),
    Sum.inr (Sum.inl (106, 24)),
    Sum.inr (Sum.inl (218, 31)),
    Sum.inr (Sum.inl (106, 26)),
    Sum.inr (Sum.inl (218, 19)),
    Sum.inr (Sum.inl (127, 32)),
    Sum.inr (Sum.inl (184, 31)),
    Sum.inr (Sum.inl (127, 44)),
    Sum.inr (Sum.inl (184, 23)),
    Sum.inr (Sum.inl (74, 50)),
    Sum.inr (Sum.inl (42, 13)),
    Sum.inr (Sum.inl (74, 32)),
    Sum.inr (Sum.inl (42, 1)),
    Sum.inr (Sum.inl (117, 11)),
    Sum.inr (Sum.inl (194, 7)),
    Sum.inr (Sum.inl (117, 8)),
    Sum.inr (Sum.inl (194, 5)),
    Sum.inr (Sum.inl (117, 19)),
    Sum.inr (Sum.inl (194, 11)),
    Sum.inr (Sum.inl (117, 16)),
    Sum.inr (Sum.inl (194, 9)),
    Sum.inr (Sum.inl (74, 19)),
    Sum.inr (Sum.inl (42, 15)),
    Sum.inr (Sum.inl (74, 1)),
    Sum.inr (Sum.inl (42, 3)),
    Sum.inr (Sum.inl (184, 6)),
    Sum.inr (Sum.inl (127, 61)),
    Sum.inr (Sum.inl (184, 14)),
    Sum.inr (Sum.inl (127, 49)),
    Sum.inr (Sum.inl (218, 2)),
    Sum.inr (Sum.inl (106, 31)),
    Sum.inr (Sum.inl (218, 14)),
    Sum.inr (Sum.inl (106, 29)),
    Sum.inr (Sum.inl (218, 34)),
    Sum.inr (Sum.inl (106, 47)),
    Sum.inr (Sum.inl (218, 46)),
    Sum.inr (Sum.inl (106, 45)),
    Sum.inr (Sum.inl (184, 61)),
    Sum.inr (Sum.inl (127, 63)),
    Sum.inr (Sum.inl (184, 53)),
    Sum.inr (Sum.inl (127, 51)),
    Sum.inr (Sum.inl (42, 44)),
    Sum.inr (Sum.inl (74, 54)),
    Sum.inr (Sum.inl (42, 32)),
    Sum.inr (Sum.inl (74, 36)),
    Sum.inr (Sum.inl (194, 38)),
    Sum.inr (Sum.inl (117, 15)),
    Sum.inr (Sum.inl (194, 36)),
    Sum.inr (Sum.inl (117, 12)),
    Sum.inr (Sum.inl (194, 42)),
    Sum.inr (Sum.inl (117, 23)),
    Sum.inr (Sum.inl (194, 40)),
    Sum.inr (Sum.inl (117, 20)),
    Sum.inr (Sum.inl (42, 46)),
    Sum.inr (Sum.inl (74, 23)),
    Sum.inr (Sum.inl (42, 34)),
    Sum.inr (Sum.inl (74, 5)),
    Sum.inr (Sum.inr (189, 1)),
    Sum.inr (Sum.inr (482, 22)),
    Sum.inr (Sum.inr (489, 22)),
    Sum.inr (Sum.inr (182, 1)),
    Sum.inr (Sum.inr (125, 22)),
    Sum.inr (Sum.inr (290, 1)),
    Sum.inr (Sum.inr (297, 1)),
    Sum.inr (Sum.inr (118, 22)),
    Sum.inr (Sum.inr (189, 15)),
    Sum.inr (Sum.inr (482, 11)),
    Sum.inr (Sum.inr (489, 11)),
    Sum.inr (Sum.inr (182, 15)),
    Sum.inr (Sum.inr (125, 11)),
    Sum.inr (Sum.inr (290, 15)),
    Sum.inr (Sum.inr (297, 15)),
    Sum.inr (Sum.inr (118, 11)),
    Sum.inr (Sum.inr (55, 22)),
    Sum.inr (Sum.inr (360, 1)),
    Sum.inr (Sum.inr (355, 1)),
    Sum.inr (Sum.inr (60, 22)),
    Sum.inr (Sum.inr (247, 1)),
    Sum.inr (Sum.inr (424, 22)),
    Sum.inr (Sum.inr (419, 22)),
    Sum.inr (Sum.inr (252, 1))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock050Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨12800 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock050InputMaskData : ℕ :=
  sixthHex% [
    "4da06d20206d68206d05a86d62306d0fb86d47b86d2a386d0e906d63106d",
    "2b106d46986d21006d4c886d04886d69086d20006d4d886d05886d68086d",
    "0f986d62186d2a186d47906d7bcee2127ee24e8ee22736e2439ee22a26e2",
    "76d6e21f66e202aee26b16e237e6e25e56e23af6e25346e20fb6e2660ee2",
    "68aee20116e25de6e23456e250f6e23946e265b6e20c0ee211c6e27876e2",
    "2486e24d3ee22996e2402ee21cdee2756ee257aee23e16e262e6e20b56e2",
    "6ff6e20646e25ab6e2330ee22ec6e24776e21b86e2723ee21696e27f2ee2",
    "23dee24a6ee244c6e22d76e27186e2183ee27c96e2152ee249dee2206ee2",
    "3da6e2541ee208eee2615ee205fee26c4ee230bee25906e22ad0023f0002",
    "5f00024ad8026f00027ad8021ad8020f08024f00025ad8023ad8022f0802",
    "0ad8021f08027f08026ad0027fd0026a08020a08021fd8023a08022fd802",
    "4fd8025a00021a08020fd8026fd8027a00025fd8024a00022a00023fd002",
    "15d00200080260080275d80250080245d80225d80230000270080265d802",
    "05d80210000235d80220000240000255d00240d80255080235080220d002",
    "05080210d00270d00265000225080230d00250d00245000260d002750002",
    "15000200d80255fe813c4e8168be810106812cae8145168111e681785681",
    "469e812f26817bd6811266813fc6815676810286816b3e81799e81102681",
    "44d6812d668100c6816976813d8681543e816af68103468157b6813e0e81",
    "13a6817a1e812eee81475e81539e813a26816ed6810766812ac681437681",
    "1786817e3e8140f6812946817db681140e8139a681501e8104ee816d5e81",
    "7ff68116468142b6812b0e8106a6816f1e813bee81525e816c9681052e81",
    "51de81386e8115ce817c7e81288e8141368176a80a1b080a71080a1ca00a",
    "4e080a23a00a49a00a24000a64080a09a00a63a00a0e000a5ca00a31000a",
    "5b000a36a80a1ba80a76000a1c000a71a00a23000a4ea00a24a00a49080a",
    "09000a64a00a0ea00a63080a31a00a5c080a36080a5ba80a6da80a00000a",
    "6a000a07a00a55000a38a00a52a00a3f080a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock050InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock050InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock050OutputMaskData : ℕ :=
  sixthHex% [
    "df0bfcbc4683c14e88d343f7e608dcf405a3890da8ea40d7aee9e6cda499",
    "b0ac92a2a1ed97eac685e7b9f8efb29ba2cd8071e6927c99ef74928c39ed",
    "c832c6ab7fb9d677b2c47acd08efd87909873da7d83d01870ca8bd0c0ee2",
    "48a0bd3946e24d98bd4d3ee20990bd7876e2389fd84979870dd7d80d7187",
    "040b9604adc940039631e5c9710cf300eaac4444f344e2ac303cf341daac",
    "0574f305d2ac347b9634ddc97073960195c93cd9873c7fd878d1870937d8",
    "49dee23838bd7c96e27c30bd08eee27908bd3da6e23d00bd0ca9870c0fd8",
    "48a1873947d8417dc9309b967435c9749396453aac459cf30132ac70d4f3",
    "040aac04acf34002ac31e4f3710dc900eb964445c944e39622db2930d138",
    "41980922d218670b29044138750809670218634213000802714133634b22",
    "57d21345d80234913357db22539a1330d002419933539322670a13750002",
    "044933670322634329714938000009634a1826932945d938349009269a18",
    "1a0938794329080a181a00092e99383c93294dda182e90092ad00238da13",
    "4993222ad9336f00020c4a137d03226f09331a0802080213794b221a0133",
    "5fd8023c92134ddb225fd1335b913838db294992185b98096f01387d0b29",
    "0c42186f080924cc90552acf198c90192acf4210de42b6810e10de7ff681",
    "2828de288e816428de15ce813fb4904e52cf02f4900252cf10facf105c90",
    "5cfacf2d1c900766817680de3a26813a80de6d5e811cb8de501e8150b8de",
    "0b82cf0b24904782cf3664902c69ef2ccfb06069ef118fb03bf5a14a13fe",
    "06b5a10613fe51cda1202bfe6c8da16c2bfe3711ef37b7b07b11ef0af7b0",
    "691fb018f9ef545fb054f9ef0fc3fe0f65a143c3fe3225a165fbfe655da1",
    "29fbfe581da17267b00381ef4f27b04f81ef2401307b7b2a32e8011cd21b",
    "0a3a1024000a6d932132e93b36a93018932a5100010e7a1b69d21036a80a",
    "7f3b2151013b7bdb2a55e1301c721b43080124a00a7bda1032493b1c7321",
    "18332a4749300eda1b20e00136080a18321051a13b0edb21299a1007a00a",
    "4e332111493b76e130299b2a6008014e321b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock050OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock050OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock050InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df86185f85f7df86185f86185f7e186185f7df86185f7df7e185f7df",
    "86185f7e186185f7df86185f86185f7e186185f7df86185f7e18617df7e1",
    "86185f7e18617df85f85f8617e17df7df85f85f8618617e17df85f85f861",
    "7e17df7df85f8617e17e17df7df85f85f8617e17df7df85f7e17df8617e1",
    "7df85f7e17df7df85f7e17df85f8617df85f8617e185f8617e17df8617e1",
    "7e17df8617e17df85f7e17df7df85f85f8617e17df7df85f7e17df7df85f",
    "8617e17e17df7e17df7df85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock050InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock050InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock050OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e17df7df85f7e17df7df85f7df85f85f8617e17df8617e17df85f7e17df",
    "7df85f7e17df85f8617df85f7df85f7e17df85f8617df85f85f8617df85f",
    "8617e185f86185f7df7df7e186185f85f7df86185f85f7df7e186186185f",
    "86185f85f7df7e186186185f7e186186185f7df7e17e186186185f85f7df",
    "85f7df7df7e17e186186185f86185f85f7df7e186186185f86185f85f7df",
    "7df7e17e18617e186186185f7e17df8617e18617e185f8618617e185f861",
    "85f8617df85f7df85f7e17df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock050OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock050OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block050_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock050Input a) =
      generatedSixthXiShortBlock050InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock050Output a) =
      generatedSixthXiShortBlock050OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock050Input a) =
      generatedSixthXiShortBlock050InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock050Output a) =
      generatedSixthXiShortBlock050OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block050_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock050InputMask a) =
      generatedSixthXiShortBlock050OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock050InputMask a)) *
      generatedSixthXiShortBlock050InputNumerator a =
        generatedSixthXiShortBlock050OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block050_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock050Input a
    let y := generatedSixthXiShortBlock050Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block050_cache a
  have hs := generatedSixth_xi_short_block050_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block050_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock050Input a
    let y := generatedSixthXiShortBlock050Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block050_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block050_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock050Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block050_certificate a).1
    (generatedSixth_xi_short_block050_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
