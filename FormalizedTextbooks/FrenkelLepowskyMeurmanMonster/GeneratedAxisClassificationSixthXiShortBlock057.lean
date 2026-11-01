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
def generatedSixthXiShortBlock057Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (135, 4)),
    Sum.inr (Sum.inl (62, 20)),
    Sum.inr (Sum.inl (59, 4)),
    Sum.inr (Sum.inl (219, 32)),
    Sum.inr (Sum.inl (98, 21)),
    Sum.inr (Sum.inl (199, 60)),
    Sum.inr (Sum.inl (85, 39)),
    Sum.inr (Sum.inl (183, 52)),
    Sum.inr (Sum.inl (85, 3)),
    Sum.inr (Sum.inl (183, 10)),
    Sum.inr (Sum.inl (98, 61)),
    Sum.inr (Sum.inl (199, 2)),
    Sum.inr (Sum.inl (59, 27)),
    Sum.inr (Sum.inl (219, 30)),
    Sum.inr (Sum.inl (135, 52)),
    Sum.inr (Sum.inl (62, 42)),
    Sum.inr (Sum.inl (85, 1)),
    Sum.inr (Sum.inl (183, 6)),
    Sum.inr (Sum.inl (98, 62)),
    Sum.inr (Sum.inl (199, 16)),
    Sum.inr (Sum.inl (59, 23)),
    Sum.inr (Sum.inl (219, 22)),
    Sum.inr (Sum.inl (135, 54)),
    Sum.inr (Sum.inl (62, 38)),
    Sum.inr (Sum.inl (59, 9)),
    Sum.inr (Sum.inl (219, 10)),
    Sum.inr (Sum.inl (135, 61)),
    Sum.inr (Sum.inl (62, 8)),
    Sum.inr (Sum.inl (85, 52)),
    Sum.inr (Sum.inl (183, 26)),
    Sum.inr (Sum.inl (98, 45)),
    Sum.inr (Sum.inl (199, 42)),
    Sum.inr (Sum.inl (59, 5)),
    Sum.inr (Sum.inl (219, 2)),
    Sum.inr (Sum.inl (135, 63)),
    Sum.inr (Sum.inl (62, 4)),
    Sum.inr (Sum.inl (85, 54)),
    Sum.inr (Sum.inl (183, 22)),
    Sum.inr (Sum.inl (98, 46)),
    Sum.inr (Sum.inl (199, 56)),
    Sum.inr (Sum.inl (121, 40)),
    Sum.inr (Sum.inl (161, 51)),
    Sum.inr (Sum.inl (192, 7)),
    Sum.inr (Sum.inl (58, 31)),
    Sum.inr (Sum.inl (63, 7)),
    Sum.inr (Sum.inl (102, 47)),
    Sum.inr (Sum.inl (84, 63)),
    Sum.inr (Sum.inl (220, 15)),
    Sum.inr (Sum.inl (63, 4)),
    Sum.inr (Sum.inl (102, 35)),
    Sum.inr (Sum.inl (84, 51)),
    Sum.inr (Sum.inl (220, 3)),
    Sum.inr (Sum.inl (121, 42)),
    Sum.inr (Sum.inl (161, 33)),
    Sum.inr (Sum.inl (192, 5)),
    Sum.inr (Sum.inl (58, 23)),
    Sum.inr (Sum.inl (192, 22)),
    Sum.inr (Sum.inl (58, 59)),
    Sum.inr (Sum.inl (121, 31)),
    Sum.inr (Sum.inl (161, 23)),
    Sum.inr (Sum.inl (84, 2)),
    Sum.inr (Sum.inl (220, 29)),
    Sum.inr (Sum.inl (63, 15)),
    Sum.inr (Sum.inl (102, 63)),
    Sum.inr (Sum.inl (84, 14)),
    Sum.inr (Sum.inl (220, 17)),
    Sum.inr (Sum.inl (63, 12)),
    Sum.inr (Sum.inl (102, 51)),
    Sum.inr (Sum.inl (192, 20)),
    Sum.inr (Sum.inl (58, 51)),
    Sum.inr (Sum.inl (121, 29)),
    Sum.inr (Sum.inl (161, 5)),
    Sum.inr (Sum.inl (121, 57)),
    Sum.inr (Sum.inl (161, 59)),
    Sum.inr (Sum.inl (192, 24)),
    Sum.inr (Sum.inl (58, 13)),
    Sum.inr (Sum.inl (63, 24)),
    Sum.inr (Sum.inl (102, 13)),
    Sum.inr (Sum.inl (84, 30)),
    Sum.inr (Sum.inl (220, 47)),
    Sum.inr (Sum.inl (63, 27)),
    Sum.inr (Sum.inl (102, 1)),
    Sum.inr (Sum.inl (84, 18)),
    Sum.inr (Sum.inl (220, 35)),
    Sum.inr (Sum.inl (121, 59)),
    Sum.inr (Sum.inl (161, 41)),
    Sum.inr (Sum.inl (192, 26)),
    Sum.inr (Sum.inl (58, 5)),
    Sum.inr (Sum.inl (192, 9)),
    Sum.inr (Sum.inl (58, 41)),
    Sum.inr (Sum.inl (121, 14)),
    Sum.inr (Sum.inl (161, 31)),
    Sum.inr (Sum.inl (84, 35)),
    Sum.inr (Sum.inl (220, 61)),
    Sum.inr (Sum.inl (63, 16)),
    Sum.inr (Sum.inl (102, 29)),
    Sum.inr (Sum.inl (84, 47)),
    Sum.inr (Sum.inl (220, 49)),
    Sum.inr (Sum.inl (63, 19)),
    Sum.inr (Sum.inl (102, 17)),
    Sum.inr (Sum.inl (192, 11)),
    Sum.inr (Sum.inl (58, 33)),
    Sum.inr (Sum.inl (121, 12)),
    Sum.inr (Sum.inl (161, 13)),
    Sum.inr (Sum.inl (193, 40)),
    Sum.inr (Sum.inl (57, 53)),
    Sum.inr (Sum.inl (61, 17)),
    Sum.inr (Sum.inl (131, 53)),
    Sum.inr (Sum.inl (89, 39)),
    Sum.inr (Sum.inl (185, 63)),
    Sum.inr (Sum.inl (113, 43)),
    Sum.inr (Sum.inl (221, 5)),
    Sum.inr (Sum.inl (193, 21)),
    Sum.inr (Sum.inl (57, 61)),
    Sum.inr (Sum.inl (61, 38)),
    Sum.inr (Sum.inl (131, 20)),
    Sum.inr (Sum.inl (89, 16)),
    Sum.inr (Sum.inl (185, 30)),
    Sum.inr (Sum.inl (113, 9)),
    Sum.inr (Sum.inl (221, 13)),
    Sum.inr (Sum.inl (89, 35)),
    Sum.inr (Sum.inl (185, 55)),
    Sum.inr (Sum.inl (113, 35)),
    Sum.inr (Sum.inl (221, 17)),
    Sum.inr (Sum.inl (193, 48)),
    Sum.inr (Sum.inl (57, 39)),
    Sum.inr (Sum.inl (61, 3)),
    Sum.inr (Sum.inl (131, 39)),
    Sum.inr (Sum.inl (89, 20)),
    Sum.inr (Sum.inl (185, 22)),
    Sum.inr (Sum.inl (113, 1)),
    Sum.inr (Sum.inl (221, 25)),
    Sum.inr (Sum.inl (193, 13)),
    Sum.inr (Sum.inl (57, 47)),
    Sum.inr (Sum.inl (61, 52)),
    Sum.inr (Sum.inl (131, 6)),
    Sum.inr (Sum.inl (61, 21)),
    Sum.inr (Sum.inl (131, 61)),
    Sum.inr (Sum.inl (193, 44)),
    Sum.inr (Sum.inl (57, 20)),
    Sum.inr (Sum.inl (113, 16)),
    Sum.inr (Sum.inl (221, 39)),
    Sum.inr (Sum.inl (89, 5)),
    Sum.inr (Sum.inl (185, 45)),
    Sum.inr (Sum.inl (61, 34)),
    Sum.inr (Sum.inl (131, 28)),
    Sum.inr (Sum.inl (193, 17)),
    Sum.inr (Sum.inl (57, 28)),
    Sum.inr (Sum.inl (113, 50)),
    Sum.inr (Sum.inl (221, 47)),
    Sum.inr (Sum.inl (89, 50)),
    Sum.inr (Sum.inl (185, 12)),
    Sum.inr (Sum.inl (113, 24)),
    Sum.inr (Sum.inl (221, 51)),
    Sum.inr (Sum.inl (89, 1)),
    Sum.inr (Sum.inl (185, 37)),
    Sum.inr (Sum.inl (61, 7)),
    Sum.inr (Sum.inl (131, 47)),
    Sum.inr (Sum.inl (193, 52)),
    Sum.inr (Sum.inl (57, 6)),
    Sum.inr (Sum.inl (113, 58)),
    Sum.inr (Sum.inl (221, 59)),
    Sum.inr (Sum.inl (89, 54)),
    Sum.inr (Sum.inl (185, 4)),
    Sum.inr (Sum.inl (61, 48)),
    Sum.inr (Sum.inl (131, 14)),
    Sum.inr (Sum.inl (193, 9)),
    Sum.inr (Sum.inl (57, 14)),
    Sum.inr (Sum.inl (129, 10)),
    Sum.inr (Sum.inl (163, 12)),
    Sum.inr (Sum.inl (129, 6)),
    Sum.inr (Sum.inl (163, 4)),
    Sum.inr (Sum.inl (163, 30)),
    Sum.inr (Sum.inl (129, 37)),
    Sum.inr (Sum.inl (163, 22)),
    Sum.inr (Sum.inl (129, 41)),
    Sum.inr (Sum.inl (116, 10)),
    Sum.inr (Sum.inl (202, 8)),
    Sum.inr (Sum.inl (116, 8)),
    Sum.inr (Sum.inl (202, 4)),
    Sum.inr (Sum.inl (202, 26)),
    Sum.inr (Sum.inl (116, 37)),
    Sum.inr (Sum.inl (202, 22)),
    Sum.inr (Sum.inl (116, 39)),
    Sum.inr (Sum.inl (56, 3)),
    Sum.inr (Sum.inl (60, 10)),
    Sum.inr (Sum.inl (56, 17)),
    Sum.inr (Sum.inl (60, 6)),
    Sum.inr (Sum.inl (60, 27)),
    Sum.inr (Sum.inl (56, 11)),
    Sum.inr (Sum.inl (60, 23)),
    Sum.inr (Sum.inl (56, 25)),
    Sum.inr (Sum.inl (105, 18)),
    Sum.inr (Sum.inl (222, 34)),
    Sum.inr (Sum.inl (105, 17)),
    Sum.inr (Sum.inl (222, 32)),
    Sum.inr (Sum.inl (222, 39)),
    Sum.inr (Sum.inl (105, 50)),
    Sum.inr (Sum.inl (222, 37)),
    Sum.inr (Sum.inl (105, 49)),
    Sum.inr (Sum.inl (116, 6)),
    Sum.inr (Sum.inl (202, 40)),
    Sum.inr (Sum.inl (116, 4)),
    Sum.inr (Sum.inl (202, 36)),
    Sum.inr (Sum.inl (202, 58)),
    Sum.inr (Sum.inl (116, 41)),
    Sum.inr (Sum.inl (202, 54)),
    Sum.inr (Sum.inl (116, 43)),
    Sum.inr (Sum.inl (129, 8)),
    Sum.inr (Sum.inl (163, 55)),
    Sum.inr (Sum.inl (129, 4)),
    Sum.inr (Sum.inl (163, 63)),
    Sum.inr (Sum.inl (163, 37)),
    Sum.inr (Sum.inl (129, 39)),
    Sum.inr (Sum.inl (163, 45)),
    Sum.inr (Sum.inl (129, 43)),
    Sum.inr (Sum.inl (105, 6)),
    Sum.inr (Sum.inl (222, 10)),
    Sum.inr (Sum.inl (105, 5)),
    Sum.inr (Sum.inl (222, 8)),
    Sum.inr (Sum.inl (222, 15)),
    Sum.inr (Sum.inl (105, 38)),
    Sum.inr (Sum.inl (222, 13)),
    Sum.inr (Sum.inl (105, 37)),
    Sum.inr (Sum.inl (56, 34)),
    Sum.inr (Sum.inl (60, 8)),
    Sum.inr (Sum.inl (56, 48)),
    Sum.inr (Sum.inl (60, 4)),
    Sum.inr (Sum.inl (60, 25)),
    Sum.inr (Sum.inl (56, 42)),
    Sum.inr (Sum.inl (60, 21)),
    Sum.inr (Sum.inl (56, 56)),
    Sum.inr (Sum.inl (191, 2)),
    Sum.inr (Sum.inl (134, 59)),
    Sum.inr (Sum.inl (44, 24)),
    Sum.inr (Sum.inl (100, 12)),
    Sum.inr (Sum.inl (77, 16)),
    Sum.inr (Sum.inl (162, 59)),
    Sum.inr (Sum.inl (86, 40)),
    Sum.inr (Sum.inl (223, 47)),
    Sum.inr (Sum.inl (191, 19)),
    Sum.inr (Sum.inl (134, 49)),
    Sum.inr (Sum.inl (44, 30)),
    Sum.inr (Sum.inl (100, 28)),
    Sum.inr (Sum.inl (77, 26)),
    Sum.inr (Sum.inl (162, 43)),
    Sum.inr (Sum.inl (86, 56)),
    Sum.inr (Sum.inl (223, 39)),
    Sum.inr (Sum.inl (134, 62)),
    Sum.inr (Sum.inl (191, 63)),
    Sum.inr (Sum.inl (100, 9)),
    Sum.inr (Sum.inl (44, 55)),
    Sum.inr (Sum.inl (162, 62)),
    Sum.inr (Sum.inl (77, 63)),
    Sum.inr (Sum.inl (223, 62)),
    Sum.inr (Sum.inl (86, 55))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock057Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨14592 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock057InputMaskData : ℕ :=
  sixthHex% [
    "70080171e80111e80110000121e80120000140000141e00140e801410801",
    "21080120e00111080110e00170e00171000131080130e00150e001510001",
    "60e00161000101000100e80155fe823c4e8268be820106826eae82071682",
    "53e6823a56826dae8204168250e68239568256f6823f46826bb682020e82",
    "6fae8206168252e6823b568254f6823d468269b682000e8257f6823e4682",
    "6ab682030e826ca682051e8251ee82385e822c9e8245268211d682786682",
    "17c6827e76822a8682433e8214c6827d7682298682403e822f9682462e82",
    "12de827b6e8216c6827f76822b8682423e822d9682442e8210de82796e82",
    "2e9682472e8213de827a6e8215ce827c7e82288e824136827698091b0809",
    "5908093490095a08093790097590091800095808093590097790091a0009",
    "7490091900095b00093698091b98097600093400095990093700095a9009",
    "1890097508093500095890091a90097708091990097408093608095b9809",
    "6d98090000094200092f90094100092c90096e90090308094300092e9009",
    "6c90090108096f90090208094008092d98090090096d00092f0009429809",
    "2c00094198090398096e08092e00094398090198096c08090298096f0809",
    "2d080940900968a2cf45d2cf15d2cf38aacf0522cf285acf785acf552acf",
    "4922cf645acf345acf192acf24aacf09dacf59dacf74a2cf5002cf7d7acf",
    "2d7acf000acf3d8acf10facf40facf6d82cf718acf5cfacf0cfacf2182cf",
    "1c0acf3172cf6172cf4c02cf7a02cf577acf077acf2a0acf178acf3afacf",
    "6afacf4782cf5b8acf76facf26facf0b82cf360acf1b72cf4b72cf6602cf",
    "42aacf6fdacf3fdacf12a2cf2f2acf0252cf5252cf7f22cf632acf4e52cf",
    "1e52cf3322cf0ea2cf23d2cf73d2cf5eaacf143c2f4d8c2f7d8c2f24342f",
    "5d8c2f04342f34342f6d842f6d7c2f34c42f04c42f5d742f24c42f7d742f",
    "4d742f14cc2f2c6c2f75d42f45d42f1c642f65d42f3c642f0c642f55dc2f",
    "55242f0c942f3c942f652c2f1c942f452c2f752c2f2c9c2f385c2f61e42f",
    "51e42f08542f71e42f28542f18542f41ec2f"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock057InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock057InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock057OutputMaskData : ℕ :=
  sixthHex% [
    "217b2a03000172493021721b54da1007e13b76a80a54d32132080110732a",
    "613a1b32013047a93b14921065db2147a00a43e00110db2a61921b43e930",
    "47013b657a1014332147080a2f67b85e81e71227b81281e70c69e70ccfb8",
    "4069e7318fb82b20dd2b86826720dd16c682796e820888dd442e824488dd",
    "1bf2c71b549857f2c726149849bc98385ac774fc98745ac76ef5a21f13fd",
    "53b5a25313fd4dfbfd4d5da201fbfd701da26a10dd6ab6822610dd57f682",
    "385e8249b8dd051e8205b8dd1f17b86ef1e72257b822f1e73c19e73cbfb8",
    "7019e701ffb82fc5a25e23fd1285a21223fd0ccbfd0c6da240cbfd312da2",
    "2b82c72b24986782c716649879cc98082ac7448c98442ac70c013370d002",
    "350213389322124b291fda185a080926d9382299332f08026ada13160b22",
    "4d932931421874900979013853db295e4a181b98096749383cd133400002",
    "05d2130843220c032970d2183500093891381249331fd8025a0a1326db22",
    "019a130c0b2249d9333508026e90091241385793295a02185e4213229322",
    "6741336ad0024008094d9938084b29749a182f000953d1381603291b9218",
    "314a133cdb2279093305d8020198090c093849db29350a186e9213124322",
    "5791335a0002203c901c0da14bd7b006a6814371ef0e00de59dacf65ebfe",
    "0f79ef4208de15d2cf29e3fe1d74902145a1769fb03bee810e07b0437681",
    "14ac90289da11c0acf203bfe77e1ef3a90de5002cf6c33fe3be9ef7698de",
    "334fb07e3e8129e49015d5a13294907fe5a1283fb0140e812099ef1ca8de",
    "4b72cf0603fe6c91ef50a0de077acf4a0bfe0fdc9042ada11577b0294681",
    "6defb051de810604904b75a10ea2cf43d3fe1409ef2838de42aacf0fdbfe",
    "5801ef6430de50a7b06c96813b4c90763da11c45154b306a6da34a4b9635",
    "69ea704fdf0f694c2f3e395065051543306a65a34a32d63561ea70369f0f",
    "100c2f3639501802703e370f18a42f4fd1501ced154b986a6d0b4a4b3e35",
    "10027047770f61e42f47d15065ad1543986a650b4a327e3528734a0e4635",
    "28d5157fa06a2c9c2f7be9505d7a707b4f0f"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock057OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock057OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock057InputNumeratorData : ℕ :=
  sixthHex% [
    "85f8618617e185f8618617e17df85f85f8617e17df8617e18617e185f861",
    "7df85f7e17df7e17df8617e17df85f7e17df7e17df8617e185f8617df85f",
    "7df85f7e17df85f8618617e17df85f85f8618617e17e17df85f8618617e1",
    "8617e17e17df85f8618617e17e17df7df85f8617e17e17df7e18617df7e1",
    "86185f7e18617df7e185f7df7e18617df7e17df7e185f7df7e18617df7e1",
    "85f7df86185f7df7e185f7df7df7e185f7df85f7df86185f7e18617df7e1",
    "7df7e185f7df85f7df86185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock057InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock057InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock057OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7e185f7df7df7e185f7df7e18617df7e17e17df7df85f8617e17e17df",
    "7df85f85f8617e17df7df85f7df85f85f8617e17df7df85f85f8618617e1",
    "7df85f85f8617e17df7df85f7df85f85f8617df85f85f86185f8618617e1",
    "8617e17e17df7e17df7df85f7e17df7df85f7df85f85f8618617e185f861",
    "85f8617df85f85f8617df85f7df85f7e17df7e17df8617e18617e185f861",
    "8617e185f86185f8617df85f7df85f85f86185f8618617e185f8618617e1",
    "8617e17e17df7e17df7df85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock057OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock057OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block057_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock057Input a) =
      generatedSixthXiShortBlock057InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock057Output a) =
      generatedSixthXiShortBlock057OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock057Input a) =
      generatedSixthXiShortBlock057InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock057Output a) =
      generatedSixthXiShortBlock057OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block057_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock057InputMask a) =
      generatedSixthXiShortBlock057OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock057InputMask a)) *
      generatedSixthXiShortBlock057InputNumerator a =
        generatedSixthXiShortBlock057OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block057_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock057Input a
    let y := generatedSixthXiShortBlock057Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block057_cache a
  have hs := generatedSixth_xi_short_block057_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block057_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock057Input a
    let y := generatedSixthXiShortBlock057Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block057_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block057_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock057Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block057_certificate a).1
    (generatedSixth_xi_short_block057_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
