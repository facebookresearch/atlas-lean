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
def generatedSixthXiShortBlock060Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (235, 8)),
    Sum.inr (Sum.inr (170, 11)),
    Sum.inr (Sum.inr (106, 9)),
    Sum.inr (Sum.inr (32, 10)),
    Sum.inr (Sum.inr (501, 4)),
    Sum.inr (Sum.inr (510, 5)),
    Sum.inr (Sum.inr (501, 6)),
    Sum.inr (Sum.inr (501, 7)),
    Sum.inr (Sum.inr (235, 0)),
    Sum.inr (Sum.inr (106, 2)),
    Sum.inr (Sum.inr (32, 3)),
    Sum.inr (Sum.inr (170, 1)),
    Sum.inr (Sum.inr (32, 20)),
    Sum.inr (Sum.inr (235, 23)),
    Sum.inr (Sum.inr (106, 21)),
    Sum.inr (Sum.inr (170, 22)),
    Sum.inr (Sum.inr (510, 16)),
    Sum.inr (Sum.inr (510, 17)),
    Sum.inr (Sum.inr (501, 18)),
    Sum.inr (Sum.inr (510, 19)),
    Sum.inr (Sum.inr (32, 12)),
    Sum.inr (Sum.inr (106, 14)),
    Sum.inr (Sum.inr (170, 15)),
    Sum.inr (Sum.inr (235, 13)),
    Sum.inr (Sum.inr (232, 13)),
    Sum.inr (Sum.inr (169, 15)),
    Sum.inr (Sum.inr (105, 14)),
    Sum.inr (Sum.inr (35, 12)),
    Sum.inr (Sum.inr (502, 4)),
    Sum.inr (Sum.inr (509, 5)),
    Sum.inr (Sum.inr (502, 6)),
    Sum.inr (Sum.inr (502, 7)),
    Sum.inr (Sum.inr (232, 23)),
    Sum.inr (Sum.inr (105, 21)),
    Sum.inr (Sum.inr (35, 20)),
    Sum.inr (Sum.inr (169, 22)),
    Sum.inr (Sum.inr (35, 3)),
    Sum.inr (Sum.inr (232, 0)),
    Sum.inr (Sum.inr (105, 2)),
    Sum.inr (Sum.inr (169, 1)),
    Sum.inr (Sum.inr (509, 16)),
    Sum.inr (Sum.inr (509, 17)),
    Sum.inr (Sum.inr (502, 18)),
    Sum.inr (Sum.inr (509, 19)),
    Sum.inr (Sum.inr (35, 10)),
    Sum.inr (Sum.inr (105, 9)),
    Sum.inr (Sum.inr (169, 11)),
    Sum.inr (Sum.inr (232, 8)),
    Sum.inr (Sum.inr (233, 23)),
    Sum.inr (Sum.inr (168, 22)),
    Sum.inr (Sum.inr (104, 21)),
    Sum.inr (Sum.inr (34, 20)),
    Sum.inr (Sum.inr (503, 4)),
    Sum.inr (Sum.inr (508, 5)),
    Sum.inr (Sum.inr (503, 6)),
    Sum.inr (Sum.inr (503, 7)),
    Sum.inr (Sum.inr (233, 13)),
    Sum.inr (Sum.inr (104, 14)),
    Sum.inr (Sum.inr (34, 12)),
    Sum.inr (Sum.inr (168, 15)),
    Sum.inr (Sum.inr (34, 10)),
    Sum.inr (Sum.inr (233, 8)),
    Sum.inr (Sum.inr (104, 9)),
    Sum.inr (Sum.inr (168, 11)),
    Sum.inr (Sum.inr (508, 16)),
    Sum.inr (Sum.inr (508, 17)),
    Sum.inr (Sum.inr (503, 18)),
    Sum.inr (Sum.inr (508, 19)),
    Sum.inr (Sum.inr (34, 3)),
    Sum.inr (Sum.inr (104, 2)),
    Sum.inr (Sum.inr (168, 1)),
    Sum.inr (Sum.inr (233, 0)),
    Sum.inr (Sum.inl (214, 36)),
    Sum.inr (Sum.inl (208, 59)),
    Sum.inr (Sum.inl (151, 20)),
    Sum.inr (Sum.inl (174, 0)),
    Sum.inr (Sum.inl (39, 8)),
    Sum.inr (Sum.inl (19, 7)),
    Sum.inr (Sum.inl (39, 24)),
    Sum.inr (Sum.inl (39, 39)),
    Sum.inr (Sum.inl (214, 59)),
    Sum.inr (Sum.inl (151, 11)),
    Sum.inr (Sum.inl (174, 31)),
    Sum.inr (Sum.inl (208, 36)),
    Sum.inr (Sum.inl (174, 47)),
    Sum.inr (Sum.inl (214, 11)),
    Sum.inr (Sum.inl (151, 59)),
    Sum.inr (Sum.inl (208, 20)),
    Sum.inr (Sum.inl (19, 24)),
    Sum.inr (Sum.inl (19, 40)),
    Sum.inr (Sum.inl (39, 55)),
    Sum.inr (Sum.inl (19, 55)),
    Sum.inr (Sum.inl (174, 48)),
    Sum.inr (Sum.inl (151, 36)),
    Sum.inr (Sum.inl (208, 11)),
    Sum.inr (Sum.inl (214, 20)),
    Sum.inr (Sum.inl (211, 59)),
    Sum.inr (Sum.inl (205, 40)),
    Sum.inr (Sum.inl (148, 31)),
    Sum.inr (Sum.inl (171, 22)),
    Sum.inr (Sum.inl (36, 36)),
    Sum.inr (Sum.inl (16, 13)),
    Sum.inr (Sum.inl (36, 33)),
    Sum.inr (Sum.inl (36, 45)),
    Sum.inr (Sum.inl (211, 36)),
    Sum.inr (Sum.inl (148, 0)),
    Sum.inr (Sum.inl (171, 9)),
    Sum.inr (Sum.inl (205, 55)),
    Sum.inr (Sum.inl (171, 55)),
    Sum.inr (Sum.inl (211, 26)),
    Sum.inr (Sum.inl (148, 62)),
    Sum.inr (Sum.inl (205, 9)),
    Sum.inr (Sum.inl (16, 18)),
    Sum.inr (Sum.inl (16, 34)),
    Sum.inr (Sum.inl (36, 40)),
    Sum.inr (Sum.inl (16, 61)),
    Sum.inr (Sum.inl (171, 40)),
    Sum.inr (Sum.inl (148, 33)),
    Sum.inr (Sum.inl (205, 22)),
    Sum.inr (Sum.inl (211, 5)),
    Sum.inr (Sum.inl (188, 59)),
    Sum.inr (Sum.inl (187, 20)),
    Sum.inr (Sum.inl (143, 47)),
    Sum.inr (Sum.inl (166, 50)),
    Sum.inr (Sum.inl (31, 36)),
    Sum.inr (Sum.inl (11, 13)),
    Sum.inr (Sum.inl (31, 33)),
    Sum.inr (Sum.inl (31, 45)),
    Sum.inr (Sum.inl (188, 62)),
    Sum.inr (Sum.inl (143, 42)),
    Sum.inr (Sum.inl (166, 55)),
    Sum.inr (Sum.inl (187, 17)),
    Sum.inr (Sum.inl (166, 9)),
    Sum.inr (Sum.inl (188, 0)),
    Sum.inr (Sum.inl (143, 20)),
    Sum.inr (Sum.inl (187, 47)),
    Sum.inr (Sum.inl (11, 18)),
    Sum.inr (Sum.inl (11, 34)),
    Sum.inr (Sum.inl (31, 40)),
    Sum.inr (Sum.inl (11, 61)),
    Sum.inr (Sum.inl (166, 12)),
    Sum.inr (Sum.inl (143, 17)),
    Sum.inr (Sum.inl (187, 42)),
    Sum.inr (Sum.inl (188, 5)),
    Sum.inr (Sum.inl (212, 41)),
    Sum.inr (Sum.inl (206, 30)),
    Sum.inr (Sum.inl (149, 26)),
    Sum.inr (Sum.inl (172, 31)),
    Sum.inr (Sum.inl (37, 11)),
    Sum.inr (Sum.inl (17, 4)),
    Sum.inr (Sum.inl (37, 14)),
    Sum.inr (Sum.inl (37, 2)),
    Sum.inr (Sum.inl (212, 44)),
    Sum.inr (Sum.inl (149, 31)),
    Sum.inr (Sum.inl (172, 26)),
    Sum.inr (Sum.inl (206, 27)),
    Sum.inr (Sum.inl (172, 22)),
    Sum.inr (Sum.inl (212, 32)),
    Sum.inr (Sum.inl (149, 19)),
    Sum.inr (Sum.inl (206, 23)),
    Sum.inr (Sum.inl (17, 14)),
    Sum.inr (Sum.inl (17, 13)),
    Sum.inr (Sum.inl (37, 7)),
    Sum.inr (Sum.inl (17, 7)),
    Sum.inr (Sum.inl (172, 19)),
    Sum.inr (Sum.inl (149, 22)),
    Sum.inr (Sum.inl (206, 18)),
    Sum.inr (Sum.inl (212, 37)),
    Sum.inr (Sum.inr (226, 23)),
    Sum.inr (Sum.inr (163, 22)),
    Sum.inr (Sum.inr (99, 21)),
    Sum.inr (Sum.inr (41, 20)),
    Sum.inr (Sum.inr (508, 4)),
    Sum.inr (Sum.inr (503, 5)),
    Sum.inr (Sum.inr (508, 6)),
    Sum.inr (Sum.inr (508, 7)),
    Sum.inr (Sum.inr (226, 13)),
    Sum.inr (Sum.inr (99, 14)),
    Sum.inr (Sum.inr (41, 12)),
    Sum.inr (Sum.inr (163, 15)),
    Sum.inr (Sum.inr (41, 10)),
    Sum.inr (Sum.inr (226, 8)),
    Sum.inr (Sum.inr (99, 9)),
    Sum.inr (Sum.inr (163, 11)),
    Sum.inr (Sum.inr (503, 16)),
    Sum.inr (Sum.inr (503, 17)),
    Sum.inr (Sum.inr (508, 18)),
    Sum.inr (Sum.inr (503, 19)),
    Sum.inr (Sum.inr (41, 3)),
    Sum.inr (Sum.inr (99, 2)),
    Sum.inr (Sum.inr (163, 1)),
    Sum.inr (Sum.inr (226, 0)),
    Sum.inr (Sum.inr (227, 13)),
    Sum.inr (Sum.inr (162, 15)),
    Sum.inr (Sum.inr (98, 14)),
    Sum.inr (Sum.inr (40, 12)),
    Sum.inr (Sum.inr (509, 4)),
    Sum.inr (Sum.inr (502, 5)),
    Sum.inr (Sum.inr (509, 6)),
    Sum.inr (Sum.inr (509, 7)),
    Sum.inr (Sum.inr (227, 23)),
    Sum.inr (Sum.inr (98, 21)),
    Sum.inr (Sum.inr (40, 20)),
    Sum.inr (Sum.inr (162, 22)),
    Sum.inr (Sum.inr (40, 3)),
    Sum.inr (Sum.inr (227, 0)),
    Sum.inr (Sum.inr (98, 2)),
    Sum.inr (Sum.inr (162, 1)),
    Sum.inr (Sum.inr (502, 16)),
    Sum.inr (Sum.inr (502, 17)),
    Sum.inr (Sum.inr (509, 18)),
    Sum.inr (Sum.inr (502, 19)),
    Sum.inr (Sum.inr (40, 10)),
    Sum.inr (Sum.inr (98, 9)),
    Sum.inr (Sum.inr (162, 11)),
    Sum.inr (Sum.inr (227, 8)),
    Sum.inr (Sum.inr (224, 8)),
    Sum.inr (Sum.inr (161, 11)),
    Sum.inr (Sum.inr (97, 9)),
    Sum.inr (Sum.inr (43, 10)),
    Sum.inr (Sum.inr (510, 4)),
    Sum.inr (Sum.inr (501, 5)),
    Sum.inr (Sum.inr (510, 6)),
    Sum.inr (Sum.inr (510, 7)),
    Sum.inr (Sum.inr (224, 0)),
    Sum.inr (Sum.inr (97, 2)),
    Sum.inr (Sum.inr (43, 3)),
    Sum.inr (Sum.inr (161, 1)),
    Sum.inr (Sum.inr (43, 20)),
    Sum.inr (Sum.inr (224, 23)),
    Sum.inr (Sum.inr (97, 21)),
    Sum.inr (Sum.inr (161, 22)),
    Sum.inr (Sum.inr (501, 16)),
    Sum.inr (Sum.inr (501, 17)),
    Sum.inr (Sum.inr (510, 18)),
    Sum.inr (Sum.inr (501, 19)),
    Sum.inr (Sum.inr (43, 12)),
    Sum.inr (Sum.inr (97, 14)),
    Sum.inr (Sum.inr (161, 15)),
    Sum.inr (Sum.inr (224, 13)),
    Sum.inr (Sum.inr (234, 0)),
    Sum.inr (Sum.inr (171, 1)),
    Sum.inr (Sum.inr (107, 2)),
    Sum.inr (Sum.inr (33, 3)),
    Sum.inr (Sum.inr (500, 4)),
    Sum.inr (Sum.inr (511, 5)),
    Sum.inr (Sum.inr (500, 6)),
    Sum.inr (Sum.inr (500, 7)),
    Sum.inr (Sum.inr (234, 8)),
    Sum.inr (Sum.inr (107, 9)),
    Sum.inr (Sum.inr (33, 10)),
    Sum.inr (Sum.inr (171, 11)),
    Sum.inr (Sum.inr (33, 12)),
    Sum.inr (Sum.inr (234, 13)),
    Sum.inr (Sum.inr (107, 14)),
    Sum.inr (Sum.inr (171, 15))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock060Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨15360 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock060InputMaskData : ℕ :=
  sixthHex% [
    "ff900bd5900bea900b80900bc3a00bc1a00bc2a00b80a00bccb80bc4b80b",
    "c8b80b80b80bb0400b90400ba0400bc0400bdbd80aedd80af6d80a80d80a",
    "e7100af9100ade100a80100aff780ad5780aea780a80780ac3400ac1400a",
    "c2400a80400acc500ac4500ac8500a80500ab0a00a90a00aa0a00ac0a00a",
    "dbe809ede809f6e80980e809e72009f92009de2009802009ff4009d54009",
    "ea4009804009c37809c17809c27809807809cc6009c46009c86009806009",
    "b09009909009a09009c090099b0008ad0008b60008c00008a7c808b9c808",
    "9ec808c0c808bfa80895a808aaa808c0a808839808819808829808c09808",
    "8c8808848808888808c08808f07008d07008e07008807008dbf807edf807",
    "f6f80780f807e73007f93007de3007803007ff5007d55007ea5007805007",
    "c36007c16007c26007806007cc7807c47807c87807807807b08007908007",
    "a08007c08007db1006ed1006f61006801006e7d806f9d806ded80680d806",
    "ffb806d5b806eab80680b806c38006c18006c28006808006cc9006c49006",
    "c89006809006b06006906006a06006c06006db2005ed2005f62005802005",
    "e7e805f9e805dee80580e805ff8005d58005ea8005808005c3b805c1b805",
    "c2b80580b805cca005c4a005c8a00580a005b05005905005a05005c05005",
    "9bc804adc804b6c804c0c804a70004b900049e0004c00004bf6804956804",
    "aa6804c06804835804815804825804c058048c4804844804884804c04804",
    "f0b004d0b004e0b00480b004db4003ed4003f64003804003e78003f98003",
    "de8003808003ffe803d5e803eae80380e803c3d803c1d803c2d80380d803",
    "ccc003c4c003c8c00380c003b03003903003a03003c030039ba802ada802",
    "b6a802c0a802a76802b968029e6802c06802bf0002950002aa0002c00002",
    "833802813802823802c038028c2802842802882802c02802f0d002d0d002",
    "e0d00280d0029b9801ad9801b69801c09801a75801b958019e5801c05801",
    "bf3801953801aa3801c03801830001810001820001c000018c1801841801",
    "881801c01801f0e001d0e001e0e00180e001"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock060InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock060InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock060OutputMaskData : ℕ :=
  sixthHex% [
    "ae52ab92c18baa139ae380b19262aba2b0b185f98bc02b9ae2ffd4eaf7d4",
    "d3ffdfaef7d4d358b1d7118bf182ab80cb9adcb390fbf2a1f66981a428bb",
    "bbbfd590bfde82bfd5dcbfd5e95aa1d5c981ed1b90a488bba42aa194f8bb",
    "b3b181f66390a5f7deadffde94f7d5e9ffdee510bbe15981c7caa1b68390",
    "f4b393d3f2a2de69828c28b893bfd6b8bfddaabfd6f4bfd6b01aa28c8982",
    "b45b93fdc8b8fd6aa2cdb8b8eaf182af23938df7dd85ffddbcf7d6c1ffdd",
    "cd10b8c95982efcaa29e8393c6bb92e1faa3ec6183be20b9a1b7d78ab7dc",
    "98b7d7c6b7d78212a3be8183865392cfc0b9be22a38ef0b9a9b983ec6b92",
    "bfffdcb7f7dc8effd7f3f7dc8e58b98a1183ac82a3ddcb926d0c494a4d78",
    "47d6581597620a000c21000733000c6d000c29a5781536582de449647762",
    "159578254762020e5847dc496508076d000754080c29000754af6250e658",
    "767578073c492a04430d457200de52529f684d080666080d7408062a0806",
    "6ead72523e526aec43237f6823dd72130f6834465271944322000d2a080d",
    "1300066e080d62e76866ae52403d7231744302044025457128de517a9f6b",
    "6508054e080e5c080502080537ed710b7e5133ac407a3f6b7a9d714a4f6b",
    "6d065128d4400a000e02080e3b000546080e4ae76b4eae51683d71197440",
    "300c41174d701ad65048976a5700047c000f6e000430000405e570397650",
    "01a44148376a39d57009076a2e4e506b9c4138080f30000f09080474000f",
    "09af6a0de6502b75705a3c4182f399a5b2a8a82988fa68b294bfdcbfbfd7",
    "adbfdcf3bfdcc65aa8fac988c21b998b88b2fa6aa8cab8b2edf188a82399",
    "8af7d782ffd7bbf7dcc6ffd7ca10b2ce5988e8caa8998399b0fb9897baa9",
    "9a2189c860b3a6b7dd8db7d69fb7ddc1b7ddf452a9c8c189f01398b980b3",
    "b922a989f0b3aeb989eb6b98b8ffd6b0f7d689ffddf4f7d68958b38d1189",
    "ab82a9dacb9898fb9bbfbaaab2218ae060b08eb7dea5b7d5b7b7dee9b7de",
    "ad12aa91818aa9539be0c0b0e062aad0b0b0f7f98ab22b9b90ffd598f7d5",
    "a1ffdedcf7d5a158b0a5118a8382aaf2cb9b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock060OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock060OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock060InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock060InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock060InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock060OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e18617df96175d7df8617df7df85f7e17e17e1",
    "86186196175d85f7e185f7e185f7e185f7e17df8616df8e37df861861861",
    "7e185f7e17e17e18616e18e37df7e18617e186185f7df85f7e17df6e18e3",
    "7e17df7e17df86185f7df7e17e18616e18e386185f8617e186185f8617e1",
    "85f86195f75d7e17df85f8617df7e17df7e17df8616df8e37df861861861",
    "7e185f7e17e186186196175d85f7e185f7e185f7e185f7e18617df96175d",
    "7df8617df7df85f7e17e17e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock060OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock060OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block060_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock060Input a) =
      generatedSixthXiShortBlock060InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock060Output a) =
      generatedSixthXiShortBlock060OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock060Input a) =
      generatedSixthXiShortBlock060InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock060Output a) =
      generatedSixthXiShortBlock060OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block060_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock060InputMask a) =
      generatedSixthXiShortBlock060OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock060InputMask a)) *
      generatedSixthXiShortBlock060InputNumerator a =
        generatedSixthXiShortBlock060OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block060_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock060Input a
    let y := generatedSixthXiShortBlock060Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block060_cache a
  have hs := generatedSixth_xi_short_block060_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block060_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock060Input a
    let y := generatedSixthXiShortBlock060Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block060_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block060_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock060Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block060_certificate a).1
    (generatedSixth_xi_short_block060_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
