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
def generatedSixthXiShortBlock067Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (436, 16)),
    Sum.inr (Sum.inr (436, 17)),
    Sum.inr (Sum.inr (447, 18)),
    Sum.inr (Sum.inr (436, 19)),
    Sum.inr (Sum.inr (106, 12)),
    Sum.inr (Sum.inr (32, 14)),
    Sum.inr (Sum.inr (224, 15)),
    Sum.inr (Sum.inr (161, 13)),
    Sum.inr (Sum.inl (188, 35)),
    Sum.inr (Sum.inl (187, 60)),
    Sum.inr (Sum.inl (143, 29)),
    Sum.inr (Sum.inl (166, 24)),
    Sum.inr (Sum.inl (31, 52)),
    Sum.inr (Sum.inl (11, 8)),
    Sum.inr (Sum.inl (31, 49)),
    Sum.inr (Sum.inl (31, 61)),
    Sum.inr (Sum.inl (188, 38)),
    Sum.inr (Sum.inl (143, 24)),
    Sum.inr (Sum.inl (166, 29)),
    Sum.inr (Sum.inl (187, 57)),
    Sum.inr (Sum.inl (166, 35)),
    Sum.inr (Sum.inl (188, 24)),
    Sum.inr (Sum.inl (143, 38)),
    Sum.inr (Sum.inl (187, 7)),
    Sum.inr (Sum.inl (11, 23)),
    Sum.inr (Sum.inl (11, 39)),
    Sum.inr (Sum.inl (31, 56)),
    Sum.inr (Sum.inl (11, 56)),
    Sum.inr (Sum.inl (166, 38)),
    Sum.inr (Sum.inl (143, 35)),
    Sum.inr (Sum.inl (187, 2)),
    Sum.inr (Sum.inl (188, 29)),
    Sum.inr (Sum.inl (212, 9)),
    Sum.inr (Sum.inl (206, 62)),
    Sum.inr (Sum.inl (149, 55)),
    Sum.inr (Sum.inl (172, 50)),
    Sum.inr (Sum.inl (37, 59)),
    Sum.inr (Sum.inl (17, 52)),
    Sum.inr (Sum.inl (37, 62)),
    Sum.inr (Sum.inl (37, 50)),
    Sum.inr (Sum.inl (212, 12)),
    Sum.inr (Sum.inl (149, 50)),
    Sum.inr (Sum.inl (172, 55)),
    Sum.inr (Sum.inl (206, 59)),
    Sum.inr (Sum.inl (172, 59)),
    Sum.inr (Sum.inl (212, 0)),
    Sum.inr (Sum.inl (149, 62)),
    Sum.inr (Sum.inl (206, 55)),
    Sum.inr (Sum.inl (17, 62)),
    Sum.inr (Sum.inl (17, 61)),
    Sum.inr (Sum.inl (37, 55)),
    Sum.inr (Sum.inl (17, 55)),
    Sum.inr (Sum.inl (172, 62)),
    Sum.inr (Sum.inl (149, 59)),
    Sum.inr (Sum.inl (206, 50)),
    Sum.inr (Sum.inl (212, 5)),
    Sum.inr (Sum.inl (214, 34)),
    Sum.inr (Sum.inl (208, 61)),
    Sum.inr (Sum.inl (151, 31)),
    Sum.inr (Sum.inl (174, 11)),
    Sum.inr (Sum.inl (39, 4)),
    Sum.inr (Sum.inl (19, 11)),
    Sum.inr (Sum.inl (39, 20)),
    Sum.inr (Sum.inl (39, 43)),
    Sum.inr (Sum.inl (214, 61)),
    Sum.inr (Sum.inl (151, 0)),
    Sum.inr (Sum.inl (174, 20)),
    Sum.inr (Sum.inl (208, 34)),
    Sum.inr (Sum.inl (174, 36)),
    Sum.inr (Sum.inl (214, 13)),
    Sum.inr (Sum.inl (151, 48)),
    Sum.inr (Sum.inl (208, 18)),
    Sum.inr (Sum.inl (19, 20)),
    Sum.inr (Sum.inl (19, 36)),
    Sum.inr (Sum.inl (39, 59)),
    Sum.inr (Sum.inl (19, 59)),
    Sum.inr (Sum.inl (174, 59)),
    Sum.inr (Sum.inl (151, 47)),
    Sum.inr (Sum.inl (208, 13)),
    Sum.inr (Sum.inl (214, 18)),
    Sum.inr (Sum.inl (211, 55)),
    Sum.inr (Sum.inl (205, 48)),
    Sum.inr (Sum.inl (148, 9)),
    Sum.inr (Sum.inl (171, 0)),
    Sum.inr (Sum.inl (36, 4)),
    Sum.inr (Sum.inl (16, 11)),
    Sum.inr (Sum.inl (36, 1)),
    Sum.inr (Sum.inl (36, 13)),
    Sum.inr (Sum.inl (211, 40)),
    Sum.inr (Sum.inl (148, 22)),
    Sum.inr (Sum.inl (171, 31)),
    Sum.inr (Sum.inl (205, 47)),
    Sum.inr (Sum.inl (171, 33)),
    Sum.inr (Sum.inl (211, 22)),
    Sum.inr (Sum.inl (148, 40)),
    Sum.inr (Sum.inl (205, 17)),
    Sum.inr (Sum.inl (16, 20)),
    Sum.inr (Sum.inl (16, 36)),
    Sum.inr (Sum.inl (36, 8)),
    Sum.inr (Sum.inl (16, 59)),
    Sum.inr (Sum.inl (171, 62)),
    Sum.inr (Sum.inl (148, 55)),
    Sum.inr (Sum.inl (205, 14)),
    Sum.inr (Sum.inl (211, 9)),
    Sum.inr (Sum.inr (420, 0)),
    Sum.inr (Sum.inr (485, 22)),
    Sum.inr (Sum.inr (293, 14)),
    Sum.inr (Sum.inr (367, 10)),
    Sum.inr (Sum.inr (186, 18)),
    Sum.inr (Sum.inr (177, 5)),
    Sum.inr (Sum.inr (186, 7)),
    Sum.inr (Sum.inr (186, 6)),
    Sum.inr (Sum.inr (420, 8)),
    Sum.inr (Sum.inr (293, 21)),
    Sum.inr (Sum.inr (367, 3)),
    Sum.inr (Sum.inr (485, 15)),
    Sum.inr (Sum.inr (367, 20)),
    Sum.inr (Sum.inr (420, 13)),
    Sum.inr (Sum.inr (293, 2)),
    Sum.inr (Sum.inr (485, 11)),
    Sum.inr (Sum.inr (177, 16)),
    Sum.inr (Sum.inr (177, 17)),
    Sum.inr (Sum.inr (186, 4)),
    Sum.inr (Sum.inr (177, 19)),
    Sum.inr (Sum.inr (367, 12)),
    Sum.inr (Sum.inr (293, 9)),
    Sum.inr (Sum.inr (485, 1)),
    Sum.inr (Sum.inr (420, 23)),
    Sum.inr (Sum.inr (366, 8)),
    Sum.inr (Sum.inr (303, 15)),
    Sum.inr (Sum.inr (495, 21)),
    Sum.inr (Sum.inr (421, 3)),
    Sum.inr (Sum.inr (112, 18)),
    Sum.inr (Sum.inr (123, 5)),
    Sum.inr (Sum.inr (112, 7)),
    Sum.inr (Sum.inr (112, 6)),
    Sum.inr (Sum.inr (366, 0)),
    Sum.inr (Sum.inr (495, 14)),
    Sum.inr (Sum.inr (421, 10)),
    Sum.inr (Sum.inr (303, 22)),
    Sum.inr (Sum.inr (421, 12)),
    Sum.inr (Sum.inr (366, 23)),
    Sum.inr (Sum.inr (495, 9)),
    Sum.inr (Sum.inr (303, 1)),
    Sum.inr (Sum.inr (123, 16)),
    Sum.inr (Sum.inr (123, 17)),
    Sum.inr (Sum.inr (112, 4)),
    Sum.inr (Sum.inr (123, 19)),
    Sum.inr (Sum.inr (421, 20)),
    Sum.inr (Sum.inr (495, 2)),
    Sum.inr (Sum.inr (303, 11)),
    Sum.inr (Sum.inr (366, 13)),
    Sum.inr (Sum.inr (295, 13)),
    Sum.inr (Sum.inr (358, 11)),
    Sum.inr (Sum.inr (422, 2)),
    Sum.inr (Sum.inr (492, 20)),
    Sum.inr (Sum.inr (57, 18)),
    Sum.inr (Sum.inr (50, 5)),
    Sum.inr (Sum.inr (57, 7)),
    Sum.inr (Sum.inr (57, 6)),
    Sum.inr (Sum.inr (295, 23)),
    Sum.inr (Sum.inr (422, 9)),
    Sum.inr (Sum.inr (492, 12)),
    Sum.inr (Sum.inr (358, 1)),
    Sum.inr (Sum.inr (492, 10)),
    Sum.inr (Sum.inr (295, 0)),
    Sum.inr (Sum.inr (422, 14)),
    Sum.inr (Sum.inr (358, 22)),
    Sum.inr (Sum.inr (50, 16)),
    Sum.inr (Sum.inr (50, 17)),
    Sum.inr (Sum.inr (57, 4)),
    Sum.inr (Sum.inr (50, 19)),
    Sum.inr (Sum.inr (492, 3)),
    Sum.inr (Sum.inr (422, 21)),
    Sum.inr (Sum.inr (358, 15)),
    Sum.inr (Sum.inr (295, 8)),
    Sum.inr (Sum.inr (486, 23)),
    Sum.inr (Sum.inr (423, 1)),
    Sum.inr (Sum.inr (359, 9)),
    Sum.inr (Sum.inr (301, 12)),
    Sum.inr (Sum.inr (248, 18)),
    Sum.inr (Sum.inr (243, 5)),
    Sum.inr (Sum.inr (248, 7)),
    Sum.inr (Sum.inr (248, 6)),
    Sum.inr (Sum.inr (486, 13)),
    Sum.inr (Sum.inr (359, 2)),
    Sum.inr (Sum.inr (301, 20)),
    Sum.inr (Sum.inr (423, 11)),
    Sum.inr (Sum.inr (301, 3)),
    Sum.inr (Sum.inr (486, 8)),
    Sum.inr (Sum.inr (359, 21)),
    Sum.inr (Sum.inr (423, 15)),
    Sum.inr (Sum.inr (243, 16)),
    Sum.inr (Sum.inr (243, 17)),
    Sum.inr (Sum.inr (248, 4)),
    Sum.inr (Sum.inr (243, 19)),
    Sum.inr (Sum.inr (301, 10)),
    Sum.inr (Sum.inr (359, 14)),
    Sum.inr (Sum.inr (423, 22)),
    Sum.inr (Sum.inr (486, 0)),
    Sum.inr (Sum.inl (210, 17)),
    Sum.inr (Sum.inl (204, 6)),
    Sum.inr (Sum.inl (147, 4)),
    Sum.inr (Sum.inl (170, 22)),
    Sum.inr (Sum.inl (35, 4)),
    Sum.inr (Sum.inl (15, 50)),
    Sum.inr (Sum.inl (35, 12)),
    Sum.inr (Sum.inl (35, 0)),
    Sum.inr (Sum.inl (210, 62)),
    Sum.inr (Sum.inl (147, 22)),
    Sum.inr (Sum.inl (170, 6)),
    Sum.inr (Sum.inl (204, 36)),
    Sum.inr (Sum.inl (170, 4)),
    Sum.inr (Sum.inl (210, 42)),
    Sum.inr (Sum.inl (147, 20)),
    Sum.inr (Sum.inl (204, 59)),
    Sum.inr (Sum.inl (15, 18)),
    Sum.inr (Sum.inl (15, 34)),
    Sum.inr (Sum.inl (35, 8)),
    Sum.inr (Sum.inl (15, 2)),
    Sum.inr (Sum.inl (170, 20)),
    Sum.inr (Sum.inl (147, 6)),
    Sum.inr (Sum.inl (204, 25)),
    Sum.inr (Sum.inl (210, 5)),
    Sum.inr (Sum.inl (133, 57)),
    Sum.inr (Sum.inl (132, 38)),
    Sum.inr (Sum.inl (126, 39)),
    Sum.inr (Sum.inl (128, 62)),
    Sum.inr (Sum.inl (26, 58)),
    Sum.inr (Sum.inl (6, 12)),
    Sum.inr (Sum.inl (26, 50)),
    Sum.inr (Sum.inl (26, 62)),
    Sum.inr (Sum.inl (133, 22)),
    Sum.inr (Sum.inl (126, 6)),
    Sum.inr (Sum.inl (128, 46)),
    Sum.inr (Sum.inl (132, 7)),
    Sum.inr (Sum.inl (128, 54)),
    Sum.inr (Sum.inl (133, 40)),
    Sum.inr (Sum.inl (126, 38)),
    Sum.inr (Sum.inl (132, 57)),
    Sum.inr (Sum.inl (6, 44)),
    Sum.inr (Sum.inl (6, 28)),
    Sum.inr (Sum.inl (26, 54)),
    Sum.inr (Sum.inl (6, 60)),
    Sum.inr (Sum.inl (128, 38)),
    Sum.inr (Sum.inl (126, 7)),
    Sum.inr (Sum.inl (132, 24)),
    Sum.inr (Sum.inl (133, 7)),
    Sum.inr (Sum.inl (88, 43)),
    Sum.inr (Sum.inl (87, 52)),
    Sum.inr (Sum.inl (81, 21)),
    Sum.inr (Sum.inl (83, 59)),
    Sum.inr (Sum.inl (23, 27)),
    Sum.inr (Sum.inl (3, 5)),
    Sum.inr (Sum.inl (23, 19)),
    Sum.inr (Sum.inl (23, 31))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock067Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨17152 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock067InputMaskData : ℕ :=
  sixthHex% [
    "8c5156845156885956c05956f0a156d0a156e0a95680a956b3e95585e955",
    "9ee955e8e9558f2155912155b62155e82155974155bd4155824955e84955",
    "ab7955a97955aa7155e87155a46155ac6155a06955e86955d89155f89155",
    "c89955a89955d10154e70154fc01548a0154edc954f3c954d4c9548ac954",
    "f5a954dfa954e0a1548aa154c99954cb9954c891548a9154c68954ce8954",
    "c281548a8154ba71549a7154aa7954ca7954998153af8153b48153c28153",
    "a54153bb41539c4153c24153bd2153972153a82953c22953811153831153",
    "801953c219538e09538609538a0153c20153f2f953d2f953e2f15382f153",
    "fb6952cd6952d66952a06952c7a952d9a952fea952a0a952dfc952f5c952",
    "cac152a0c152e3f152e1f152e2f952a0f952ece152e4e152e8e952a0e952",
    "901952b01952801152e01152d35951e55951fe5951885951ef9951f19951",
    "d69951889951f7f151ddf151e2f95188f951cbc951c9c951cac15188c151",
    "c4d151ccd151c0d95188d951b82951982951a82151c82151f1b150c7b150",
    "dcb150aab150cd7150d37150f47150aa7150d51950ff1950c01150aa1150",
    "e92950eb2950e82150aa2150e63950ee3950e23150aa31509ac950bac950",
    "8ac150eac150ffc93fc9c93fd2c13fa4c13fc3013fdd013ffa013fa4013f",
    "db693ff1613fce693fa4613fe7513fe5593fe6593fa4513fe8493fe0493f",
    "ec493fa4493f94b13fb4b13f84b93fe4b93f9c213eaa213eb1293ec7293e",
    "a0e93ebee93e99e93ec7e93eb8813e92893ead813ec7893e84b13e86b93e",
    "85b93ec7b13e8ba13e83a13e8fa13ec7a13ef7513ed7513ee7593e87593e",
    "8a113dbc113da7193dd1193db6d93da8d93d8fd93dd1d93daeb93d84b13d",
    "bbb93dd1b13d92893d90813d93813dd1893d9d913d95913d99913dd1913d",
    "e1613dc1613df1693d91693da9f93c9ff93c84f13cf2f13c95313c8b313c",
    "ac313cf2313c8d513ca7593c98513cf2593cb1693cb3613cb0613cf2693c",
    "be793cb6793cba793cf2793cc2813ce2813cd2893cb2893c9f793ba9793b",
    "b2713bc4713ba3b93bbdb93b9ab93bc4b93b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock067InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock067InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock067OutputMaskData : ℕ :=
  sixthHex% [
    "222e382a2638626e331f663862c95d668067315347401a767f2b4f586a7e",
    "55f15e07b06418270a33270121270a7f270a3b827e07115e4e834f071064",
    "76f27e46206410295e55fb4f066f010e6701462f0a3b270146886442c15e",
    "15127e645b4f79b86e5ef95f53627f0123451eb42b35b42027b42b79b42b",
    "3d115f01827f48106e01834501215f31f34567fa7f22286e00fc2008f420",
    "40bc2b3db420315b4535127f62c15f13886eb20fb6954e8798d5a7ca949d",
    "a443f38f43f89d43f3c343f387e687bb75a7f2e7b6bb749dbbd6878b049d",
    "dd0da798dfb6cb4bf8c343f88b0bf3f603f88bac9d8fe5a7d83687a97fb6",
    "b49c9793dda69e4686cc07bca2d0d289d0d99bd0d2c5d0d28175a6bde686",
    "f47497bde7bccc05a6fcd7bcaade86ef0c97cdd8d9c5d0d98d98d2f090d9",
    "fc7fbcf83686afe5a6deac9790ddaeb79c9fba07bfe846858691ebad91e0",
    "bf91ebe191ebd4749fe8e7bfa175aee8e68599049fa9d685ffdfbfba0dae",
    "e999e0e191e0a9d9ebd4d1e0d83e85dc77bf8ba49ffaedaee34e84c40fb5",
    "c994959bd5aff502c1de02cacc02c19202c1a7e7b59b7495d2e6849b75af",
    "9bd7b5ab05affd0c95b8de849a0aca9202cada4ac1a742cadaedafdea495",
    "8977b5f83e840104402645715a9e5108df6b6608054d080e5f0805010805",
    "34ed71793e5130ac40087f6b799d71380f6b1f46512bd44009000e01080e",
    "38000545080e38a76b3cee516b3d711a7440100c41374d704b965019d76a",
    "7700045c000f4e000410000425e57068365021a44119776a19d57058476a",
    "7f0e504b9c4118080f10000f29080454000f58ef6a5ca6500b75707a3c41",
    "1b04493c4578409e5812df627c080c57080745080c1b080c5fad78127e58",
    "5bec49633f62639d78220f6205465831d4491300071b080722000c5f0807",
    "53e76257ae58007d787134497f0c43584d7224965276d76818000633000d",
    "2100067f00063ba5727676523fe44307376876d572374768100e52249c43",
    "77080d7f000d4608063b000d46af6842e652153572647c43eef2a1c9b390",
    "b568b0e7298af8bee4d3beefc1bee49fbee4"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock067OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock067OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock067InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock067InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock067InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock067OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df85f85f85f7e196175d8617df85f85f7df7df7e185f85f85f96175d",
    "85f7e17df8617df7df7e17e17df85f6e18e386185f7e18617e18617df7e1",
    "7df7e16e18e385f86186185f7e18617df85f7df85f6e18e37df7e17e1861",
    "7e186186185f7df7e16e18e37e17df86185f7e18618617e17e18616e18e3",
    "86185f8617e186185f8617e17e17df6e18e385f8617e17df86185f86185f",
    "85f7df95f75d86185f7df85f7df7e18617e17e17df6e18e37e17df7e17df",
    "86185f7df7e17df8616df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock067OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock067OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block067_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock067Input a) =
      generatedSixthXiShortBlock067InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock067Output a) =
      generatedSixthXiShortBlock067OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock067Input a) =
      generatedSixthXiShortBlock067InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock067Output a) =
      generatedSixthXiShortBlock067OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block067_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock067InputMask a) =
      generatedSixthXiShortBlock067OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock067InputMask a)) *
      generatedSixthXiShortBlock067InputNumerator a =
        generatedSixthXiShortBlock067OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block067_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock067Input a
    let y := generatedSixthXiShortBlock067Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block067_cache a
  have hs := generatedSixth_xi_short_block067_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block067_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock067Input a
    let y := generatedSixthXiShortBlock067Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block067_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block067_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock067Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block067_certificate a).1
    (generatedSixth_xi_short_block067_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
