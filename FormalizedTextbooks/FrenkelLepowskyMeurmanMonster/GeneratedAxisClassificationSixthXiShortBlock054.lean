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
def generatedSixthXiShortBlock054Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (333, 22)),
    Sum.inr (Sum.inr (455, 1)),
    Sum.inr (Sum.inr (263, 22)),
    Sum.inr (Sum.inr (397, 1)),
    Sum.inr (Sum.inr (147, 22)),
    Sum.inr (Sum.inr (25, 1)),
    Sum.inr (Sum.inr (217, 22)),
    Sum.inr (Sum.inr (83, 1)),
    Sum.inr (Sum.inr (217, 11)),
    Sum.inr (Sum.inr (83, 15)),
    Sum.inr (Sum.inr (147, 11)),
    Sum.inr (Sum.inr (25, 15)),
    Sum.inr (Sum.inr (263, 11)),
    Sum.inr (Sum.inr (397, 15)),
    Sum.inr (Sum.inr (333, 11)),
    Sum.inr (Sum.inr (455, 15)),
    Sum.inr (Sum.inr (268, 11)),
    Sum.inr (Sum.inr (390, 15)),
    Sum.inr (Sum.inr (326, 11)),
    Sum.inr (Sum.inr (460, 15)),
    Sum.inr (Sum.inr (210, 11)),
    Sum.inr (Sum.inr (88, 15)),
    Sum.inr (Sum.inr (152, 11)),
    Sum.inr (Sum.inr (18, 15)),
    Sum.inr (Sum.inr (18, 11)),
    Sum.inr (Sum.inr (152, 15)),
    Sum.inr (Sum.inr (88, 11)),
    Sum.inr (Sum.inr (210, 15)),
    Sum.inr (Sum.inr (460, 11)),
    Sum.inr (Sum.inr (326, 15)),
    Sum.inr (Sum.inr (390, 11)),
    Sum.inr (Sum.inr (268, 15)),
    Sum.inr (Sum.inr (455, 11)),
    Sum.inr (Sum.inr (333, 15)),
    Sum.inr (Sum.inr (397, 11)),
    Sum.inr (Sum.inr (263, 15)),
    Sum.inr (Sum.inr (25, 11)),
    Sum.inr (Sum.inr (147, 15)),
    Sum.inr (Sum.inr (83, 11)),
    Sum.inr (Sum.inr (217, 15)),
    Sum.inr (Sum.inr (496, 1)),
    Sum.inr (Sum.inr (238, 1)),
    Sum.inr (Sum.inr (111, 1)),
    Sum.inr (Sum.inr (369, 1)),
    Sum.inr (Sum.inr (37, 1)),
    Sum.inr (Sum.inr (315, 1)),
    Sum.inr (Sum.inr (442, 1)),
    Sum.inr (Sum.inr (164, 1)),
    Sum.inr (Sum.inr (507, 1)),
    Sum.inr (Sum.inr (229, 1)),
    Sum.inr (Sum.inr (100, 1)),
    Sum.inr (Sum.inr (378, 1)),
    Sum.inr (Sum.inr (46, 1)),
    Sum.inr (Sum.inr (304, 1)),
    Sum.inr (Sum.inr (433, 1)),
    Sum.inr (Sum.inr (175, 1)),
    Sum.inr (Sum.inr (175, 11)),
    Sum.inr (Sum.inr (433, 11)),
    Sum.inr (Sum.inr (304, 11)),
    Sum.inr (Sum.inr (46, 11)),
    Sum.inr (Sum.inr (378, 11)),
    Sum.inr (Sum.inr (100, 11)),
    Sum.inr (Sum.inr (229, 11)),
    Sum.inr (Sum.inr (507, 11)),
    Sum.inr (Sum.inr (164, 11)),
    Sum.inr (Sum.inr (442, 11)),
    Sum.inr (Sum.inr (315, 11)),
    Sum.inr (Sum.inr (37, 11)),
    Sum.inr (Sum.inr (369, 11)),
    Sum.inr (Sum.inr (111, 11)),
    Sum.inr (Sum.inr (238, 11)),
    Sum.inr (Sum.inr (496, 11)),
    Sum.inr (Sum.inr (175, 15)),
    Sum.inr (Sum.inr (433, 15)),
    Sum.inr (Sum.inr (304, 15)),
    Sum.inr (Sum.inr (46, 15)),
    Sum.inr (Sum.inr (378, 15)),
    Sum.inr (Sum.inr (100, 15)),
    Sum.inr (Sum.inr (229, 15)),
    Sum.inr (Sum.inr (507, 15)),
    Sum.inr (Sum.inr (164, 15)),
    Sum.inr (Sum.inr (442, 15)),
    Sum.inr (Sum.inr (315, 15)),
    Sum.inr (Sum.inr (37, 15)),
    Sum.inr (Sum.inr (369, 15)),
    Sum.inr (Sum.inr (111, 15)),
    Sum.inr (Sum.inr (238, 15)),
    Sum.inr (Sum.inr (496, 15)),
    Sum.inr (Sum.inr (496, 22)),
    Sum.inr (Sum.inr (238, 22)),
    Sum.inr (Sum.inr (111, 22)),
    Sum.inr (Sum.inr (369, 22)),
    Sum.inr (Sum.inr (37, 22)),
    Sum.inr (Sum.inr (315, 22)),
    Sum.inr (Sum.inr (442, 22)),
    Sum.inr (Sum.inr (164, 22)),
    Sum.inr (Sum.inr (507, 22)),
    Sum.inr (Sum.inr (229, 22)),
    Sum.inr (Sum.inr (100, 22)),
    Sum.inr (Sum.inr (378, 22)),
    Sum.inr (Sum.inr (46, 22)),
    Sum.inr (Sum.inr (304, 22)),
    Sum.inr (Sum.inr (433, 22)),
    Sum.inr (Sum.inr (175, 22)),
    Sum.inr (Sum.inr (64, 15)),
    Sum.inr (Sum.inr (64, 11)),
    Sum.inr (Sum.inr (128, 22)),
    Sum.inr (Sum.inr (128, 1)),
    Sum.inr (Sum.inr (276, 22)),
    Sum.inr (Sum.inr (276, 1)),
    Sum.inr (Sum.inr (468, 15)),
    Sum.inr (Sum.inr (468, 11)),
    Sum.inr (Sum.inr (287, 22)),
    Sum.inr (Sum.inr (287, 1)),
    Sum.inr (Sum.inr (479, 15)),
    Sum.inr (Sum.inr (479, 11)),
    Sum.inr (Sum.inr (75, 15)),
    Sum.inr (Sum.inr (75, 11)),
    Sum.inr (Sum.inr (139, 22)),
    Sum.inr (Sum.inr (139, 1)),
    Sum.inr (Sum.inr (202, 22)),
    Sum.inr (Sum.inr (202, 1)),
    Sum.inr (Sum.inr (10, 15)),
    Sum.inr (Sum.inr (10, 11)),
    Sum.inr (Sum.inr (414, 15)),
    Sum.inr (Sum.inr (414, 11)),
    Sum.inr (Sum.inr (350, 22)),
    Sum.inr (Sum.inr (350, 1)),
    Sum.inr (Sum.inr (405, 15)),
    Sum.inr (Sum.inr (405, 11)),
    Sum.inr (Sum.inr (341, 22)),
    Sum.inr (Sum.inr (341, 1)),
    Sum.inr (Sum.inr (193, 22)),
    Sum.inr (Sum.inr (193, 1)),
    Sum.inr (Sum.inr (1, 15)),
    Sum.inr (Sum.inr (1, 11)),
    Sum.inr (Sum.inr (64, 1)),
    Sum.inr (Sum.inr (64, 22)),
    Sum.inr (Sum.inr (128, 11)),
    Sum.inr (Sum.inr (128, 15)),
    Sum.inr (Sum.inr (276, 11)),
    Sum.inr (Sum.inr (276, 15)),
    Sum.inr (Sum.inr (468, 1)),
    Sum.inr (Sum.inr (468, 22)),
    Sum.inr (Sum.inr (287, 11)),
    Sum.inr (Sum.inr (287, 15)),
    Sum.inr (Sum.inr (479, 1)),
    Sum.inr (Sum.inr (479, 22)),
    Sum.inr (Sum.inr (75, 1)),
    Sum.inr (Sum.inr (75, 22)),
    Sum.inr (Sum.inr (139, 11)),
    Sum.inr (Sum.inr (139, 15)),
    Sum.inr (Sum.inr (202, 11)),
    Sum.inr (Sum.inr (202, 15)),
    Sum.inr (Sum.inr (10, 1)),
    Sum.inr (Sum.inr (10, 22)),
    Sum.inr (Sum.inr (414, 1)),
    Sum.inr (Sum.inr (414, 22)),
    Sum.inr (Sum.inr (350, 11)),
    Sum.inr (Sum.inr (350, 15)),
    Sum.inr (Sum.inr (405, 1)),
    Sum.inr (Sum.inr (405, 22)),
    Sum.inr (Sum.inr (341, 11)),
    Sum.inr (Sum.inr (341, 15)),
    Sum.inr (Sum.inr (193, 11)),
    Sum.inr (Sum.inr (193, 15)),
    Sum.inr (Sum.inr (1, 1)),
    Sum.inr (Sum.inr (1, 22)),
    Sum.inr (Sum.inr (255, 0)),
    Sum.inr (Sum.inr (416, 0)),
    Sum.inr (Sum.inr (427, 0)),
    Sum.inr (Sum.inr (244, 0)),
    Sum.inr (Sum.inr (190, 8)),
    Sum.inr (Sum.inr (481, 8)),
    Sum.inr (Sum.inr (490, 8)),
    Sum.inr (Sum.inr (181, 8)),
    Sum.inr (Sum.inr (117, 0)),
    Sum.inr (Sum.inr (298, 0)),
    Sum.inr (Sum.inr (289, 0)),
    Sum.inr (Sum.inr (126, 0)),
    Sum.inr (Sum.inr (52, 8)),
    Sum.inr (Sum.inr (363, 8)),
    Sum.inr (Sum.inr (352, 8)),
    Sum.inr (Sum.inr (63, 8)),
    Sum.inr (Sum.inr (190, 13)),
    Sum.inr (Sum.inr (481, 13)),
    Sum.inr (Sum.inr (490, 13)),
    Sum.inr (Sum.inr (181, 13)),
    Sum.inr (Sum.inr (255, 23)),
    Sum.inr (Sum.inr (416, 23)),
    Sum.inr (Sum.inr (427, 23)),
    Sum.inr (Sum.inr (244, 23)),
    Sum.inr (Sum.inr (52, 13)),
    Sum.inr (Sum.inr (363, 13)),
    Sum.inr (Sum.inr (352, 13)),
    Sum.inr (Sum.inr (63, 13)),
    Sum.inr (Sum.inr (117, 23)),
    Sum.inr (Sum.inr (298, 23)),
    Sum.inr (Sum.inr (289, 23)),
    Sum.inr (Sum.inr (126, 23)),
    Sum.inr (Sum.inr (63, 0)),
    Sum.inr (Sum.inr (352, 0)),
    Sum.inr (Sum.inr (363, 0)),
    Sum.inr (Sum.inr (52, 0)),
    Sum.inr (Sum.inr (126, 8)),
    Sum.inr (Sum.inr (289, 8)),
    Sum.inr (Sum.inr (298, 8)),
    Sum.inr (Sum.inr (117, 8)),
    Sum.inr (Sum.inr (181, 0)),
    Sum.inr (Sum.inr (490, 0)),
    Sum.inr (Sum.inr (481, 0)),
    Sum.inr (Sum.inr (190, 0)),
    Sum.inr (Sum.inr (244, 8)),
    Sum.inr (Sum.inr (427, 8)),
    Sum.inr (Sum.inr (416, 8)),
    Sum.inr (Sum.inr (255, 8)),
    Sum.inr (Sum.inr (126, 13)),
    Sum.inr (Sum.inr (289, 13)),
    Sum.inr (Sum.inr (298, 13)),
    Sum.inr (Sum.inr (117, 13)),
    Sum.inr (Sum.inr (63, 23)),
    Sum.inr (Sum.inr (352, 23)),
    Sum.inr (Sum.inr (363, 23)),
    Sum.inr (Sum.inr (52, 23)),
    Sum.inr (Sum.inr (244, 13)),
    Sum.inr (Sum.inr (427, 13)),
    Sum.inr (Sum.inr (416, 13)),
    Sum.inr (Sum.inr (255, 13)),
    Sum.inr (Sum.inr (181, 23)),
    Sum.inr (Sum.inr (490, 23)),
    Sum.inr (Sum.inr (481, 23)),
    Sum.inr (Sum.inr (190, 23)),
    Sum.inr (Sum.inr (497, 8)),
    Sum.inr (Sum.inr (239, 0)),
    Sum.inr (Sum.inr (506, 8)),
    Sum.inr (Sum.inr (228, 0)),
    Sum.inr (Sum.inr (110, 8)),
    Sum.inr (Sum.inr (368, 0)),
    Sum.inr (Sum.inr (101, 8)),
    Sum.inr (Sum.inr (379, 0)),
    Sum.inr (Sum.inr (36, 8)),
    Sum.inr (Sum.inr (314, 0)),
    Sum.inr (Sum.inr (47, 8)),
    Sum.inr (Sum.inr (305, 0)),
    Sum.inr (Sum.inr (443, 8)),
    Sum.inr (Sum.inr (165, 0)),
    Sum.inr (Sum.inr (432, 8)),
    Sum.inr (Sum.inr (174, 0)),
    Sum.inr (Sum.inr (174, 8)),
    Sum.inr (Sum.inr (432, 0)),
    Sum.inr (Sum.inr (165, 8)),
    Sum.inr (Sum.inr (443, 0)),
    Sum.inr (Sum.inr (305, 8)),
    Sum.inr (Sum.inr (47, 0)),
    Sum.inr (Sum.inr (314, 8)),
    Sum.inr (Sum.inr (36, 0))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock054Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨13824 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock054InputMaskData : ℕ :=
  sixthHex% [
    "91c4030ac40385c4001e440324c400bf4400304403ab4400b1c4032ac403",
    "a5c4003e440304c4009f44001044038b440334c400af4400204403bb4400",
    "8144031a44039544000ec404fa86e22286e6a286e07a06e22386e4fb06e0",
    "7b06e6a306e63386e0eb06e46b06e2b306e0ea06e63206e2b206e46a86e4",
    "8086e25806e6d806e00006e25906e48106e00106e6d986e64906e09106e4",
    "1106e2c986e09006e64886e2c886e41086e77086e1a806e52806e3f006e1",
    "a906e77106e3f106e52986e5b906e36106e7e106e13986e36006e5b886e1",
    "3886e7e086e70a06e1d206e55206e38a86e1d306e70b86e38b86e55386e5",
    "c306e31b86e79b86e14386e31a86e5c286e14286e79a06e406b900d1b903",
    "d1b9070639065eb9028939018939055e39061eb902c93901c939051e3904",
    "46390091390391390746b906cfb902183901183905cf3904973900403903",
    "40390797b904d73900003903003907d7b9068f390258b90158b9058fb906",
    "efb902383901383905ef3904b73900603903603907b7b904f73900203903",
    "203907f7b906af390278b90178b905afb904263900f13903f1390726b906",
    "7e3902a9b901a9b9057eb9063e3902e9b901e9b9053eb90466b900b1b903",
    "b1b9076639062c5705b75700b757032cd702b757012cd7042cd707b7d705",
    "385706a3d703a3d70038d701a3d70238d70738d704a3570589570612d703",
    "12d70089d70112d70289d70789d7041257069dd70506d70006d7039d5702",
    "06d7019d57049d57070657064a5705d1d700d1d7034ad702d1d7014ad704",
    "4ad707d157055ed706c5d703c5d7005e5701c5d7025e57075e5704c55705",
    "efd70674d70374d700ef570174d702ef5707ef5704745706fbd705605700",
    "605703fb5702605701fb5704fb570760d707cfbf35c2bf36c2bf34cf3f33",
    "4dbf31403f32403f304d3f338dbf31803f32803f308d3f370f3f35023f36",
    "023f340fbf37ccbf35c13f36c13f34cc3f334e3f31433f32433f304ebf33",
    "8e3f31833f32833f308ebf370c3f3501bf3601bf340cbf33fcbf31f13f32",
    "f13f30fc3f377e3f35733f36733f347ebf3"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock054InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock054InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock054OutputMaskData : ℕ :=
  sixthHex% [
    "a000b4863cfaa448bff334f1830eebd472a5f606e0d03aae90d2aeb6eee0",
    "949aa5c3e6ebb3dcf1e4a0bfc6d4fae0e8b49495cbc3e985e19dc0c7a18e",
    "c6db94e0e7dac2939f95efd19532cef67fb18b77ba997ac5e9e3fffbee80",
    "86e68be5abf48b78d49975abe47da08730df86e9e5e5a49a98ac918aa1ee",
    "83dbff91d680ecde8b8f93f48e4aceed07b1900fba8202c5ecd1e58f9c9a",
    "f29491e099ee9000d4820dabff05a09c48dfbb09eea90491d40c9ab741e5",
    "b698dfd5d5a0a8ddabbad0d4d403f4b74e8bca4680d84bffa8d2c5badfba",
    "c7d7b1a49acedca0dfbfeda0c2e5abd0e8d4a071eeb27c91cf749aac39e5",
    "c2eac5d0e7baadefb1cea2cecf7bf4ac368bd13e80c333ffad9801e0e001",
    "c67321fa4b21b3dd758fe575a97655e40e5582dd7ebee57e98765ed50e5e",
    "edd80aa0a00a86332aba0b2ab3d21b8fea1ba9793be4013bdcd76f91af6f",
    "b73c4f8b044fedd764a0af64863c44ba0444f39210cfaa10e93930a44130",
    "830001bf380199ab21d4d321ec0575a17d7587ee55bbd655dd057e907d7e",
    "b6ee5e8ad65ec3400aff780ad9eb2a94932aec0a1ba1721b87e13bbbd93b",
    "f24f6fce776fe8e44fa59c4fc34f64ff7764d9e444949c44ac4a10e13210",
    "c7a130fb9930ec4aafca76e19dacf0cad0be99e5cace9984994395bf7fdb",
    "e802a4bf7eeae8a4fbce98b5ecedc1cad18f9d0b9eca77d0d8dfd08fa39e",
    "d8798ffe45c1dc30b5fa0cfbadd6eafaaaa4add7db8beb95dc31848b4dca",
    "d878be8f04f0d8dee1fee2afe4efd0b3939ee4498fc275c1e000b5c63cfb",
    "91e6eac69aa491e7dbb7db95e00184b77dcae448beb334f0e4eee1c2d2af",
    "a13aaf8706e1d0dcf087a0bed495ca83e984d43395f20fdba572a4f20eea",
    "a5d4fb83e8b5a19dc187a18fd07b9e8707d0931349811153a78273c4c069",
    "d22c27b16e3d97fd1d85ff07eb242c886636aef516bcf70cdb5b42c95958",
    "efca788c8862b0b862d3fa78f56958e76b4280c70c92c516b45636d7142c",
    "b9cf07abcd1d8d5e3dee1c27f8f0699bb273bd2153af2349e2f15381b349",
    "a72069b52273d28e3dc08c27e61f07855d1d"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock054OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock054OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock054InputNumeratorData : ℕ :=
  sixthHex% [
    "86185f7e18617df7e185f7df85f7df86185f86185f7e18617e18617df7e1",
    "7e18617df7e17df7e185f7df85f7df86185f86185f7e186186185f7e1861",
    "7e18617df7e17df85f85f86185f8618617e17e17df7df85f7df85f85f861",
    "7e17df7df85f7df85f85f8618617e17e17df7e17df7df85f85f8617df85f",
    "8617e185f8617df85f7e17df85f8617df85f8617e185f8617e17df8617e1",
    "85f8617df85f8617e185f8618617e17e17df85f8618617e17e17df7df85f",
    "8617e17e17df85f8618617e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock054InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock054InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock054OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df7df7e17e186186185f7df7e17e18617df85f7e17df7e17df8617e1",
    "7e17df8617e18617e185f86185f8617df85f7df85f7e17df7df85f7e17df",
    "7e17df8617e17df7e185f7df7e18617df7e17e18617df7e186185f7e1861",
    "7e18617df7e186185f7e186186185f7e186185f7df86185f7e186186185f",
    "86185f85f7df86185f85f7df85f7df7df7e17df7e17e18617e186186185f",
    "7e186186185f86185f85f7df8617e185f8617e17df8617e17e17df8617e1",
    "7df85f7e17df85f8617df85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock054OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock054OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block054_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock054Input a) =
      generatedSixthXiShortBlock054InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock054Output a) =
      generatedSixthXiShortBlock054OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock054Input a) =
      generatedSixthXiShortBlock054InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock054Output a) =
      generatedSixthXiShortBlock054OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block054_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock054InputMask a) =
      generatedSixthXiShortBlock054OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock054InputMask a)) *
      generatedSixthXiShortBlock054InputNumerator a =
        generatedSixthXiShortBlock054OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block054_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock054Input a
    let y := generatedSixthXiShortBlock054Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block054_cache a
  have hs := generatedSixth_xi_short_block054_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block054_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock054Input a
    let y := generatedSixthXiShortBlock054Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block054_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block054_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock054Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block054_certificate a).1
    (generatedSixth_xi_short_block054_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
