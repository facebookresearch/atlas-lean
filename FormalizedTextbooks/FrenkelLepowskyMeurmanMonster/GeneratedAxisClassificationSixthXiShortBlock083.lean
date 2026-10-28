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
def generatedSixthXiShortBlock083Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (258, 8)),
    Sum.inr (Sum.inr (387, 2)),
    Sum.inr (Sum.inr (457, 12)),
    Sum.inr (Sum.inr (323, 22)),
    Sum.inr (Sum.inr (457, 10)),
    Sum.inr (Sum.inr (258, 13)),
    Sum.inr (Sum.inr (387, 21)),
    Sum.inr (Sum.inr (323, 1)),
    Sum.inr (Sum.inr (23, 16)),
    Sum.inr (Sum.inr (23, 17)),
    Sum.inr (Sum.inr (28, 6)),
    Sum.inr (Sum.inr (23, 19)),
    Sum.inr (Sum.inr (457, 3)),
    Sum.inr (Sum.inr (387, 14)),
    Sum.inr (Sum.inr (323, 11)),
    Sum.inr (Sum.inr (258, 23)),
    Sum.inr (Sum.inr (386, 8)),
    Sum.inr (Sum.inr (451, 22)),
    Sum.inr (Sum.inr (259, 2)),
    Sum.inr (Sum.inr (329, 12)),
    Sum.inr (Sum.inr (156, 7)),
    Sum.inr (Sum.inr (151, 5)),
    Sum.inr (Sum.inr (156, 18)),
    Sum.inr (Sum.inr (156, 4)),
    Sum.inr (Sum.inr (386, 0)),
    Sum.inr (Sum.inr (259, 9)),
    Sum.inr (Sum.inr (329, 20)),
    Sum.inr (Sum.inr (451, 15)),
    Sum.inr (Sum.inr (329, 3)),
    Sum.inr (Sum.inr (386, 23)),
    Sum.inr (Sum.inr (259, 14)),
    Sum.inr (Sum.inr (451, 11)),
    Sum.inr (Sum.inr (151, 16)),
    Sum.inr (Sum.inr (151, 17)),
    Sum.inr (Sum.inr (156, 6)),
    Sum.inr (Sum.inr (151, 19)),
    Sum.inr (Sum.inr (329, 10)),
    Sum.inr (Sum.inr (259, 21)),
    Sum.inr (Sum.inr (451, 1)),
    Sum.inr (Sum.inr (386, 13)),
    Sum.inr (Sum.inl (213, 55)),
    Sum.inr (Sum.inl (207, 9)),
    Sum.inr (Sum.inl (150, 10)),
    Sum.inr (Sum.inl (173, 42)),
    Sum.inr (Sum.inl (38, 10)),
    Sum.inr (Sum.inl (18, 50)),
    Sum.inr (Sum.inl (38, 2)),
    Sum.inr (Sum.inl (38, 0)),
    Sum.inr (Sum.inl (213, 40)),
    Sum.inr (Sum.inl (150, 42)),
    Sum.inr (Sum.inl (173, 8)),
    Sum.inr (Sum.inl (207, 40)),
    Sum.inr (Sum.inl (173, 10)),
    Sum.inr (Sum.inl (213, 22)),
    Sum.inr (Sum.inl (150, 2)),
    Sum.inr (Sum.inl (207, 55)),
    Sum.inr (Sum.inl (18, 18)),
    Sum.inr (Sum.inl (18, 34)),
    Sum.inr (Sum.inl (38, 8)),
    Sum.inr (Sum.inl (18, 2)),
    Sum.inr (Sum.inl (173, 40)),
    Sum.inr (Sum.inl (150, 34)),
    Sum.inr (Sum.inl (207, 22)),
    Sum.inr (Sum.inl (213, 9)),
    Sum.inr (Sum.inl (158, 26)),
    Sum.inr (Sum.inl (157, 56)),
    Sum.inr (Sum.inl (140, 39)),
    Sum.inr (Sum.inl (153, 24)),
    Sum.inr (Sum.inl (28, 37)),
    Sum.inr (Sum.inl (8, 9)),
    Sum.inr (Sum.inl (28, 45)),
    Sum.inr (Sum.inl (28, 47)),
    Sum.inr (Sum.inl (158, 53)),
    Sum.inr (Sum.inl (140, 8)),
    Sum.inr (Sum.inl (153, 58)),
    Sum.inr (Sum.inl (157, 26)),
    Sum.inr (Sum.inl (153, 26)),
    Sum.inr (Sum.inl (158, 33)),
    Sum.inr (Sum.inl (140, 53)),
    Sum.inr (Sum.inl (157, 39)),
    Sum.inr (Sum.inl (8, 41)),
    Sum.inr (Sum.inl (8, 25)),
    Sum.inr (Sum.inl (28, 39)),
    Sum.inr (Sum.inl (8, 57)),
    Sum.inr (Sum.inl (153, 56)),
    Sum.inr (Sum.inl (140, 26)),
    Sum.inr (Sum.inl (157, 5)),
    Sum.inr (Sum.inl (158, 14)),
    Sum.inr (Sum.inl (53, 11)),
    Sum.inr (Sum.inl (52, 21)),
    Sum.inr (Sum.inl (46, 53)),
    Sum.inr (Sum.inl (48, 61)),
    Sum.inr (Sum.inl (21, 52)),
    Sum.inr (Sum.inl (1, 12)),
    Sum.inr (Sum.inl (21, 60)),
    Sum.inr (Sum.inl (21, 62)),
    Sum.inr (Sum.inl (53, 26)),
    Sum.inr (Sum.inl (46, 36)),
    Sum.inr (Sum.inl (48, 45)),
    Sum.inr (Sum.inl (52, 53)),
    Sum.inr (Sum.inl (48, 57)),
    Sum.inr (Sum.inl (53, 10)),
    Sum.inr (Sum.inl (46, 37)),
    Sum.inr (Sum.inl (52, 52)),
    Sum.inr (Sum.inl (1, 44)),
    Sum.inr (Sum.inl (1, 28)),
    Sum.inr (Sum.inl (21, 54)),
    Sum.inr (Sum.inl (1, 60)),
    Sum.inr (Sum.inl (48, 41)),
    Sum.inr (Sum.inl (46, 52)),
    Sum.inr (Sum.inl (52, 20)),
    Sum.inr (Sum.inl (53, 27)),
    Sum.inr (Sum.inl (119, 39)),
    Sum.inr (Sum.inl (118, 45)),
    Sum.inr (Sum.inl (112, 26)),
    Sum.inr (Sum.inl (114, 5)),
    Sum.inr (Sum.inl (25, 21)),
    Sum.inr (Sum.inl (5, 5)),
    Sum.inr (Sum.inl (25, 29)),
    Sum.inr (Sum.inl (25, 31)),
    Sum.inr (Sum.inl (119, 54)),
    Sum.inr (Sum.inl (112, 8)),
    Sum.inr (Sum.inl (114, 21)),
    Sum.inr (Sum.inl (118, 50)),
    Sum.inr (Sum.inl (114, 23)),
    Sum.inr (Sum.inl (119, 8)),
    Sum.inr (Sum.inl (112, 39)),
    Sum.inr (Sum.inl (118, 26)),
    Sum.inr (Sum.inl (5, 37)),
    Sum.inr (Sum.inl (5, 21)),
    Sum.inr (Sum.inl (25, 23)),
    Sum.inr (Sum.inl (5, 53)),
    Sum.inr (Sum.inl (114, 7)),
    Sum.inr (Sum.inl (112, 53)),
    Sum.inr (Sum.inl (118, 5)),
    Sum.inr (Sum.inl (119, 25)),
    Sum.inr (Sum.inr (393, 8)),
    Sum.inr (Sum.inr (456, 22)),
    Sum.inr (Sum.inr (264, 2)),
    Sum.inr (Sum.inr (322, 12)),
    Sum.inr (Sum.inr (151, 7)),
    Sum.inr (Sum.inr (156, 5)),
    Sum.inr (Sum.inr (151, 18)),
    Sum.inr (Sum.inr (151, 4)),
    Sum.inr (Sum.inr (393, 0)),
    Sum.inr (Sum.inr (264, 9)),
    Sum.inr (Sum.inr (322, 20)),
    Sum.inr (Sum.inr (456, 15)),
    Sum.inr (Sum.inr (322, 3)),
    Sum.inr (Sum.inr (393, 23)),
    Sum.inr (Sum.inr (264, 14)),
    Sum.inr (Sum.inr (456, 11)),
    Sum.inr (Sum.inr (156, 16)),
    Sum.inr (Sum.inr (156, 17)),
    Sum.inr (Sum.inr (151, 6)),
    Sum.inr (Sum.inr (156, 19)),
    Sum.inr (Sum.inr (322, 10)),
    Sum.inr (Sum.inr (264, 21)),
    Sum.inr (Sum.inr (456, 1)),
    Sum.inr (Sum.inr (393, 13)),
    Sum.inr (Sum.inr (265, 0)),
    Sum.inr (Sum.inr (328, 15)),
    Sum.inr (Sum.inr (392, 9)),
    Sum.inr (Sum.inr (450, 20)),
    Sum.inr (Sum.inr (23, 7)),
    Sum.inr (Sum.inr (28, 5)),
    Sum.inr (Sum.inr (23, 18)),
    Sum.inr (Sum.inr (23, 4)),
    Sum.inr (Sum.inr (265, 8)),
    Sum.inr (Sum.inr (392, 2)),
    Sum.inr (Sum.inr (450, 12)),
    Sum.inr (Sum.inr (328, 22)),
    Sum.inr (Sum.inr (450, 10)),
    Sum.inr (Sum.inr (265, 13)),
    Sum.inr (Sum.inr (392, 21)),
    Sum.inr (Sum.inr (328, 1)),
    Sum.inr (Sum.inr (28, 16)),
    Sum.inr (Sum.inr (28, 17)),
    Sum.inr (Sum.inr (23, 6)),
    Sum.inr (Sum.inr (28, 19)),
    Sum.inr (Sum.inr (450, 3)),
    Sum.inr (Sum.inr (392, 14)),
    Sum.inr (Sum.inr (328, 11)),
    Sum.inr (Sum.inr (265, 23)),
    Sum.inr (Sum.inr (449, 23)),
    Sum.inr (Sum.inr (384, 11)),
    Sum.inr (Sum.inr (320, 14)),
    Sum.inr (Sum.inr (266, 3)),
    Sum.inr (Sum.inr (223, 7)),
    Sum.inr (Sum.inr (212, 5)),
    Sum.inr (Sum.inr (223, 18)),
    Sum.inr (Sum.inr (223, 4)),
    Sum.inr (Sum.inr (449, 13)),
    Sum.inr (Sum.inr (320, 21)),
    Sum.inr (Sum.inr (266, 10)),
    Sum.inr (Sum.inr (384, 1)),
    Sum.inr (Sum.inr (266, 12)),
    Sum.inr (Sum.inr (449, 8)),
    Sum.inr (Sum.inr (320, 2)),
    Sum.inr (Sum.inr (384, 22)),
    Sum.inr (Sum.inr (212, 16)),
    Sum.inr (Sum.inr (212, 17)),
    Sum.inr (Sum.inr (223, 6)),
    Sum.inr (Sum.inr (212, 19)),
    Sum.inr (Sum.inr (266, 20)),
    Sum.inr (Sum.inr (320, 9)),
    Sum.inr (Sum.inr (384, 15)),
    Sum.inr (Sum.inr (449, 0)),
    Sum.inr (Sum.inr (330, 13)),
    Sum.inr (Sum.inr (267, 1)),
    Sum.inr (Sum.inr (459, 21)),
    Sum.inr (Sum.inr (385, 10)),
    Sum.inr (Sum.inr (84, 7)),
    Sum.inr (Sum.inr (95, 5)),
    Sum.inr (Sum.inr (84, 18)),
    Sum.inr (Sum.inr (84, 4)),
    Sum.inr (Sum.inr (330, 23)),
    Sum.inr (Sum.inr (459, 14)),
    Sum.inr (Sum.inr (385, 3)),
    Sum.inr (Sum.inr (267, 11)),
    Sum.inr (Sum.inr (385, 20)),
    Sum.inr (Sum.inr (330, 0)),
    Sum.inr (Sum.inr (459, 9)),
    Sum.inr (Sum.inr (267, 15)),
    Sum.inr (Sum.inr (95, 16)),
    Sum.inr (Sum.inr (95, 17)),
    Sum.inr (Sum.inr (84, 6)),
    Sum.inr (Sum.inr (95, 19)),
    Sum.inr (Sum.inr (385, 12)),
    Sum.inr (Sum.inr (459, 2)),
    Sum.inr (Sum.inr (267, 22)),
    Sum.inr (Sum.inr (330, 8)),
    Sum.inr (Sum.inl (210, 19)),
    Sum.inr (Sum.inl (204, 19)),
    Sum.inr (Sum.inl (147, 51)),
    Sum.inr (Sum.inl (170, 33)),
    Sum.inr (Sum.inl (35, 57)),
    Sum.inr (Sum.inl (15, 61)),
    Sum.inr (Sum.inl (35, 49)),
    Sum.inr (Sum.inl (35, 61)),
    Sum.inr (Sum.inl (210, 60)),
    Sum.inr (Sum.inl (147, 33)),
    Sum.inr (Sum.inl (170, 49)),
    Sum.inr (Sum.inl (204, 49)),
    Sum.inr (Sum.inl (170, 51)),
    Sum.inr (Sum.inl (210, 40)),
    Sum.inr (Sum.inl (147, 35)),
    Sum.inr (Sum.inl (204, 46)),
    Sum.inr (Sum.inl (15, 29)),
    Sum.inr (Sum.inl (15, 45)),
    Sum.inr (Sum.inl (35, 53)),
    Sum.inr (Sum.inl (15, 13)),
    Sum.inr (Sum.inl (170, 35)),
    Sum.inr (Sum.inl (147, 49)),
    Sum.inr (Sum.inl (204, 12)),
    Sum.inr (Sum.inl (210, 7))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock083Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨21248 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock083InputMaskData : ℕ :=
  sixthHex% [
    "9b8c20ad8420b68c20c08c20a74c20b944209e4c20c04c20bf2c20952420",
    "aa2c20c02c20831c20811420821c20c01c208c0420840420880420c00c20",
    "f0fc20d0fc20e0fc2080f420d84bffee4bfff54bff834bffe48bfffa8bff",
    "dd8bff838bfffcebffd6e3ffe9e3ff83ebffc0dbffc2d3ffc1d3ff83dbff",
    "cfc3ffc7cbffcbcbff83c3ffb333ff933bffa33bffc333ffaba3fe9da3fe",
    "86a3fef0a3fe9763fe8963feae63fef063fe8f03fea50bfe9a0bfef003fe",
    "b33bfeb133feb233fef03bfebc2bfeb423feb823fef02bfec0d3fee0dbfe",
    "d0dbfeb0d3fe9793fda193fdba93fdcc93fdab53fdb553fd9253fdcc53fd",
    "b33bfd9933fda633fdcc3bfd8f03fd8d0bfd8e0bfdcc03fd801bfd8813fd",
    "8413fdcc1bfdfce3fddcebfdecebfd8ce3fda47bfc927bfc897bfcff7bfc",
    "98bbfc86bbfca1bbfcffbbfc80d3fcaadbfc95dbfcffd3fcbce3fcbeebfc",
    "bdebfcffe3fcb3f3fcbbfbfcb7fbfcfff3fccf03fcef0bfcdf0bfcbf03fc",
    "a8fbfb9efbfb85fbfbf3fbfb9433fb8a33fbad33fbf333fb8c5bfba653fb",
    "9953fbf35bfbb06bfbb263fbb163fbf36bfbbf73fbb77bfbbb7bfbf373fb",
    "c38bfbe383fbd383fbb38bfb9b13faad13fab613fac013faa7dbfab9dbfa",
    "9edbfac0dbfabfb3fa95bbfaaabbfac0b3fa838bfa8183fa8283fac08bfa",
    "8c9bfa8493fa8893fac09bfaf06bfad063fae063fa806bfaa723f99123f9",
    "8a23f9fc23f99bebf985ebf9a2ebf9fcebf9838bf9a983f99683f9fc8bf9",
    "bfb3f9bdbbf9bebbf9fcb3f9b0abf9b8a3f9b4a3f9fcabf9cc5bf9ec53f9",
    "dc53f9bc5bf9d4cbf8e2cbf8f9cbf88fcbf8e803f8f603f8d103f88f03f8",
    "f063f8da6bf8e56bf88f63f8cc53f8ce5bf8cd5bf88f53f8c343f8cb4bf8",
    "c74bf88f43f8bfbbf89fb3f8afb3f8cfbbf8a833f79e33f78533f7f333f7",
    "94fbf78afbf7adfbf7f3fbf78c9bf7a693f79993f7f39bf7b0abf7b2a3f7",
    "b1a3f7f3abf7bfb3f7b7bbf7bbbbf7f3b3f7c34bf7e343f7d343f7b34bf7",
    "9bdbf6addbf6b6dbf6c0dbf6a713f6b913f69e13f6c013f6bf73f6957bf6",
    "aa7bf6c073f6834bf68143f68243f6c04bf6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock083InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock083InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock083OutputMaskData : ℕ :=
  sixthHex% [
    "5c306e0a315f76ea7f24ab454a7c2b103c20737c2b2d7c2b69d95f240a7f",
    "6d986e240b4555e95f147b4542727f07a06e2574202d7c2014742b183c20",
    "14d345109a7f36095f36006ef3c51ad4842bd91f0b8b5e31e5895fce8954",
    "dc895f82895fc62c2b8bff0bb32d1a8bfe31fa1c2bbb8e319cc70ba8551a",
    "8a8154f3c954cac15fc68954ca6631bf6f0b99fc2b99f51ac01701e75630",
    "eacd10b88c2ad65b44fd5b4fef5b44b15b44f5fe30b82d1080ff01b82c2a",
    "b88e30f91c2ade5510eac701b9534fc01b4ff91344f55b4f88f42afdfd10",
    "db6e30db6701f78c29d0cd18dd56388f1702e1c06ccac067d8c06c86c06c",
    "b32518fef638c62429fef702fe5518bfc702988e38ac1c298ec867f78067",
    "ce886cc2c067bf6f02ca6638ecf518ecfc29b15e39961f089b8428c9c512",
    "a7127c8c12779e127cc0127cf5f708b8242880f639b82512c9c708885512",
    "af1c289b8e39c81a77b15277885a7c84127788fd12fdf428db6708db6e39",
    "3ee9e119a8d01433f04672ca59e5a472e5af60e5a43ee5a40b00d046d3f0",
    "7e01e146d2ca3730d076a2ca51ebf06579e147adaf3ee5af07eda40ba5af",
    "760aca0303f02590d02599e1783bf15f7ac052e1e000a0da1f37b43437bf",
    "2637b47837b44dd2c00001e038d3f10000da00a2c04130da6679e052ebf1",
    "017fbf7837bf413fb44d77bf4198da3491e01202c0120bf14fa0d968e1e8",
    "657ac8373bf228ac9c03ac9711ac9c4fac9c0b09e846dac87e08d946dbf2",
    "4679e807ebf220a2c81430d936e4974fac9776a49c7aec977603f2030ac8",
    "2599e82590d97c72c25b33f356a8d304e9e91b7e87307e8c227e877c7e87",
    "38dbf37508d34ddac27509e904ebf34579e96230d356a2c205368c7c7e8c",
    "457687493e8c3491e94198d3670bf36702c2c85e32ef1f03e28423b0c519",
    "af527784527c965277c852778cf703c12423f9f632c12519b0c703f15519",
    "d61c23e28e32c05a7cb9127c801a778c527cf1fd1984f423a26703a26e32",
    "8e8c22a9cd13a45633f61709e98067c2806cd080678e8067ca251387f633",
    "bf242287f709875513c6c709e18e33d51c22"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock083OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock083OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock083InputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock083InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock083InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock083OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e17e16df8e37e185f8617df86186185f85f85f85f96175d85f7e17df861",
    "7df7df7e17e17e185f6df8e37df8617e17e186186185f7e17e17e16df8e3",
    "85f7e18617df8618617e17e185f7e196175d7df86185f85f7df7df85f7e1",
    "7df7e16e18e37e17df86185f7e18618617e17df85f6e18e37df7e17e1861",
    "7e186186185f86185f95f75d7e17df7df7e185f7df8617e17df85f6e18e3",
    "86185f7e18617e18617df7e17e185f6df8e38617df7e17e18618617e185f",
    "85f85f96175d7e185f7df861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock083OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock083OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block083_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock083Input a) =
      generatedSixthXiShortBlock083InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock083Output a) =
      generatedSixthXiShortBlock083OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock083Input a) =
      generatedSixthXiShortBlock083InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock083Output a) =
      generatedSixthXiShortBlock083OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block083_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock083InputMask a) =
      generatedSixthXiShortBlock083OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock083InputMask a)) *
      generatedSixthXiShortBlock083InputNumerator a =
        generatedSixthXiShortBlock083OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block083_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock083Input a
    let y := generatedSixthXiShortBlock083Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block083_cache a
  have hs := generatedSixth_xi_short_block083_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block083_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock083Input a
    let y := generatedSixthXiShortBlock083Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block083_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block083_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock083Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block083_certificate a).1
    (generatedSixth_xi_short_block083_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
