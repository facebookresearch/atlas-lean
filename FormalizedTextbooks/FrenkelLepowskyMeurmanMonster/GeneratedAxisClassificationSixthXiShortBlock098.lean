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
def generatedSixthXiShortBlock098Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (380, 23)),
    Sum.inr (Sum.inr (509, 21)),
    Sum.inr (Sum.inr (439, 20)),
    Sum.inr (Sum.inr (317, 22)),
    Sum.inr (Sum.inr (439, 3)),
    Sum.inr (Sum.inr (380, 0)),
    Sum.inr (Sum.inr (509, 2)),
    Sum.inr (Sum.inr (317, 1)),
    Sum.inr (Sum.inr (105, 16)),
    Sum.inr (Sum.inr (105, 17)),
    Sum.inr (Sum.inr (98, 18)),
    Sum.inr (Sum.inr (105, 19)),
    Sum.inr (Sum.inr (439, 10)),
    Sum.inr (Sum.inr (509, 9)),
    Sum.inr (Sum.inr (317, 11)),
    Sum.inr (Sum.inr (380, 8)),
    Sum.inr (Sum.inr (381, 23)),
    Sum.inr (Sum.inr (316, 22)),
    Sum.inr (Sum.inr (508, 21)),
    Sum.inr (Sum.inr (438, 20)),
    Sum.inr (Sum.inr (99, 4)),
    Sum.inr (Sum.inr (104, 5)),
    Sum.inr (Sum.inr (99, 6)),
    Sum.inr (Sum.inr (99, 7)),
    Sum.inr (Sum.inr (381, 13)),
    Sum.inr (Sum.inr (508, 14)),
    Sum.inr (Sum.inr (438, 12)),
    Sum.inr (Sum.inr (316, 15)),
    Sum.inr (Sum.inr (438, 10)),
    Sum.inr (Sum.inr (381, 8)),
    Sum.inr (Sum.inr (508, 9)),
    Sum.inr (Sum.inr (316, 11)),
    Sum.inr (Sum.inr (104, 16)),
    Sum.inr (Sum.inr (104, 17)),
    Sum.inr (Sum.inr (99, 18)),
    Sum.inr (Sum.inr (104, 19)),
    Sum.inr (Sum.inr (438, 3)),
    Sum.inr (Sum.inr (508, 2)),
    Sum.inr (Sum.inr (316, 1)),
    Sum.inr (Sum.inr (381, 0)),
    Sum.inr (Sum.inl (212, 57)),
    Sum.inr (Sum.inl (206, 14)),
    Sum.inr (Sum.inl (149, 7)),
    Sum.inr (Sum.inl (172, 47)),
    Sum.inr (Sum.inl (37, 38)),
    Sum.inr (Sum.inl (17, 32)),
    Sum.inr (Sum.inl (37, 35)),
    Sum.inr (Sum.inl (37, 47)),
    Sum.inr (Sum.inl (212, 60)),
    Sum.inr (Sum.inl (149, 2)),
    Sum.inr (Sum.inl (172, 42)),
    Sum.inr (Sum.inl (206, 11)),
    Sum.inr (Sum.inl (172, 38)),
    Sum.inr (Sum.inl (212, 48)),
    Sum.inr (Sum.inl (149, 14)),
    Sum.inr (Sum.inl (206, 7)),
    Sum.inr (Sum.inl (17, 42)),
    Sum.inr (Sum.inl (17, 41)),
    Sum.inr (Sum.inl (37, 42)),
    Sum.inr (Sum.inl (17, 35)),
    Sum.inr (Sum.inl (172, 35)),
    Sum.inr (Sum.inl (149, 11)),
    Sum.inr (Sum.inl (206, 2)),
    Sum.inr (Sum.inl (212, 53)),
    Sum.inr (Sum.inl (188, 43)),
    Sum.inr (Sum.inl (187, 52)),
    Sum.inr (Sum.inl (143, 21)),
    Sum.inr (Sum.inl (166, 34)),
    Sum.inr (Sum.inl (31, 41)),
    Sum.inr (Sum.inl (11, 9)),
    Sum.inr (Sum.inl (31, 44)),
    Sum.inr (Sum.inl (31, 32)),
    Sum.inr (Sum.inl (188, 46)),
    Sum.inr (Sum.inl (143, 16)),
    Sum.inr (Sum.inl (166, 39)),
    Sum.inr (Sum.inl (187, 49)),
    Sum.inr (Sum.inl (166, 25)),
    Sum.inr (Sum.inl (188, 16)),
    Sum.inr (Sum.inl (143, 46)),
    Sum.inr (Sum.inl (187, 15)),
    Sum.inr (Sum.inl (11, 22)),
    Sum.inr (Sum.inl (11, 38)),
    Sum.inr (Sum.inl (31, 37)),
    Sum.inr (Sum.inl (11, 57)),
    Sum.inr (Sum.inl (166, 28)),
    Sum.inr (Sum.inl (143, 43)),
    Sum.inr (Sum.inl (187, 10)),
    Sum.inr (Sum.inl (188, 21)),
    Sum.inr (Sum.inl (211, 63)),
    Sum.inr (Sum.inl (205, 32)),
    Sum.inr (Sum.inl (148, 1)),
    Sum.inr (Sum.inl (171, 30)),
    Sum.inr (Sum.inl (36, 9)),
    Sum.inr (Sum.inl (16, 15)),
    Sum.inr (Sum.inl (36, 12)),
    Sum.inr (Sum.inl (36, 0)),
    Sum.inr (Sum.inl (211, 32)),
    Sum.inr (Sum.inl (148, 30)),
    Sum.inr (Sum.inl (171, 1)),
    Sum.inr (Sum.inl (205, 63)),
    Sum.inr (Sum.inl (171, 63)),
    Sum.inr (Sum.inl (211, 30)),
    Sum.inr (Sum.inl (148, 32)),
    Sum.inr (Sum.inl (205, 1)),
    Sum.inr (Sum.inl (16, 16)),
    Sum.inr (Sum.inl (16, 32)),
    Sum.inr (Sum.inl (36, 5)),
    Sum.inr (Sum.inl (16, 63)),
    Sum.inr (Sum.inl (171, 32)),
    Sum.inr (Sum.inl (148, 63)),
    Sum.inr (Sum.inl (205, 30)),
    Sum.inr (Sum.inl (211, 1)),
    Sum.inr (Sum.inl (214, 38)),
    Sum.inr (Sum.inl (208, 57)),
    Sum.inr (Sum.inl (151, 27)),
    Sum.inr (Sum.inl (174, 4)),
    Sum.inr (Sum.inl (39, 35)),
    Sum.inr (Sum.inl (19, 3)),
    Sum.inr (Sum.inl (39, 51)),
    Sum.inr (Sum.inl (39, 12)),
    Sum.inr (Sum.inl (214, 57)),
    Sum.inr (Sum.inl (151, 4)),
    Sum.inr (Sum.inl (174, 27)),
    Sum.inr (Sum.inl (208, 38)),
    Sum.inr (Sum.inl (174, 43)),
    Sum.inr (Sum.inl (214, 9)),
    Sum.inr (Sum.inl (151, 52)),
    Sum.inr (Sum.inl (208, 22)),
    Sum.inr (Sum.inl (19, 28)),
    Sum.inr (Sum.inl (19, 44)),
    Sum.inr (Sum.inl (39, 28)),
    Sum.inr (Sum.inl (19, 51)),
    Sum.inr (Sum.inl (174, 52)),
    Sum.inr (Sum.inl (151, 43)),
    Sum.inr (Sum.inl (208, 9)),
    Sum.inr (Sum.inl (214, 22)),
    Sum.inr (Sum.inr (374, 23)),
    Sum.inr (Sum.inr (311, 22)),
    Sum.inr (Sum.inr (503, 21)),
    Sum.inr (Sum.inr (445, 20)),
    Sum.inr (Sum.inr (104, 4)),
    Sum.inr (Sum.inr (99, 5)),
    Sum.inr (Sum.inr (104, 6)),
    Sum.inr (Sum.inr (104, 7)),
    Sum.inr (Sum.inr (374, 13)),
    Sum.inr (Sum.inr (503, 14)),
    Sum.inr (Sum.inr (445, 12)),
    Sum.inr (Sum.inr (311, 15)),
    Sum.inr (Sum.inr (445, 10)),
    Sum.inr (Sum.inr (374, 8)),
    Sum.inr (Sum.inr (503, 9)),
    Sum.inr (Sum.inr (311, 11)),
    Sum.inr (Sum.inr (99, 16)),
    Sum.inr (Sum.inr (99, 17)),
    Sum.inr (Sum.inr (104, 18)),
    Sum.inr (Sum.inr (99, 19)),
    Sum.inr (Sum.inr (445, 3)),
    Sum.inr (Sum.inr (503, 2)),
    Sum.inr (Sum.inr (311, 1)),
    Sum.inr (Sum.inr (374, 0)),
    Sum.inr (Sum.inr (375, 13)),
    Sum.inr (Sum.inr (310, 15)),
    Sum.inr (Sum.inr (502, 14)),
    Sum.inr (Sum.inr (444, 12)),
    Sum.inr (Sum.inr (105, 4)),
    Sum.inr (Sum.inr (98, 5)),
    Sum.inr (Sum.inr (105, 6)),
    Sum.inr (Sum.inr (105, 7)),
    Sum.inr (Sum.inr (375, 23)),
    Sum.inr (Sum.inr (502, 21)),
    Sum.inr (Sum.inr (444, 20)),
    Sum.inr (Sum.inr (310, 22)),
    Sum.inr (Sum.inr (444, 3)),
    Sum.inr (Sum.inr (375, 0)),
    Sum.inr (Sum.inr (502, 2)),
    Sum.inr (Sum.inr (310, 1)),
    Sum.inr (Sum.inr (98, 16)),
    Sum.inr (Sum.inr (98, 17)),
    Sum.inr (Sum.inr (105, 18)),
    Sum.inr (Sum.inr (98, 19)),
    Sum.inr (Sum.inr (444, 10)),
    Sum.inr (Sum.inr (502, 9)),
    Sum.inr (Sum.inr (310, 11)),
    Sum.inr (Sum.inr (375, 8)),
    Sum.inr (Sum.inr (372, 8)),
    Sum.inr (Sum.inr (309, 11)),
    Sum.inr (Sum.inr (501, 9)),
    Sum.inr (Sum.inr (447, 10)),
    Sum.inr (Sum.inr (106, 4)),
    Sum.inr (Sum.inr (97, 5)),
    Sum.inr (Sum.inr (106, 6)),
    Sum.inr (Sum.inr (106, 7)),
    Sum.inr (Sum.inr (372, 0)),
    Sum.inr (Sum.inr (501, 2)),
    Sum.inr (Sum.inr (447, 3)),
    Sum.inr (Sum.inr (309, 1)),
    Sum.inr (Sum.inr (447, 20)),
    Sum.inr (Sum.inr (372, 23)),
    Sum.inr (Sum.inr (501, 21)),
    Sum.inr (Sum.inr (309, 22)),
    Sum.inr (Sum.inr (97, 16)),
    Sum.inr (Sum.inr (97, 17)),
    Sum.inr (Sum.inr (106, 18)),
    Sum.inr (Sum.inr (97, 19)),
    Sum.inr (Sum.inr (447, 12)),
    Sum.inr (Sum.inr (501, 14)),
    Sum.inr (Sum.inr (309, 15)),
    Sum.inr (Sum.inr (372, 13)),
    Sum.inr (Sum.inr (382, 0)),
    Sum.inr (Sum.inr (319, 1)),
    Sum.inr (Sum.inr (511, 2)),
    Sum.inr (Sum.inr (437, 3)),
    Sum.inr (Sum.inr (96, 4)),
    Sum.inr (Sum.inr (107, 5)),
    Sum.inr (Sum.inr (96, 6)),
    Sum.inr (Sum.inr (96, 7)),
    Sum.inr (Sum.inr (382, 8)),
    Sum.inr (Sum.inr (511, 9)),
    Sum.inr (Sum.inr (437, 10)),
    Sum.inr (Sum.inr (319, 11)),
    Sum.inr (Sum.inr (437, 12)),
    Sum.inr (Sum.inr (382, 13)),
    Sum.inr (Sum.inr (511, 14)),
    Sum.inr (Sum.inr (319, 15)),
    Sum.inr (Sum.inr (107, 16)),
    Sum.inr (Sum.inr (107, 17)),
    Sum.inr (Sum.inr (96, 18)),
    Sum.inr (Sum.inr (107, 19)),
    Sum.inr (Sum.inr (437, 20)),
    Sum.inr (Sum.inr (511, 21)),
    Sum.inr (Sum.inr (319, 22)),
    Sum.inr (Sum.inr (382, 23)),
    Sum.inr (Sum.inr (21, 13)),
    Sum.inr (Sum.inr (84, 1)),
    Sum.inr (Sum.inr (148, 21)),
    Sum.inr (Sum.inr (222, 10)),
    Sum.inr (Sum.inr (267, 7)),
    Sum.inr (Sum.inr (256, 5)),
    Sum.inr (Sum.inr (267, 18)),
    Sum.inr (Sum.inr (267, 4)),
    Sum.inr (Sum.inr (21, 23)),
    Sum.inr (Sum.inr (148, 14)),
    Sum.inr (Sum.inr (222, 3)),
    Sum.inr (Sum.inr (84, 11)),
    Sum.inr (Sum.inr (222, 20)),
    Sum.inr (Sum.inr (21, 0)),
    Sum.inr (Sum.inr (148, 9)),
    Sum.inr (Sum.inr (84, 15)),
    Sum.inr (Sum.inr (256, 16)),
    Sum.inr (Sum.inr (256, 17)),
    Sum.inr (Sum.inr (267, 6)),
    Sum.inr (Sum.inr (256, 19)),
    Sum.inr (Sum.inr (222, 12)),
    Sum.inr (Sum.inr (148, 2)),
    Sum.inr (Sum.inr (84, 22)),
    Sum.inr (Sum.inr (21, 8))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock098Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨25088 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock098InputMaskData : ℕ :=
  sixthHex% [
    "ca4680fc4e80e74680914680f68680e88e80cf8680918680eeee80c4ee80",
    "fbee8091e680d2de80d0de80d3de8091d680ddc680d5ce80d9c68091c680",
    "a13e80813680b13e80d13e80fc765fca765fd17e5fa7765fc0b65fdebe5f",
    "f9b65fa7b65fd8d65ff2de5fcdd65fa7d65fe4e65fe6e65fe5ee5fa7e65f",
    "ebfe5fe3fe5feff65fa7fe5f97065fb70e5f87065fe7065fae765e98765e",
    "837e5ef5765e92b65e8cbe5eabb65ef5b65e8ad65ea0de5e9fd65ef5d65e",
    "b6ee5eb4ee5eb7e65ef5ee5eb9fe5eb1fe5ebdf65ef5fe5ec50e5ee5065e",
    "d50e5eb50e5eb9765d8f765d947e5de2765d85b65d9bbe5dbcb65de2b65d",
    "9dde5db7d65d88de5de2de5da1e65da3e65da0ee5de2e65daefe5da6fe5d",
    "aaf65de2fe5dd20e5df2065dc20e5da20e5dab7e5c9d7e5c86765cf07e5c",
    "97be5c89b65caebe5cf0be5c8fd65ca5de5c9ad65cf0d65cb3e65cb1e65c",
    "b2ee5cf0e65cbcf65cb4f65cb8fe5cf0f65cc00e5ce0065cd00e5cb00e5c",
    "95765ba3765bb87e5bce765ba9be5bb7b65b90be5bcebe5bb1d65b9bde5b",
    "a4d65bced65b8de65b8fe65b8cee5bcee65b82fe5b8afe5b86f65bcefe5b",
    "fe0e5bde065bee0e5b8e0e5b877e5ab17e5aaa765adc7e5abbb65aa5be5a",
    "82b65adcb65aa3de5a89d65ab6de5adcde5a9fe65a9de65a9eee5adce65a",
    "90f65a98f65a94fe5adcf65aec0e5acc065afc0e5a9c0e5a907e59a67e59",
    "bd7659cb7e59acb659b2be5995b659cbb659b4d6599ede59a1d659cbd659",
    "88ee598aee5989e659cbee5987f6598ff65983fe59cbf659fb0e59db0659",
    "eb0e598b0e59c27e58f47e58ef7658997e58feb658e0be58c7b65899b658",
    "e6d658ccde58f3d65899d658dae658d8e658dbee5899e658d5f658ddf658",
    "d1fe5899f658a90658890e58b90658d906589a7e57ac7e57b77657c17e57",
    "a6b657b8be579fb657c1b657bed65794de57abd657c1d65782e65780e657",
    "83ee57c1e6578dfe5785fe5789f657c1fe57f10e57d10657e10e57810e57",
    "887656be7656a57e56d37656b4be56aab6568dbe56d3be56acde5686d656",
    "b9de56d3de5690e65692e65691ee56d3e656"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock098InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock098InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock098OutputMaskData : ℕ :=
  sixthHex% [
    "b10065e701549bda74c99b4ea74c20fd0c2b9e4c20c04c20f5a954c93a74",
    "f1e865c93b4ec99954f94b4ede0274ea9065b9042bc04c2b880420f50c2b",
    "88a34efdaa74aa7954db3065b6edce91acffed77dfce76e5a0a18bfae180",
    "99a18bc7a18b8304ffced7df8745ceced6e5bf34ff8fe6e5d9efdfed7dce",
    "cfa980c7a1808fe98b83a180fe0ee58b07dfdcd4ffad9dced24dc4f50cf5",
    "89d7d5aad6efc401819e418afd0181a30181e7a4f5aa77d5e3e5c4aa76ef",
    "aad4f59a06efcc0fd5f89dc4ab098aa3018aeb4981e7018aebeeef9ee7d5",
    "c934f5b87dc4ed75c7ca34f6b6efd695eeecfb3982a17989c239829c3982",
    "a9dcf6e40fd6ad9dc7e40eece4acf6d47eec8277d6b6e5c79431899c3989",
    "d47182d83989d4d6eca1dfd6f60cf68745c78d95c6aad4f7d60fd7f50eed",
    "9bd983c19988a2d983fcd983c93cf784efd7cd7dc684eeedf50cf7c5deed",
    "93d7d7a745c6f4d188fcd988b49183b8d988c576edb07fd7e7acf796e5c6",
    "59b4417ef570022e50212f6a3eb80464f80f07b80459b8046c5d70218e50",
    "681c41218f6a506d7060bf6a36b65002244120f00f28f80f60b0046cf80f",
    "60176a151e5042cd703384413954401e157162ce5141cf6b5e580504180e",
    "6758053958050cbd71416e5108fc40416f6b41cd71711f6b271651138440",
    "40100e48180e0050050c180e71b76b04be51536d71222440066c43212d72",
    "5df6527ef7686160063b200d58600606600642c5720f16524684430f1768",
    "0fb5723f6768696e525dfc437f280d77200d3f680633200d4e8f683b8652",
    "6c55721d1c4362cc49458d783956581a576205c00c5f80073cc00c62c00c",
    "2665786bb6582224496bb7621a55782a87627c8e58481c491b8807138007",
    "5bc80c5780075b6f622e665879b57808fc49b895cd9fd4fce30fdcc00ee6",
    "df998885d983e69988b89988fc3cfcb1efdcf87dcdb1eee6c00cfcf0dee6",
    "a6d7dc9245cdb09183b89983f0d188fc9983f076e6857fdcd2acfca3e5cd",
    "d875ccff34fd83efdda0eee7bf7989e53982867989d879899cdcfdd10fdd",
    "989dccd10ee7d1acfde17ee7b777dd83e5cc"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock098OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock098OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock098InputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock098InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock098InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock098OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f85f96175d85f7e17df8617df7df7e17e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df8616df8e38617df8618617e185f85f85f7df7df6df8e3",
    "7e185f7e185f7e185f7e185f8617df96175d8617df7df7df85f7e185f85f",
    "7e17df6e18e385f8617e17df86185f86185f85f7df95f75d7df7e17df85f",
    "7df7e17df85f85f86195f75d85f86185f8617df7e186185f7e18616e18e3",
    "7df7e18617e186185f7df85f8617df96175d8617df7df7df85f7e185f85f",
    "7df7df6df8e37e185f7e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock098OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock098OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block098_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock098Input a) =
      generatedSixthXiShortBlock098InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock098Output a) =
      generatedSixthXiShortBlock098OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock098Input a) =
      generatedSixthXiShortBlock098InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock098Output a) =
      generatedSixthXiShortBlock098OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block098_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock098InputMask a) =
      generatedSixthXiShortBlock098OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock098InputMask a)) *
      generatedSixthXiShortBlock098InputNumerator a =
        generatedSixthXiShortBlock098OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block098_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock098Input a
    let y := generatedSixthXiShortBlock098Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block098_cache a
  have hs := generatedSixth_xi_short_block098_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block098_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock098Input a
    let y := generatedSixthXiShortBlock098Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block098_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block098_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock098Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block098_certificate a).1
    (generatedSixth_xi_short_block098_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
