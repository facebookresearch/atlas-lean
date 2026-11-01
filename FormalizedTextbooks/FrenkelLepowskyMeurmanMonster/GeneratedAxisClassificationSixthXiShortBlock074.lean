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
def generatedSixthXiShortBlock074Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (88, 24)),
    Sum.inr (Sum.inl (81, 25)),
    Sum.inr (Sum.inl (83, 8)),
    Sum.inr (Sum.inl (87, 55)),
    Sum.inr (Sum.inl (83, 24)),
    Sum.inr (Sum.inl (88, 38)),
    Sum.inr (Sum.inl (81, 61)),
    Sum.inr (Sum.inl (87, 9)),
    Sum.inr (Sum.inl (3, 32)),
    Sum.inr (Sum.inl (3, 16)),
    Sum.inr (Sum.inl (23, 6)),
    Sum.inr (Sum.inl (3, 48)),
    Sum.inr (Sum.inl (83, 10)),
    Sum.inr (Sum.inl (81, 34)),
    Sum.inr (Sum.inl (87, 22)),
    Sum.inr (Sum.inl (88, 55)),
    Sum.inr (Sum.inl (196, 56)),
    Sum.inr (Sum.inl (195, 22)),
    Sum.inr (Sum.inl (144, 56)),
    Sum.inr (Sum.inl (167, 24)),
    Sum.inr (Sum.inl (32, 58)),
    Sum.inr (Sum.inl (12, 12)),
    Sum.inr (Sum.inl (32, 50)),
    Sum.inr (Sum.inl (32, 62)),
    Sum.inr (Sum.inl (196, 41)),
    Sum.inr (Sum.inl (144, 24)),
    Sum.inr (Sum.inl (167, 58)),
    Sum.inr (Sum.inl (195, 54)),
    Sum.inr (Sum.inl (167, 56)),
    Sum.inr (Sum.inl (196, 6)),
    Sum.inr (Sum.inl (144, 26)),
    Sum.inr (Sum.inl (195, 30)),
    Sum.inr (Sum.inl (12, 44)),
    Sum.inr (Sum.inl (12, 28)),
    Sum.inr (Sum.inl (32, 54)),
    Sum.inr (Sum.inl (12, 60)),
    Sum.inr (Sum.inl (167, 26)),
    Sum.inr (Sum.inl (144, 58)),
    Sum.inr (Sum.inl (195, 62)),
    Sum.inr (Sum.inl (196, 23)),
    Sum.inr (Sum.inr (301, 23)),
    Sum.inr (Sum.inr (364, 1)),
    Sum.inr (Sum.inr (428, 9)),
    Sum.inr (Sum.inr (486, 12)),
    Sum.inr (Sum.inr (51, 18)),
    Sum.inr (Sum.inr (56, 5)),
    Sum.inr (Sum.inr (51, 7)),
    Sum.inr (Sum.inr (51, 6)),
    Sum.inr (Sum.inr (301, 13)),
    Sum.inr (Sum.inr (428, 2)),
    Sum.inr (Sum.inr (486, 20)),
    Sum.inr (Sum.inr (364, 11)),
    Sum.inr (Sum.inr (486, 3)),
    Sum.inr (Sum.inr (301, 8)),
    Sum.inr (Sum.inr (428, 21)),
    Sum.inr (Sum.inr (364, 15)),
    Sum.inr (Sum.inr (56, 16)),
    Sum.inr (Sum.inr (56, 17)),
    Sum.inr (Sum.inr (51, 4)),
    Sum.inr (Sum.inr (56, 19)),
    Sum.inr (Sum.inr (486, 10)),
    Sum.inr (Sum.inr (428, 14)),
    Sum.inr (Sum.inr (364, 22)),
    Sum.inr (Sum.inr (301, 0)),
    Sum.inr (Sum.inr (492, 13)),
    Sum.inr (Sum.inr (429, 11)),
    Sum.inr (Sum.inr (365, 2)),
    Sum.inr (Sum.inr (295, 20)),
    Sum.inr (Sum.inr (242, 18)),
    Sum.inr (Sum.inr (249, 5)),
    Sum.inr (Sum.inr (242, 7)),
    Sum.inr (Sum.inr (242, 6)),
    Sum.inr (Sum.inr (492, 23)),
    Sum.inr (Sum.inr (365, 9)),
    Sum.inr (Sum.inr (295, 12)),
    Sum.inr (Sum.inr (429, 1)),
    Sum.inr (Sum.inr (295, 10)),
    Sum.inr (Sum.inr (492, 0)),
    Sum.inr (Sum.inr (365, 14)),
    Sum.inr (Sum.inr (429, 22)),
    Sum.inr (Sum.inr (249, 16)),
    Sum.inr (Sum.inr (249, 17)),
    Sum.inr (Sum.inr (242, 4)),
    Sum.inr (Sum.inr (249, 19)),
    Sum.inr (Sum.inr (295, 3)),
    Sum.inr (Sum.inr (365, 21)),
    Sum.inr (Sum.inr (429, 15)),
    Sum.inr (Sum.inr (492, 8)),
    Sum.inr (Sum.inr (421, 8)),
    Sum.inr (Sum.inr (484, 15)),
    Sum.inr (Sum.inr (292, 21)),
    Sum.inr (Sum.inr (366, 3)),
    Sum.inr (Sum.inr (187, 18)),
    Sum.inr (Sum.inr (176, 5)),
    Sum.inr (Sum.inr (187, 7)),
    Sum.inr (Sum.inr (187, 6)),
    Sum.inr (Sum.inr (421, 0)),
    Sum.inr (Sum.inr (292, 14)),
    Sum.inr (Sum.inr (366, 10)),
    Sum.inr (Sum.inr (484, 22)),
    Sum.inr (Sum.inr (366, 12)),
    Sum.inr (Sum.inr (421, 23)),
    Sum.inr (Sum.inr (292, 9)),
    Sum.inr (Sum.inr (484, 1)),
    Sum.inr (Sum.inr (176, 16)),
    Sum.inr (Sum.inr (176, 17)),
    Sum.inr (Sum.inr (187, 4)),
    Sum.inr (Sum.inr (176, 19)),
    Sum.inr (Sum.inr (366, 20)),
    Sum.inr (Sum.inr (292, 2)),
    Sum.inr (Sum.inr (484, 11)),
    Sum.inr (Sum.inr (421, 13)),
    Sum.inr (Sum.inr (367, 0)),
    Sum.inr (Sum.inr (302, 22)),
    Sum.inr (Sum.inr (494, 14)),
    Sum.inr (Sum.inr (420, 10)),
    Sum.inr (Sum.inr (113, 18)),
    Sum.inr (Sum.inr (122, 5)),
    Sum.inr (Sum.inr (113, 7)),
    Sum.inr (Sum.inr (113, 6)),
    Sum.inr (Sum.inr (367, 8)),
    Sum.inr (Sum.inr (494, 21)),
    Sum.inr (Sum.inr (420, 3)),
    Sum.inr (Sum.inr (302, 15)),
    Sum.inr (Sum.inr (420, 20)),
    Sum.inr (Sum.inr (367, 13)),
    Sum.inr (Sum.inr (494, 2)),
    Sum.inr (Sum.inr (302, 11)),
    Sum.inr (Sum.inr (122, 16)),
    Sum.inr (Sum.inr (122, 17)),
    Sum.inr (Sum.inr (113, 4)),
    Sum.inr (Sum.inr (122, 19)),
    Sum.inr (Sum.inr (420, 12)),
    Sum.inr (Sum.inr (494, 9)),
    Sum.inr (Sum.inr (302, 1)),
    Sum.inr (Sum.inr (367, 23)),
    Sum.inr (Sum.inl (196, 52)),
    Sum.inr (Sum.inl (195, 21)),
    Sum.inr (Sum.inl (144, 52)),
    Sum.inr (Sum.inl (167, 20)),
    Sum.inr (Sum.inl (32, 52)),
    Sum.inr (Sum.inl (12, 62)),
    Sum.inr (Sum.inl (32, 60)),
    Sum.inr (Sum.inl (32, 48)),
    Sum.inr (Sum.inl (196, 37)),
    Sum.inr (Sum.inl (144, 20)),
    Sum.inr (Sum.inl (167, 54)),
    Sum.inr (Sum.inl (195, 53)),
    Sum.inr (Sum.inl (167, 52)),
    Sum.inr (Sum.inl (196, 10)),
    Sum.inr (Sum.inl (144, 22)),
    Sum.inr (Sum.inl (195, 29)),
    Sum.inr (Sum.inl (12, 30)),
    Sum.inr (Sum.inl (12, 46)),
    Sum.inr (Sum.inl (32, 56)),
    Sum.inr (Sum.inl (12, 14)),
    Sum.inr (Sum.inl (167, 22)),
    Sum.inr (Sum.inl (144, 54)),
    Sum.inr (Sum.inl (195, 61)),
    Sum.inr (Sum.inl (196, 27)),
    Sum.inr (Sum.inl (88, 5)),
    Sum.inr (Sum.inl (87, 36)),
    Sum.inr (Sum.inl (81, 5)),
    Sum.inr (Sum.inl (83, 22)),
    Sum.inr (Sum.inl (23, 4)),
    Sum.inr (Sum.inl (3, 50)),
    Sum.inr (Sum.inl (23, 12)),
    Sum.inr (Sum.inl (23, 0)),
    Sum.inr (Sum.inl (88, 20)),
    Sum.inr (Sum.inl (81, 26)),
    Sum.inr (Sum.inl (83, 4)),
    Sum.inr (Sum.inl (87, 59)),
    Sum.inr (Sum.inl (83, 20)),
    Sum.inr (Sum.inl (88, 42)),
    Sum.inr (Sum.inl (81, 62)),
    Sum.inr (Sum.inl (87, 5)),
    Sum.inr (Sum.inl (3, 18)),
    Sum.inr (Sum.inl (3, 34)),
    Sum.inr (Sum.inl (23, 8)),
    Sum.inr (Sum.inl (3, 2)),
    Sum.inr (Sum.inl (83, 6)),
    Sum.inr (Sum.inl (81, 33)),
    Sum.inr (Sum.inl (87, 26)),
    Sum.inr (Sum.inl (88, 59)),
    Sum.inr (Sum.inl (133, 21)),
    Sum.inr (Sum.inl (132, 52)),
    Sum.inr (Sum.inl (126, 53)),
    Sum.inr (Sum.inl (128, 34)),
    Sum.inr (Sum.inl (26, 43)),
    Sum.inr (Sum.inl (6, 9)),
    Sum.inr (Sum.inl (26, 35)),
    Sum.inr (Sum.inl (26, 47)),
    Sum.inr (Sum.inl (133, 58)),
    Sum.inr (Sum.inl (126, 20)),
    Sum.inr (Sum.inl (128, 50)),
    Sum.inr (Sum.inl (132, 21)),
    Sum.inr (Sum.inl (128, 42)),
    Sum.inr (Sum.inl (133, 4)),
    Sum.inr (Sum.inl (126, 52)),
    Sum.inr (Sum.inl (132, 43)),
    Sum.inr (Sum.inl (6, 41)),
    Sum.inr (Sum.inl (6, 25)),
    Sum.inr (Sum.inl (26, 39)),
    Sum.inr (Sum.inl (6, 57)),
    Sum.inr (Sum.inl (128, 58)),
    Sum.inr (Sum.inl (126, 21)),
    Sum.inr (Sum.inl (132, 10)),
    Sum.inr (Sum.inl (133, 43)),
    Sum.inr (Sum.inl (210, 50)),
    Sum.inr (Sum.inl (204, 23)),
    Sum.inr (Sum.inl (147, 37)),
    Sum.inr (Sum.inl (170, 5)),
    Sum.inr (Sum.inl (35, 21)),
    Sum.inr (Sum.inl (15, 55)),
    Sum.inr (Sum.inl (35, 29)),
    Sum.inr (Sum.inl (35, 17)),
    Sum.inr (Sum.inl (210, 29)),
    Sum.inr (Sum.inl (147, 55)),
    Sum.inr (Sum.inl (170, 21)),
    Sum.inr (Sum.inl (204, 53)),
    Sum.inr (Sum.inl (170, 23)),
    Sum.inr (Sum.inl (210, 9)),
    Sum.inr (Sum.inl (147, 53)),
    Sum.inr (Sum.inl (204, 42)),
    Sum.inr (Sum.inl (15, 23)),
    Sum.inr (Sum.inl (15, 39)),
    Sum.inr (Sum.inl (35, 25)),
    Sum.inr (Sum.inl (15, 7)),
    Sum.inr (Sum.inl (170, 7)),
    Sum.inr (Sum.inl (147, 39)),
    Sum.inr (Sum.inl (204, 8)),
    Sum.inr (Sum.inl (210, 38)),
    Sum.inr (Sum.inl (71, 1)),
    Sum.inr (Sum.inl (70, 31)),
    Sum.inr (Sum.inl (64, 62)),
    Sum.inr (Sum.inl (66, 39)),
    Sum.inr (Sum.inl (22, 61)),
    Sum.inr (Sum.inl (2, 15)),
    Sum.inr (Sum.inl (22, 55)),
    Sum.inr (Sum.inl (22, 53)),
    Sum.inr (Sum.inl (71, 16)),
    Sum.inr (Sum.inl (64, 30)),
    Sum.inr (Sum.inl (66, 55)),
    Sum.inr (Sum.inl (70, 62)),
    Sum.inr (Sum.inl (66, 47)),
    Sum.inr (Sum.inl (71, 46)),
    Sum.inr (Sum.inl (64, 31)),
    Sum.inr (Sum.inl (70, 33)),
    Sum.inr (Sum.inl (2, 47)),
    Sum.inr (Sum.inl (2, 31)),
    Sum.inr (Sum.inl (22, 63)),
    Sum.inr (Sum.inl (2, 63)),
    Sum.inr (Sum.inl (66, 63)),
    Sum.inr (Sum.inl (64, 63)),
    Sum.inr (Sum.inl (70, 0)),
    Sum.inr (Sum.inl (71, 63))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock074Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨18944 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock074InputMaskData : ℕ :=
  sixthHex% [
    "ceb2a0f8b2a0e3b2a095b2a0f272a0ec72a0cb72a09572a0ea1aa0c012a0",
    "ff1aa09512a0d62aa0d422a0d72aa09522a0d93aa0d132a0dd3aa09532a0",
    "a5caa085c2a0b5caa0d5c2a0d8ea7feee27ff5e27f83ea7fe42a7ffa2a7f",
    "dd2a7f832a7ffc4a7fd64a7fe94a7f834a7fc07a7fc2727fc1727f837a7f",
    "cf6a7fc76a7fcb627f83627fb39a7f93927fa39a7fc3927f8b027ebd0a7e",
    "a60a7ed0027eb7c27ea9c27e8ec27ed0c27eafa27e85a27ebaa27ed0a27e",
    "939a7e91927e92927ed09a7e9c827e94827e988a7ed08a7ee07a7ec0727e",
    "f07a7e90727e883a7dbe327da5327dd33a7db4fa7daafa7d8dfa7dd3fa7d",
    "ac927d86927db9927dd3927d90aa7d92a27d91a27dd3aa7d9fba7d97ba7d",
    "9bb27dd3b27de3427dc34a7df3427d934a7d9bd27cadda7cb6da7cc0d27c",
    "a7127cb9127c9e127cc0127cbf7a7c957a7caa7a7cc07a7c834a7c81427c",
    "82427cc04a7c8c527c84527c885a7cc05a7cf0a27cd0aa7ce0a27c80aa7c",
    "885a7bbe527ba5527bd35a7bb4927baa927b8d927bd3927bacfa7b86fa7b",
    "b9fa7bd3fa7b90ca7b92c27b91c27bd3ca7b9fda7b97da7b9bd27bd3d27b",
    "e3227bc32a7bf3227b932a7b9bb27aadba7ab6ba7ac0b27aa77a7ab97a7a",
    "9e7a7ac07a7abf127a95127aaa127ac0127a832a7a81227a82227ac02a7a",
    "8c327a84327a883a7ac03a7af0c27ad0ca7ae0c27a80ca7a988a79ae8279",
    "b58279c38a79a44279ba42799d4279c34279bc2279962279a92279c32279",
    "801a79821279811279c31a798f0a79870a798b0279c30279f3fa79d3f279",
    "e3fa7983f279cb6278fd6a78e66a78906278f7aa78e9aa78ceaa7890aa78",
    "efca78c5ca78faca7890ca78d3fa78d1f278d2f27890fa78dce278d4e278",
    "d8ea7890ea78a01a78801278b01a78d01278939a77a59277be9277c89a77",
    "af5277b15277965277c85277b732779d3277a23277c832778b0277890a77",
    "8a0a77c802778412778c1277801a77c81a77f8ea77d8e277e8ea7788e277",
    "807276b67a76ad7a76db7276bcba76a2ba7685ba76dbba76a4da768eda76",
    "b1da76dbda7698e2769aea7699ea76dbe276"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock074InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock074InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock074OutputMaskData : ℕ :=
  sixthHex% [
    "72839155c2a05859800a18ba64cfd44fcfdf5dcfd403cfd4362aa07bf980",
    "326b910ab8ba0a1aa04b88ba1d81802913910bc7df728fdf3ac7d4368fdf",
    "4b20ba3e298069faa069f39109106e5f115f528a7f718b451f5c2b345c20",
    "265c2b785c2b3cf95f006a7f38b86e712b4500c95f415b4566127f52806e",
    "011420091c2041542b3c5c2041f34534fa7f63295f63206e3e8b4f688a7e",
    "65115e46106428c70a03c70111c70a4fc70a0b627e37f15e0f234f46b064",
    "46127e07806420c95e145b4f368f013e870176cf0a0bc70107286472215e",
    "25f27e25fb4f4082761683471b186738195d56ce337dce386fce3331ce33",
    "042b4738b867006a7649f95d495b4708c95d2f80671b1276488638408e38",
    "08c63375ce3879215d0c28675bfb475bf27602195c54186d59834d7a8277",
    "1455193f55122d551973551946b06d7a234d42f15c0b62777a806d3b1277",
    "1c5b4d28c95c0a1d120215124a5d193755124afa773ff34d68206d68295c",
    "c075af96749e9befbeb8ee84a779ea8c79e19e79eac079eaf59c9ec90fbe",
    "f1ddafb84e84c9ac9e883e84af77be9be5afc871e1c079e18831eaf539e1",
    "f9d6848cdfbedb0c9edb05af82ee85d4efb4d97494fa75aee5e2c0cee2cb",
    "dce2c082e2c0b707b48b9494b34685fad5aefa77b4bbe5ae9cac94a83e85",
    "8aeacb82e2cbcaaac0b7a2cbca0daebf0494e8d7b4e8de85fce7bcaae68d",
    "a77dad847c979bebf9b0ebf2a2ebf9fcebf9b84e8d84ddadbc0fbcf59c97",
    "f53e8db4ac9793e5ada777bcf4e3f2fcebf2b4a3f9c9abf2b40497c10dad",
    "96de8d96d7bccb7c9d9d7dac90e68cb3e7b6ac70d88770d39570d8cb70d8",
    "8fd5acb3468c8b949dc207b6b3e5acf277b6d53e8ce1ac9dc378d3cb70d3",
    "8338d8fe30d3f2dfb687d68cd005acd00c9d4a195c1c186d11834d328277",
    "2d15190615121415194a15190eb06d32234d0af15c43627732806d731277",
    "545b4d60c95c335d123b5512731d190e151202fa7777f34d20206d20295c",
    "0882765e834753186770195d6f8e33448e38568e33088e334c2b4770b867",
    "486a7601f95d015b4740c95d678067531276"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock074OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock074OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock074InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock074InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock074InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock074OutputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f7e17e16df8e37e185f8617df",
    "86186185f85f7e185f6df8e37df8617e17e186186185f7e17e17e16df8e3",
    "85f7e18617df8618617e17e185f7e196175d7df86185f85f7df7df85f7e1",
    "7df7e16e18e37e17df86185f7e18618617e17df85f6e18e37df7e17e1861",
    "7e186186185f7df7e16e18e385f86186185f7e18617df85f7df85f6e18e3",
    "86185f7e18617e18617df7e185f7e196175d7df86185f85f7df7df85f7e1",
    "7e17e16df8e385f7e18617df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock074OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock074OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block074_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock074Input a) =
      generatedSixthXiShortBlock074InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock074Output a) =
      generatedSixthXiShortBlock074OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock074Input a) =
      generatedSixthXiShortBlock074InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock074Output a) =
      generatedSixthXiShortBlock074OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block074_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock074InputMask a) =
      generatedSixthXiShortBlock074OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock074InputMask a)) *
      generatedSixthXiShortBlock074InputNumerator a =
        generatedSixthXiShortBlock074OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block074_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock074Input a
    let y := generatedSixthXiShortBlock074Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block074_cache a
  have hs := generatedSixth_xi_short_block074_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block074_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock074Input a
    let y := generatedSixthXiShortBlock074Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block074_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block074_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock074Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block074_certificate a).1
    (generatedSixth_xi_short_block074_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
