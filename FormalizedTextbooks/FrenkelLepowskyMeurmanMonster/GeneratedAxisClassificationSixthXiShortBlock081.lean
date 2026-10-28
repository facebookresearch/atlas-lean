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
def generatedSixthXiShortBlock081Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (71, 47)),
    Sum.inr (Sum.inl (70, 1)),
    Sum.inr (Sum.inl (64, 17)),
    Sum.inr (Sum.inl (66, 56)),
    Sum.inr (Sum.inl (22, 34)),
    Sum.inr (Sum.inl (2, 56)),
    Sum.inr (Sum.inl (22, 40)),
    Sum.inr (Sum.inl (22, 42)),
    Sum.inr (Sum.inl (71, 62)),
    Sum.inr (Sum.inl (64, 49)),
    Sum.inr (Sum.inl (66, 40)),
    Sum.inr (Sum.inl (70, 32)),
    Sum.inr (Sum.inl (66, 48)),
    Sum.inr (Sum.inl (71, 0)),
    Sum.inr (Sum.inl (64, 48)),
    Sum.inr (Sum.inl (70, 63)),
    Sum.inr (Sum.inl (2, 24)),
    Sum.inr (Sum.inl (2, 40)),
    Sum.inr (Sum.inl (22, 32)),
    Sum.inr (Sum.inl (2, 8)),
    Sum.inr (Sum.inl (66, 32)),
    Sum.inr (Sum.inl (64, 16)),
    Sum.inr (Sum.inl (70, 30)),
    Sum.inr (Sum.inl (71, 17)),
    Sum.inr (Sum.inl (179, 31)),
    Sum.inr (Sum.inl (178, 47)),
    Sum.inr (Sum.inl (142, 34)),
    Sum.inr (Sum.inl (165, 29)),
    Sum.inr (Sum.inl (30, 34)),
    Sum.inr (Sum.inl (10, 56)),
    Sum.inr (Sum.inl (30, 40)),
    Sum.inr (Sum.inl (30, 42)),
    Sum.inr (Sum.inl (179, 48)),
    Sum.inr (Sum.inl (142, 0)),
    Sum.inr (Sum.inl (165, 63)),
    Sum.inr (Sum.inl (178, 48)),
    Sum.inr (Sum.inl (165, 31)),
    Sum.inr (Sum.inl (179, 14)),
    Sum.inr (Sum.inl (142, 61)),
    Sum.inr (Sum.inl (178, 24)),
    Sum.inr (Sum.inl (10, 24)),
    Sum.inr (Sum.inl (10, 40)),
    Sum.inr (Sum.inl (30, 32)),
    Sum.inr (Sum.inl (10, 8)),
    Sum.inr (Sum.inl (165, 61)),
    Sum.inr (Sum.inl (142, 31)),
    Sum.inr (Sum.inl (178, 7)),
    Sum.inr (Sum.inl (179, 33)),
    Sum.inr (Sum.inl (104, 48)),
    Sum.inr (Sum.inl (103, 48)),
    Sum.inr (Sum.inl (97, 63)),
    Sum.inr (Sum.inl (99, 0)),
    Sum.inr (Sum.inl (24, 34)),
    Sum.inr (Sum.inl (4, 56)),
    Sum.inr (Sum.inl (24, 40)),
    Sum.inr (Sum.inl (24, 42)),
    Sum.inr (Sum.inl (104, 47)),
    Sum.inr (Sum.inl (97, 45)),
    Sum.inr (Sum.inl (99, 18)),
    Sum.inr (Sum.inl (103, 47)),
    Sum.inr (Sum.inl (99, 16)),
    Sum.inr (Sum.inl (104, 11)),
    Sum.inr (Sum.inl (97, 2)),
    Sum.inr (Sum.inl (103, 18)),
    Sum.inr (Sum.inl (4, 24)),
    Sum.inr (Sum.inl (4, 40)),
    Sum.inr (Sum.inl (24, 32)),
    Sum.inr (Sum.inl (4, 8)),
    Sum.inr (Sum.inl (99, 2)),
    Sum.inr (Sum.inl (97, 16)),
    Sum.inr (Sum.inl (103, 13)),
    Sum.inr (Sum.inl (104, 20)),
    Sum.inr (Sum.inr (401, 23)),
    Sum.inr (Sum.inr (464, 15)),
    Sum.inr (Sum.inr (272, 2)),
    Sum.inr (Sum.inr (346, 10)),
    Sum.inr (Sum.inr (143, 6)),
    Sum.inr (Sum.inr (132, 5)),
    Sum.inr (Sum.inr (143, 4)),
    Sum.inr (Sum.inr (143, 18)),
    Sum.inr (Sum.inr (401, 13)),
    Sum.inr (Sum.inr (272, 9)),
    Sum.inr (Sum.inr (346, 3)),
    Sum.inr (Sum.inr (464, 22)),
    Sum.inr (Sum.inr (346, 20)),
    Sum.inr (Sum.inr (401, 8)),
    Sum.inr (Sum.inr (272, 14)),
    Sum.inr (Sum.inr (464, 1)),
    Sum.inr (Sum.inr (132, 16)),
    Sum.inr (Sum.inr (132, 17)),
    Sum.inr (Sum.inr (143, 7)),
    Sum.inr (Sum.inr (132, 19)),
    Sum.inr (Sum.inr (346, 12)),
    Sum.inr (Sum.inr (272, 21)),
    Sum.inr (Sum.inr (464, 11)),
    Sum.inr (Sum.inr (401, 0)),
    Sum.inr (Sum.inr (474, 13)),
    Sum.inr (Sum.inr (411, 22)),
    Sum.inr (Sum.inr (347, 9)),
    Sum.inr (Sum.inr (273, 3)),
    Sum.inr (Sum.inr (196, 6)),
    Sum.inr (Sum.inr (207, 5)),
    Sum.inr (Sum.inr (196, 4)),
    Sum.inr (Sum.inr (196, 18)),
    Sum.inr (Sum.inr (474, 23)),
    Sum.inr (Sum.inr (347, 2)),
    Sum.inr (Sum.inr (273, 10)),
    Sum.inr (Sum.inr (411, 15)),
    Sum.inr (Sum.inr (273, 12)),
    Sum.inr (Sum.inr (474, 0)),
    Sum.inr (Sum.inr (347, 21)),
    Sum.inr (Sum.inr (411, 11)),
    Sum.inr (Sum.inr (207, 16)),
    Sum.inr (Sum.inr (207, 17)),
    Sum.inr (Sum.inr (196, 7)),
    Sum.inr (Sum.inr (207, 19)),
    Sum.inr (Sum.inr (273, 20)),
    Sum.inr (Sum.inr (347, 14)),
    Sum.inr (Sum.inr (411, 1)),
    Sum.inr (Sum.inr (474, 8)),
    Sum.inr (Sum.inr (339, 8)),
    Sum.inr (Sum.inr (274, 1)),
    Sum.inr (Sum.inr (466, 14)),
    Sum.inr (Sum.inr (408, 20)),
    Sum.inr (Sum.inr (77, 6)),
    Sum.inr (Sum.inr (70, 5)),
    Sum.inr (Sum.inr (77, 4)),
    Sum.inr (Sum.inr (77, 18)),
    Sum.inr (Sum.inr (339, 0)),
    Sum.inr (Sum.inr (466, 21)),
    Sum.inr (Sum.inr (408, 12)),
    Sum.inr (Sum.inr (274, 11)),
    Sum.inr (Sum.inr (408, 10)),
    Sum.inr (Sum.inr (339, 23)),
    Sum.inr (Sum.inr (466, 2)),
    Sum.inr (Sum.inr (274, 15)),
    Sum.inr (Sum.inr (70, 16)),
    Sum.inr (Sum.inr (70, 17)),
    Sum.inr (Sum.inr (77, 7)),
    Sum.inr (Sum.inr (70, 19)),
    Sum.inr (Sum.inr (408, 3)),
    Sum.inr (Sum.inr (466, 9)),
    Sum.inr (Sum.inr (274, 22)),
    Sum.inr (Sum.inr (339, 13)),
    Sum.inr (Sum.inr (275, 0)),
    Sum.inr (Sum.inr (338, 11)),
    Sum.inr (Sum.inr (402, 21)),
    Sum.inr (Sum.inr (472, 12)),
    Sum.inr (Sum.inr (13, 6)),
    Sum.inr (Sum.inr (6, 5)),
    Sum.inr (Sum.inr (13, 4)),
    Sum.inr (Sum.inr (13, 18)),
    Sum.inr (Sum.inr (275, 8)),
    Sum.inr (Sum.inr (402, 14)),
    Sum.inr (Sum.inr (472, 20)),
    Sum.inr (Sum.inr (338, 1)),
    Sum.inr (Sum.inr (472, 3)),
    Sum.inr (Sum.inr (275, 13)),
    Sum.inr (Sum.inr (402, 9)),
    Sum.inr (Sum.inr (338, 22)),
    Sum.inr (Sum.inr (6, 16)),
    Sum.inr (Sum.inr (6, 17)),
    Sum.inr (Sum.inr (13, 7)),
    Sum.inr (Sum.inr (6, 19)),
    Sum.inr (Sum.inr (472, 10)),
    Sum.inr (Sum.inr (402, 2)),
    Sum.inr (Sum.inr (338, 15)),
    Sum.inr (Sum.inr (275, 23)),
    Sum.inr (Sum.inl (104, 51)),
    Sum.inr (Sum.inl (103, 60)),
    Sum.inr (Sum.inl (97, 51)),
    Sum.inr (Sum.inl (99, 12)),
    Sum.inr (Sum.inl (24, 44)),
    Sum.inr (Sum.inl (4, 10)),
    Sum.inr (Sum.inl (24, 38)),
    Sum.inr (Sum.inl (24, 36)),
    Sum.inr (Sum.inl (104, 44)),
    Sum.inr (Sum.inl (97, 33)),
    Sum.inr (Sum.inl (99, 30)),
    Sum.inr (Sum.inl (103, 35)),
    Sum.inr (Sum.inl (99, 28)),
    Sum.inr (Sum.inl (104, 8)),
    Sum.inr (Sum.inl (97, 14)),
    Sum.inr (Sum.inl (103, 30)),
    Sum.inr (Sum.inl (4, 42)),
    Sum.inr (Sum.inl (4, 26)),
    Sum.inr (Sum.inl (24, 46)),
    Sum.inr (Sum.inl (4, 58)),
    Sum.inr (Sum.inl (99, 14)),
    Sum.inr (Sum.inl (97, 28)),
    Sum.inr (Sum.inl (103, 1)),
    Sum.inr (Sum.inl (104, 23)),
    Sum.inr (Sum.inl (179, 19)),
    Sum.inr (Sum.inl (178, 44)),
    Sum.inr (Sum.inl (142, 46)),
    Sum.inr (Sum.inl (165, 17)),
    Sum.inr (Sum.inl (30, 44)),
    Sum.inr (Sum.inl (10, 10)),
    Sum.inr (Sum.inl (30, 38)),
    Sum.inr (Sum.inl (30, 36)),
    Sum.inr (Sum.inl (179, 60)),
    Sum.inr (Sum.inl (142, 12)),
    Sum.inr (Sum.inl (165, 51)),
    Sum.inr (Sum.inl (178, 51)),
    Sum.inr (Sum.inl (165, 19)),
    Sum.inr (Sum.inl (179, 2)),
    Sum.inr (Sum.inl (142, 49)),
    Sum.inr (Sum.inl (178, 27)),
    Sum.inr (Sum.inl (10, 42)),
    Sum.inr (Sum.inl (10, 26)),
    Sum.inr (Sum.inl (30, 46)),
    Sum.inr (Sum.inl (10, 58)),
    Sum.inr (Sum.inl (165, 49)),
    Sum.inr (Sum.inl (142, 19)),
    Sum.inr (Sum.inl (178, 4)),
    Sum.inr (Sum.inl (179, 45)),
    Sum.inr (Sum.inl (71, 35)),
    Sum.inr (Sum.inl (70, 13)),
    Sum.inr (Sum.inl (64, 29)),
    Sum.inr (Sum.inl (66, 59)),
    Sum.inr (Sum.inl (22, 44)),
    Sum.inr (Sum.inl (2, 10)),
    Sum.inr (Sum.inl (22, 38)),
    Sum.inr (Sum.inl (22, 36)),
    Sum.inr (Sum.inl (71, 50)),
    Sum.inr (Sum.inl (64, 61)),
    Sum.inr (Sum.inl (66, 43)),
    Sum.inr (Sum.inl (70, 44)),
    Sum.inr (Sum.inl (66, 51)),
    Sum.inr (Sum.inl (71, 12)),
    Sum.inr (Sum.inl (64, 60)),
    Sum.inr (Sum.inl (70, 51)),
    Sum.inr (Sum.inl (2, 42)),
    Sum.inr (Sum.inl (2, 26)),
    Sum.inr (Sum.inl (22, 46)),
    Sum.inr (Sum.inl (2, 58)),
    Sum.inr (Sum.inl (66, 35)),
    Sum.inr (Sum.inl (64, 28)),
    Sum.inr (Sum.inl (70, 18)),
    Sum.inr (Sum.inl (71, 29)),
    Sum.inr (Sum.inl (215, 47)),
    Sum.inr (Sum.inl (209, 1)),
    Sum.inr (Sum.inl (152, 36)),
    Sum.inr (Sum.inl (175, 50)),
    Sum.inr (Sum.inl (40, 34)),
    Sum.inr (Sum.inl (20, 56)),
    Sum.inr (Sum.inl (40, 40)),
    Sum.inr (Sum.inl (40, 42)),
    Sum.inr (Sum.inl (215, 62)),
    Sum.inr (Sum.inl (152, 52)),
    Sum.inr (Sum.inl (175, 34)),
    Sum.inr (Sum.inl (209, 32)),
    Sum.inr (Sum.inl (175, 32)),
    Sum.inr (Sum.inl (215, 46)),
    Sum.inr (Sum.inl (152, 32)),
    Sum.inr (Sum.inl (209, 33))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock081Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨20736 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock081InputMaskData : ℕ :=
  sixthHex% [
    "8dfb9ba7fb9b98fb9bf2fb9bb1c39bb3c39bb0cb9bf2cb9bbedb9bb6d39b",
    "badb9bf2d39bc22b9be2239bd2239bb22b9b9bbb9aadbb9ab6b39ac0b39a",
    "a77b9ab97b9a9e7b9ac07b9abf139a95139aaa139ac0139a83239a81239a",
    "822b9ac02b9a8c339a843b9a88339ac03b9af0cb9ad0c39ae0c39a80cb9a",
    "998399af8399b48b99c28b99a54399bb43999c4399c24399bd2399972399",
    "a82399c22399811399831399801b99c21b998e0b998603998a0b99c20399",
    "f2f399d2fb99e2fb9982f399eb6b98dd6b98c66398b06398d7ab98c9ab98",
    "eeab98b0ab98cfcb98e5cb98dacb98b0cb98f3f398f1f398f2fb98b0fb98",
    "fce398f4eb98f8e398b0eb98801398a01b98901b98f013989f9397a99397",
    "b29b97c49b97a35397bd53979a5397c45397bb3397913397ae3397c43397",
    "870b97850b97860397c40397881397801b978c1397c41b97f4e397d4eb97",
    "e4eb9784e397ad7b969b7b96807396f6739691bb968fbb96a8bb96f6bb96",
    "89db96a3db969cdb96f6db96b5eb96b7eb96b4e396f6e396bafb96b2f396",
    "befb96f6f396c60396e60b96d60b96b60396af4395994395824b95f44b95",
    "9383958d8395aa8395f483958beb95a1eb959eeb95f4eb95b7db95b5db95",
    "b6d395f4d395b8c395b0cb95bcc395f4cb95c43b95e43395d43395b43b95",
    "ddab94ebab94f0a39486a394e16b94ff6b94d86b94866b94f90394d30394",
    "ec0394860394c53b94c73b94c43394863394ca2b94c22394ce2b94862394",
    "b6db9496d394a6d394c6db94af2393992393822b93f42b9393eb938deb93",
    "aaeb93f4eb938b8393a183939e8393f48393b7bb93b5bb93b6b393f4b393",
    "b8a393b0ab93bca393f4ab93c45b93e45393d45393b45b93ddcb92ebcb92",
    "f0c39286c392e10392ff0392d80392860392f96b92d36b92ec6b92866b92",
    "c55b92c75b92c45392865392ca4b92c24392ce4b92864392b6bb9296b392",
    "a6b392c6bb92dff391e9f391f2fb9184fb91e33b91fd3b91da3b91843b91",
    "fb5b91d15b91ee5b91845b91c76b91c56b91c66391846391c87391c07b91",
    "cc7391847b91b48391948b91a48b91c48391"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock081InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock081InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock081OutputMaskData : ℕ :=
  sixthHex% [
    "158b902918b011caa158598a58fb9068298a3e20b07bf2a12866ef512eef",
    "1966e4152eef68818a1d88b03b1b903b12a1006b91272aa05bf18009b0ba",
    "1627d43d27df2f27d47127d444c2a07851804083910910ba78f2a04820ba",
    "1e29805bfb91792fdf0067df482fd44467df4888ba3d81801b12a01b1b91",
    "69f9884eb8b93263996022a37fb5cd54b5c646b5cd18b5cd5c10b9608399",
    "58518811c2a36020b950f2a306fb9943298810bdc669f5c621bdcd2df5c6",
    "211aa35413997280b97289884db0b36af182162aa2446b985bfcf670fcfd",
    "62fcf63cfcf678598244caa27c18b3358b9835298205fb9853f2a21620b3",
    "34f4fd4dbcfd05f4f609bcfd741398011aa22789822780b3f19443d6d572",
    "aa0e52f84f68e7d806ccd80dded80680d806c47d72f8ee52c03c4389af68",
    "890d72b9df68efd652aa0443f9900d80d80dc89006c4d80db97768cc7e52",
    "eaed72eae443a0dd73879c42fb4762a90658b691369d913d8f9136d19136",
    "953442a9a762917573d8e658a9044299d658cfdf628a0d73a8d93dd1913d",
    "99d93695913d997e58ec7762cae442caed73c94f6aee0e5b92d57bc09441",
    "df032ff40324e6032fb8032f8de65bb1757b89a76ac03441b1d65b810441",
    "d70d7b92df6ac14b24b80324f04b2ffc0324f0ec4185e57ba3765ba37f6a",
    "ed0651ca4760b69c40e4dd7afb4a14d04a1fc24a149c4a14a9af60953c40",
    "adee51e47d7ae4df60d40d7a820440c7d651e5021f9c4a1fd40214d84a1f",
    "a5e57ad0ec40f67f60f6765149b8b36ef9821222a24063982eb4f605b4fd",
    "17b4f649b4f67c518240c2a27810b331839831218201f39857faa21228b3",
    "41bcfd38f4fd70bcf67cf4fd701b980512a22381822388b36df1884ab0b9",
    "366b99642aa30afdcd21fdc633fdcd6dfdcd5818b9648b995c598815caa3",
    "6428b954faa302f39947218865f5c61cbdc654f5cd58bdc62512a3501b99",
    "7688b97681880463912322a05ff9800db8ba636fd4486fdf5a6fd4046fd4",
    "40caa07c5980448b910d18ba7cfaa04c28ba1a21805ff3910c67df752fdf",
    "3d67d4312fdf4c80ba3989801f1aa01f1391"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock081OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock081OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock081InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock081InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock081InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock081OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df8618617e185f85f85f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df8616df8e37df8618618617e185f7e17e186186196175d85f7e185f7e1",
    "85f7e185f7e185f86195f75d85f86185f8617df7e186185f7e18616e18e3",
    "7df7e18617e186185f7df85f85f86195f75d7e17df85f8617df7e17df7e1",
    "7e18616e18e386185f8617e186185f8617e17df7df6df8e37e185f7e185f",
    "7e185f7e185f8617df96175d8617df7df7df85f7e185f85f86186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock081OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock081OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block081_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock081Input a) =
      generatedSixthXiShortBlock081InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock081Output a) =
      generatedSixthXiShortBlock081OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock081Input a) =
      generatedSixthXiShortBlock081InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock081Output a) =
      generatedSixthXiShortBlock081OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block081_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock081InputMask a) =
      generatedSixthXiShortBlock081OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock081InputMask a)) *
      generatedSixthXiShortBlock081InputNumerator a =
        generatedSixthXiShortBlock081OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block081_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock081Input a
    let y := generatedSixthXiShortBlock081Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block081_cache a
  have hs := generatedSixth_xi_short_block081_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block081_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock081Input a
    let y := generatedSixthXiShortBlock081Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block081_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block081_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock081Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block081_certificate a).1
    (generatedSixth_xi_short_block081_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
