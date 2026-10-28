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
def generatedSixthXiShortBlock082Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (20, 24)),
    Sum.inr (Sum.inl (20, 40)),
    Sum.inr (Sum.inl (40, 32)),
    Sum.inr (Sum.inl (20, 8)),
    Sum.inr (Sum.inl (175, 48)),
    Sum.inr (Sum.inl (152, 48)),
    Sum.inr (Sum.inl (209, 0)),
    Sum.inr (Sum.inl (215, 63)),
    Sum.inr (Sum.inr (280, 0)),
    Sum.inr (Sum.inr (345, 11)),
    Sum.inr (Sum.inr (409, 21)),
    Sum.inr (Sum.inr (467, 12)),
    Sum.inr (Sum.inr (6, 6)),
    Sum.inr (Sum.inr (13, 5)),
    Sum.inr (Sum.inr (6, 4)),
    Sum.inr (Sum.inr (6, 18)),
    Sum.inr (Sum.inr (280, 8)),
    Sum.inr (Sum.inr (409, 14)),
    Sum.inr (Sum.inr (467, 20)),
    Sum.inr (Sum.inr (345, 1)),
    Sum.inr (Sum.inr (467, 3)),
    Sum.inr (Sum.inr (280, 13)),
    Sum.inr (Sum.inr (409, 9)),
    Sum.inr (Sum.inr (345, 22)),
    Sum.inr (Sum.inr (13, 16)),
    Sum.inr (Sum.inr (13, 17)),
    Sum.inr (Sum.inr (6, 7)),
    Sum.inr (Sum.inr (13, 19)),
    Sum.inr (Sum.inr (467, 10)),
    Sum.inr (Sum.inr (409, 2)),
    Sum.inr (Sum.inr (345, 15)),
    Sum.inr (Sum.inr (280, 23)),
    Sum.inr (Sum.inr (344, 8)),
    Sum.inr (Sum.inr (281, 1)),
    Sum.inr (Sum.inr (473, 14)),
    Sum.inr (Sum.inr (403, 20)),
    Sum.inr (Sum.inr (70, 6)),
    Sum.inr (Sum.inr (77, 5)),
    Sum.inr (Sum.inr (70, 4)),
    Sum.inr (Sum.inr (70, 18)),
    Sum.inr (Sum.inr (344, 0)),
    Sum.inr (Sum.inr (473, 21)),
    Sum.inr (Sum.inr (403, 12)),
    Sum.inr (Sum.inr (281, 11)),
    Sum.inr (Sum.inr (403, 10)),
    Sum.inr (Sum.inr (344, 23)),
    Sum.inr (Sum.inr (473, 2)),
    Sum.inr (Sum.inr (281, 15)),
    Sum.inr (Sum.inr (77, 16)),
    Sum.inr (Sum.inr (77, 17)),
    Sum.inr (Sum.inr (70, 7)),
    Sum.inr (Sum.inr (77, 19)),
    Sum.inr (Sum.inr (403, 3)),
    Sum.inr (Sum.inr (473, 9)),
    Sum.inr (Sum.inr (281, 22)),
    Sum.inr (Sum.inr (344, 13)),
    Sum.inr (Sum.inr (465, 13)),
    Sum.inr (Sum.inr (400, 22)),
    Sum.inr (Sum.inr (336, 9)),
    Sum.inr (Sum.inr (282, 3)),
    Sum.inr (Sum.inr (207, 6)),
    Sum.inr (Sum.inr (196, 5)),
    Sum.inr (Sum.inr (207, 4)),
    Sum.inr (Sum.inr (207, 18)),
    Sum.inr (Sum.inr (465, 23)),
    Sum.inr (Sum.inr (336, 2)),
    Sum.inr (Sum.inr (282, 10)),
    Sum.inr (Sum.inr (400, 15)),
    Sum.inr (Sum.inr (282, 12)),
    Sum.inr (Sum.inr (465, 0)),
    Sum.inr (Sum.inr (336, 21)),
    Sum.inr (Sum.inr (400, 11)),
    Sum.inr (Sum.inr (196, 16)),
    Sum.inr (Sum.inr (196, 17)),
    Sum.inr (Sum.inr (207, 7)),
    Sum.inr (Sum.inr (196, 19)),
    Sum.inr (Sum.inr (282, 20)),
    Sum.inr (Sum.inr (336, 14)),
    Sum.inr (Sum.inr (400, 1)),
    Sum.inr (Sum.inr (465, 8)),
    Sum.inr (Sum.inr (410, 23)),
    Sum.inr (Sum.inr (475, 15)),
    Sum.inr (Sum.inr (283, 2)),
    Sum.inr (Sum.inr (337, 10)),
    Sum.inr (Sum.inr (132, 6)),
    Sum.inr (Sum.inr (143, 5)),
    Sum.inr (Sum.inr (132, 4)),
    Sum.inr (Sum.inr (132, 18)),
    Sum.inr (Sum.inr (410, 13)),
    Sum.inr (Sum.inr (283, 9)),
    Sum.inr (Sum.inr (337, 3)),
    Sum.inr (Sum.inr (475, 22)),
    Sum.inr (Sum.inr (337, 20)),
    Sum.inr (Sum.inr (410, 8)),
    Sum.inr (Sum.inr (283, 14)),
    Sum.inr (Sum.inr (475, 1)),
    Sum.inr (Sum.inr (143, 16)),
    Sum.inr (Sum.inr (143, 17)),
    Sum.inr (Sum.inr (132, 7)),
    Sum.inr (Sum.inr (143, 19)),
    Sum.inr (Sum.inr (337, 12)),
    Sum.inr (Sum.inr (283, 21)),
    Sum.inr (Sum.inr (475, 11)),
    Sum.inr (Sum.inr (410, 0)),
    Sum.inr (Sum.inl (119, 43)),
    Sum.inr (Sum.inl (118, 46)),
    Sum.inr (Sum.inl (112, 22)),
    Sum.inr (Sum.inl (114, 9)),
    Sum.inr (Sum.inl (25, 27)),
    Sum.inr (Sum.inl (5, 55)),
    Sum.inr (Sum.inl (25, 19)),
    Sum.inr (Sum.inl (25, 17)),
    Sum.inr (Sum.inl (119, 58)),
    Sum.inr (Sum.inl (112, 4)),
    Sum.inr (Sum.inl (114, 25)),
    Sum.inr (Sum.inl (118, 49)),
    Sum.inr (Sum.inl (114, 27)),
    Sum.inr (Sum.inl (119, 4)),
    Sum.inr (Sum.inl (112, 43)),
    Sum.inr (Sum.inl (118, 25)),
    Sum.inr (Sum.inl (5, 23)),
    Sum.inr (Sum.inl (5, 39)),
    Sum.inr (Sum.inl (25, 25)),
    Sum.inr (Sum.inl (5, 7)),
    Sum.inr (Sum.inl (114, 11)),
    Sum.inr (Sum.inl (112, 57)),
    Sum.inr (Sum.inl (118, 6)),
    Sum.inr (Sum.inl (119, 21)),
    Sum.inr (Sum.inl (53, 7)),
    Sum.inr (Sum.inl (52, 25)),
    Sum.inr (Sum.inl (46, 57)),
    Sum.inr (Sum.inl (48, 62)),
    Sum.inr (Sum.inl (21, 58)),
    Sum.inr (Sum.inl (1, 62)),
    Sum.inr (Sum.inl (21, 50)),
    Sum.inr (Sum.inl (21, 48)),
    Sum.inr (Sum.inl (53, 22)),
    Sum.inr (Sum.inl (46, 40)),
    Sum.inr (Sum.inl (48, 46)),
    Sum.inr (Sum.inl (52, 57)),
    Sum.inr (Sum.inl (48, 58)),
    Sum.inr (Sum.inl (53, 6)),
    Sum.inr (Sum.inl (46, 41)),
    Sum.inr (Sum.inl (52, 56)),
    Sum.inr (Sum.inl (1, 30)),
    Sum.inr (Sum.inl (1, 46)),
    Sum.inr (Sum.inl (21, 56)),
    Sum.inr (Sum.inl (1, 14)),
    Sum.inr (Sum.inl (48, 42)),
    Sum.inr (Sum.inl (46, 56)),
    Sum.inr (Sum.inl (52, 24)),
    Sum.inr (Sum.inl (53, 23)),
    Sum.inr (Sum.inl (158, 25)),
    Sum.inr (Sum.inl (157, 52)),
    Sum.inr (Sum.inl (140, 43)),
    Sum.inr (Sum.inl (153, 20)),
    Sum.inr (Sum.inl (28, 43)),
    Sum.inr (Sum.inl (8, 59)),
    Sum.inr (Sum.inl (28, 35)),
    Sum.inr (Sum.inl (28, 33)),
    Sum.inr (Sum.inl (158, 54)),
    Sum.inr (Sum.inl (140, 4)),
    Sum.inr (Sum.inl (153, 54)),
    Sum.inr (Sum.inl (157, 22)),
    Sum.inr (Sum.inl (153, 22)),
    Sum.inr (Sum.inl (158, 34)),
    Sum.inr (Sum.inl (140, 57)),
    Sum.inr (Sum.inl (157, 43)),
    Sum.inr (Sum.inl (8, 27)),
    Sum.inr (Sum.inl (8, 43)),
    Sum.inr (Sum.inl (28, 41)),
    Sum.inr (Sum.inl (8, 11)),
    Sum.inr (Sum.inl (153, 52)),
    Sum.inr (Sum.inl (140, 22)),
    Sum.inr (Sum.inl (157, 9)),
    Sum.inr (Sum.inl (158, 13)),
    Sum.inr (Sum.inl (213, 59)),
    Sum.inr (Sum.inl (207, 5)),
    Sum.inr (Sum.inl (150, 9)),
    Sum.inr (Sum.inl (173, 38)),
    Sum.inr (Sum.inl (38, 4)),
    Sum.inr (Sum.inl (18, 0)),
    Sum.inr (Sum.inl (38, 12)),
    Sum.inr (Sum.inl (38, 14)),
    Sum.inr (Sum.inl (213, 36)),
    Sum.inr (Sum.inl (150, 41)),
    Sum.inr (Sum.inl (173, 4)),
    Sum.inr (Sum.inl (207, 36)),
    Sum.inr (Sum.inl (173, 6)),
    Sum.inr (Sum.inl (213, 26)),
    Sum.inr (Sum.inl (150, 1)),
    Sum.inr (Sum.inl (207, 59)),
    Sum.inr (Sum.inl (18, 32)),
    Sum.inr (Sum.inl (18, 16)),
    Sum.inr (Sum.inl (38, 6)),
    Sum.inr (Sum.inl (18, 48)),
    Sum.inr (Sum.inl (173, 36)),
    Sum.inr (Sum.inl (150, 33)),
    Sum.inr (Sum.inl (207, 26)),
    Sum.inr (Sum.inl (213, 5)),
    Sum.inr (Sum.inr (321, 13)),
    Sum.inr (Sum.inr (256, 1)),
    Sum.inr (Sum.inr (448, 21)),
    Sum.inr (Sum.inr (394, 10)),
    Sum.inr (Sum.inr (95, 7)),
    Sum.inr (Sum.inr (84, 5)),
    Sum.inr (Sum.inr (95, 18)),
    Sum.inr (Sum.inr (95, 4)),
    Sum.inr (Sum.inr (321, 23)),
    Sum.inr (Sum.inr (448, 14)),
    Sum.inr (Sum.inr (394, 3)),
    Sum.inr (Sum.inr (256, 11)),
    Sum.inr (Sum.inr (394, 20)),
    Sum.inr (Sum.inr (321, 0)),
    Sum.inr (Sum.inr (448, 9)),
    Sum.inr (Sum.inr (256, 15)),
    Sum.inr (Sum.inr (84, 16)),
    Sum.inr (Sum.inr (84, 17)),
    Sum.inr (Sum.inr (95, 6)),
    Sum.inr (Sum.inr (84, 19)),
    Sum.inr (Sum.inr (394, 12)),
    Sum.inr (Sum.inr (448, 2)),
    Sum.inr (Sum.inr (256, 22)),
    Sum.inr (Sum.inr (321, 8)),
    Sum.inr (Sum.inr (458, 23)),
    Sum.inr (Sum.inr (395, 11)),
    Sum.inr (Sum.inr (331, 14)),
    Sum.inr (Sum.inr (257, 3)),
    Sum.inr (Sum.inr (212, 7)),
    Sum.inr (Sum.inr (223, 5)),
    Sum.inr (Sum.inr (212, 18)),
    Sum.inr (Sum.inr (212, 4)),
    Sum.inr (Sum.inr (458, 13)),
    Sum.inr (Sum.inr (331, 21)),
    Sum.inr (Sum.inr (257, 10)),
    Sum.inr (Sum.inr (395, 1)),
    Sum.inr (Sum.inr (257, 12)),
    Sum.inr (Sum.inr (458, 8)),
    Sum.inr (Sum.inr (331, 2)),
    Sum.inr (Sum.inr (395, 22)),
    Sum.inr (Sum.inr (223, 16)),
    Sum.inr (Sum.inr (223, 17)),
    Sum.inr (Sum.inr (212, 6)),
    Sum.inr (Sum.inr (223, 19)),
    Sum.inr (Sum.inr (257, 20)),
    Sum.inr (Sum.inr (331, 9)),
    Sum.inr (Sum.inr (395, 15)),
    Sum.inr (Sum.inr (458, 0)),
    Sum.inr (Sum.inr (258, 0)),
    Sum.inr (Sum.inr (323, 15)),
    Sum.inr (Sum.inr (387, 9)),
    Sum.inr (Sum.inr (457, 20)),
    Sum.inr (Sum.inr (28, 7)),
    Sum.inr (Sum.inr (23, 5)),
    Sum.inr (Sum.inr (28, 18)),
    Sum.inr (Sum.inr (28, 4))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock082Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨20992 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock082InputMaskData : ℕ :=
  sixthHex% [
    "8c5bf68453f68853f6c05bf6f0abf6d0a3f6e0a3f680abf6a7ebf591ebf5",
    "8aebf5fcebf59b23f58523f5a223f5fc23f5834bf5a943f59643f5fc4bf5",
    "bf73f5bd7bf5be7bf5fc73f5b06bf5b863f5b463f5fc6bf5cc9bf5ec93f5",
    "dc93f5bc9bf5d403f4e203f4f903f48f03f4e8cbf4f6cbf4d1cbf48fcbf4",
    "f0a3f4daabf4e5abf48fa3f4cc93f4ce9bf4cd9bf48f93f4c383f4cb8bf4",
    "c78bf48f83f4bf7bf49f73f4af73f4cf7bf49883f3ae83f3b583f3c383f3",
    "a443f3ba43f39d43f3c343f3bc2bf39623f3a923f3c32bf3801bf38213f3",
    "8113f3c31bf38f03f3870bf38b0bf3c303f3f3f3f3d3fbf3e3fbf383f3f3",
    "eb6bf2dd6bf2c66bf2b06bf2d7abf2c9abf2eeabf2b0abf2cfc3f2e5cbf2",
    "dacbf2b0c3f2f3fbf2f1f3f2f2f3f2b0fbf2fcebf2f4e3f2f8e3f2b0ebf2",
    "8013f2a01bf2901bf2f013f2d75bf1e15bf1fa5bf18c5bf1eb9bf1f59bf1",
    "d29bf18c9bf1f3fbf1d9f3f1e6f3f18cfbf1cfc3f1cdcbf1cecbf18cc3f1",
    "c0dbf1c8d3f1c4d3f18cdbf1bc23f19c2bf1ac2bf1cc23f1e4b3f0d2b3f0",
    "c9b3f0bfb3f0d873f0c673f0e173f0bf73f0c013f0ea1bf0d51bf0bf13f0",
    "fc23f0fe2bf0fd2bf0bf23f0f333f0fb3bf0f73bf0bf33f08fc3f0afcbf0",
    "9fcbf0ffc3f0d9e39fefe39ff4eb9f82eb9fe52b9ffb2b9fdc2b9f822b9f",
    "fd4b9fd74b9fe84b9f824b9fc1739fc3739fc07b9f827b9fce6b9fc6639f",
    "ca6b9f82639fb2939f929b9fa29b9fc2939fab0b9e9d0b9e86039ef0039e",
    "97c39e89c39eaec39ef0c39e8fa39ea5a39e9aa39ef0a39eb3939eb1939e",
    "b29b9ef09b9ebc839eb48b9eb8839ef08b9ec0739ee07b9ed07b9eb0739e",
    "a9339d9f339d843b9df23b9d95fb9d8bfb9dacfb9df2fb9d8d939da7939d",
    "98939df2939db1a39db3a39db0ab9df2ab9dbebb9db6b39dbabb9df2b39d",
    "c24b9de2439dd2439db24b9d9bdb9caddb9cb6d39cc0d39ca7139cb9139c",
    "9e139cc0139cbf7b9c957b9caa7b9cc07b9c83439c81439c824b9cc04b9c",
    "8c539c845b9c88539cc05b9cf0ab9cd0a39ce0a39c80ab9ca9539b9f539b",
    "845b9bf25b9b95939b8b939bac939bf2939b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock082InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock082InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock082OutputMaskData : ℕ :=
  sixthHex% [
    "86886cffc06cc6c867ca806cc66f09b3663395f51395fc22b9170a9e563b",
    "93cd1bc18c21de1b4ff51b44e71b4fb91b4f8cfe3bc12d1bf9ff0ac12c21",
    "c18e3b801c21a7551b93c70ab11344c85b44f1534ffd1b44f1f42184fd1b",
    "a26e3ba2670a8ac511ad8420a01f00f25e3aedc954c6c95fd4c9548ac954",
    "bf2c20f2ff00ca2d11f2fe3a831c20c28e3ae5c700d1551182c15ffb895f",
    "c28154cec95fb3663ac66f00e0fc20e0f5117072c25733f35aa8d308e9e9",
    "663e874d3e8c5f3e87013e8734dbf37908d341dac27909e908ebf34979e9",
    "6e30d35aa2c278768c013e8c383687347e8c3891e94d98d36b0bf36b02c2",
    "43a0d964e1e8697ac83b3bf255ec9c7eec976cec9c32ec9c0709e84adac8",
    "7208d94adbf24a79e80bebf22ca2c81830d94ba49732ec970be49c07ac97",
    "7a03f20f0ac82999e82990d9743bf1537ac05ee1e00ca0da6277b44977bf",
    "5b77b40577b441d2c00c01e034d3f10c00da0ca2c04d30da6a79e05eebf1",
    "7c3fbf0577bf3c7fb43037bf4d98da3891e01e02c01e0bf132e9e115a8d0",
    "1833f04a72ca24a5a40fa5af1da5a443a5a40700d04ad3f07201e14ad2ca",
    "3b30d07aa2ca5debf06979e13aedaf43a5af7aada476e5af7a0aca0f03f0",
    "2990d02999e19c0e5abb4f6bc7944b95d571fb021fd00214c2021f9c021f",
    "d8a76be4344bdce65a95757195d76ba50571f30c4bb6de5ae54a149c0214",
    "d44a1fd80214d4ed71a1e44b87776b877e5ab847619f0650e3dd70b19c4a",
    "df4b24f44b2fe64b24b84b24fcee50c07d70f8af61b13c4ac0de50f00c4a",
    "a60570e3d761c1032fb84b2ff00324fc4b2f81e44af4ed70d27e50d27761",
    "d1d578f694498a4f69d80e53b6d93d9dd9368fd93dd1d93de43c49d8af69",
    "e07d78a9ee53d80c49e8de53bed769fb0578a89136d1d93699913d95d936",
    "e876539d7f69bbec49bbe578809c48a7dd79db0659894763e7900dcc9006",
    "de900d80900db5757989e659b13448f8a763f80579c8d7639ede59db0c48",
    "f9d806809006c8d80dc49006c87f63bd76599be5799bec485122a1766390",
    "0ab8b058f98a476ee46c6eef7e6ee4206ee4"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock082OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock082OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock082InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock082InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock082InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock082OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df85f85f85f7e196175d8617df85f85f7df7df7e185f7e17e16df8e3",
    "7e185f8617df86186185f85f8617e195f75d7df7e185f7df85f7df86185f",
    "7df7e16e18e385f86186185f7e18617df85f8617e195f75d86185f85f7df",
    "85f7df7df7e186185f95f75d85f8617df7e185f7df7df85f85f7df95f75d",
    "7df7e17df85f7df7e17df85f7e17df6e18e385f8617e17df86185f86185f",
    "85f7df95f75d86185f7df85f7df7e18617e17e17df6e18e37e17df7e17df",
    "86185f7df7e17df8616df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock082OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock082OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block082_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock082Input a) =
      generatedSixthXiShortBlock082InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock082Output a) =
      generatedSixthXiShortBlock082OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock082Input a) =
      generatedSixthXiShortBlock082InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock082Output a) =
      generatedSixthXiShortBlock082OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block082_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock082InputMask a) =
      generatedSixthXiShortBlock082OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock082InputMask a)) *
      generatedSixthXiShortBlock082InputNumerator a =
        generatedSixthXiShortBlock082OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block082_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock082Input a
    let y := generatedSixthXiShortBlock082Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block082_cache a
  have hs := generatedSixth_xi_short_block082_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block082_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock082Input a
    let y := generatedSixthXiShortBlock082Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block082_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block082_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock082Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block082_certificate a).1
    (generatedSixth_xi_short_block082_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
