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
def generatedSixthXiShortBlock101Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (179, 54)),
    Sum.inr (Sum.inl (142, 5)),
    Sum.inr (Sum.inl (165, 58)),
    Sum.inr (Sum.inl (178, 38)),
    Sum.inr (Sum.inl (165, 26)),
    Sum.inr (Sum.inl (179, 8)),
    Sum.inr (Sum.inl (142, 56)),
    Sum.inr (Sum.inl (178, 14)),
    Sum.inr (Sum.inl (10, 41)),
    Sum.inr (Sum.inl (10, 25)),
    Sum.inr (Sum.inl (30, 37)),
    Sum.inr (Sum.inl (10, 57)),
    Sum.inr (Sum.inl (165, 56)),
    Sum.inr (Sum.inl (142, 26)),
    Sum.inr (Sum.inl (178, 17)),
    Sum.inr (Sum.inl (179, 39)),
    Sum.inr (Sum.inl (104, 57)),
    Sum.inr (Sum.inl (103, 41)),
    Sum.inr (Sum.inl (97, 27)),
    Sum.inr (Sum.inl (99, 36)),
    Sum.inr (Sum.inl (24, 54)),
    Sum.inr (Sum.inl (4, 12)),
    Sum.inr (Sum.inl (24, 60)),
    Sum.inr (Sum.inl (24, 62)),
    Sum.inr (Sum.inl (104, 38)),
    Sum.inr (Sum.inl (97, 9)),
    Sum.inr (Sum.inl (99, 54)),
    Sum.inr (Sum.inl (103, 54)),
    Sum.inr (Sum.inl (99, 52)),
    Sum.inr (Sum.inl (104, 2)),
    Sum.inr (Sum.inl (97, 38)),
    Sum.inr (Sum.inl (103, 11)),
    Sum.inr (Sum.inl (4, 44)),
    Sum.inr (Sum.inl (4, 28)),
    Sum.inr (Sum.inl (24, 52)),
    Sum.inr (Sum.inl (4, 60)),
    Sum.inr (Sum.inl (99, 38)),
    Sum.inr (Sum.inl (97, 52)),
    Sum.inr (Sum.inl (103, 20)),
    Sum.inr (Sum.inl (104, 29)),
    Sum.inr (Sum.inr (76, 0)),
    Sum.inr (Sum.inr (13, 11)),
    Sum.inr (Sum.inr (205, 21)),
    Sum.inr (Sum.inr (135, 12)),
    Sum.inr (Sum.inr (338, 6)),
    Sum.inr (Sum.inr (345, 5)),
    Sum.inr (Sum.inr (338, 4)),
    Sum.inr (Sum.inr (338, 18)),
    Sum.inr (Sum.inr (76, 8)),
    Sum.inr (Sum.inr (205, 14)),
    Sum.inr (Sum.inr (135, 20)),
    Sum.inr (Sum.inr (13, 1)),
    Sum.inr (Sum.inr (135, 3)),
    Sum.inr (Sum.inr (76, 13)),
    Sum.inr (Sum.inr (205, 9)),
    Sum.inr (Sum.inr (13, 22)),
    Sum.inr (Sum.inr (345, 16)),
    Sum.inr (Sum.inr (345, 17)),
    Sum.inr (Sum.inr (338, 7)),
    Sum.inr (Sum.inr (345, 19)),
    Sum.inr (Sum.inr (135, 10)),
    Sum.inr (Sum.inr (205, 2)),
    Sum.inr (Sum.inr (13, 15)),
    Sum.inr (Sum.inr (76, 23)),
    Sum.inr (Sum.inr (12, 8)),
    Sum.inr (Sum.inr (77, 1)),
    Sum.inr (Sum.inr (141, 14)),
    Sum.inr (Sum.inr (199, 20)),
    Sum.inr (Sum.inr (274, 6)),
    Sum.inr (Sum.inr (281, 5)),
    Sum.inr (Sum.inr (274, 4)),
    Sum.inr (Sum.inr (274, 18)),
    Sum.inr (Sum.inr (12, 0)),
    Sum.inr (Sum.inr (141, 21)),
    Sum.inr (Sum.inr (199, 12)),
    Sum.inr (Sum.inr (77, 11)),
    Sum.inr (Sum.inr (199, 10)),
    Sum.inr (Sum.inr (12, 23)),
    Sum.inr (Sum.inr (141, 2)),
    Sum.inr (Sum.inr (77, 15)),
    Sum.inr (Sum.inr (281, 16)),
    Sum.inr (Sum.inr (281, 17)),
    Sum.inr (Sum.inr (274, 7)),
    Sum.inr (Sum.inr (281, 19)),
    Sum.inr (Sum.inr (199, 3)),
    Sum.inr (Sum.inr (141, 9)),
    Sum.inr (Sum.inr (77, 22)),
    Sum.inr (Sum.inr (12, 13)),
    Sum.inr (Sum.inr (133, 13)),
    Sum.inr (Sum.inr (196, 22)),
    Sum.inr (Sum.inr (4, 9)),
    Sum.inr (Sum.inr (78, 3)),
    Sum.inr (Sum.inr (411, 6)),
    Sum.inr (Sum.inr (400, 5)),
    Sum.inr (Sum.inr (411, 4)),
    Sum.inr (Sum.inr (411, 18)),
    Sum.inr (Sum.inr (133, 23)),
    Sum.inr (Sum.inr (4, 2)),
    Sum.inr (Sum.inr (78, 10)),
    Sum.inr (Sum.inr (196, 15)),
    Sum.inr (Sum.inr (78, 12)),
    Sum.inr (Sum.inr (133, 0)),
    Sum.inr (Sum.inr (4, 21)),
    Sum.inr (Sum.inr (196, 11)),
    Sum.inr (Sum.inr (400, 16)),
    Sum.inr (Sum.inr (400, 17)),
    Sum.inr (Sum.inr (411, 7)),
    Sum.inr (Sum.inr (400, 19)),
    Sum.inr (Sum.inr (78, 20)),
    Sum.inr (Sum.inr (4, 14)),
    Sum.inr (Sum.inr (196, 1)),
    Sum.inr (Sum.inr (133, 8)),
    Sum.inr (Sum.inr (206, 23)),
    Sum.inr (Sum.inr (143, 15)),
    Sum.inr (Sum.inr (79, 2)),
    Sum.inr (Sum.inr (5, 10)),
    Sum.inr (Sum.inr (464, 6)),
    Sum.inr (Sum.inr (475, 5)),
    Sum.inr (Sum.inr (464, 4)),
    Sum.inr (Sum.inr (464, 18)),
    Sum.inr (Sum.inr (206, 13)),
    Sum.inr (Sum.inr (79, 9)),
    Sum.inr (Sum.inr (5, 3)),
    Sum.inr (Sum.inr (143, 22)),
    Sum.inr (Sum.inr (5, 20)),
    Sum.inr (Sum.inr (206, 8)),
    Sum.inr (Sum.inr (79, 14)),
    Sum.inr (Sum.inr (143, 1)),
    Sum.inr (Sum.inr (475, 16)),
    Sum.inr (Sum.inr (475, 17)),
    Sum.inr (Sum.inr (464, 7)),
    Sum.inr (Sum.inr (475, 19)),
    Sum.inr (Sum.inr (5, 12)),
    Sum.inr (Sum.inr (79, 21)),
    Sum.inr (Sum.inr (143, 11)),
    Sum.inr (Sum.inr (206, 0)),
    Sum.inr (Sum.inl (104, 58)),
    Sum.inr (Sum.inl (103, 37)),
    Sum.inr (Sum.inl (97, 23)),
    Sum.inr (Sum.inl (99, 40)),
    Sum.inr (Sum.inl (24, 56)),
    Sum.inr (Sum.inl (4, 62)),
    Sum.inr (Sum.inl (24, 50)),
    Sum.inr (Sum.inl (24, 48)),
    Sum.inr (Sum.inl (104, 37)),
    Sum.inr (Sum.inl (97, 5)),
    Sum.inr (Sum.inl (99, 58)),
    Sum.inr (Sum.inl (103, 58)),
    Sum.inr (Sum.inl (99, 56)),
    Sum.inr (Sum.inl (104, 1)),
    Sum.inr (Sum.inl (97, 42)),
    Sum.inr (Sum.inl (103, 7)),
    Sum.inr (Sum.inl (4, 30)),
    Sum.inr (Sum.inl (4, 46)),
    Sum.inr (Sum.inl (24, 58)),
    Sum.inr (Sum.inl (4, 14)),
    Sum.inr (Sum.inl (99, 42)),
    Sum.inr (Sum.inl (97, 56)),
    Sum.inr (Sum.inl (103, 24)),
    Sum.inr (Sum.inl (104, 30)),
    Sum.inr (Sum.inl (179, 21)),
    Sum.inr (Sum.inl (178, 58)),
    Sum.inr (Sum.inl (142, 43)),
    Sum.inr (Sum.inl (165, 20)),
    Sum.inr (Sum.inl (30, 41)),
    Sum.inr (Sum.inl (10, 59)),
    Sum.inr (Sum.inl (30, 35)),
    Sum.inr (Sum.inl (30, 33)),
    Sum.inr (Sum.inl (179, 58)),
    Sum.inr (Sum.inl (142, 9)),
    Sum.inr (Sum.inl (165, 54)),
    Sum.inr (Sum.inl (178, 37)),
    Sum.inr (Sum.inl (165, 22)),
    Sum.inr (Sum.inl (179, 4)),
    Sum.inr (Sum.inl (142, 52)),
    Sum.inr (Sum.inl (178, 13)),
    Sum.inr (Sum.inl (10, 27)),
    Sum.inr (Sum.inl (10, 43)),
    Sum.inr (Sum.inl (30, 43)),
    Sum.inr (Sum.inl (10, 11)),
    Sum.inr (Sum.inl (165, 52)),
    Sum.inr (Sum.inl (142, 22)),
    Sum.inr (Sum.inl (178, 18)),
    Sum.inr (Sum.inl (179, 43)),
    Sum.inr (Sum.inl (71, 39)),
    Sum.inr (Sum.inl (70, 23)),
    Sum.inr (Sum.inl (64, 38)),
    Sum.inr (Sum.inl (66, 5)),
    Sum.inr (Sum.inl (22, 23)),
    Sum.inr (Sum.inl (2, 5)),
    Sum.inr (Sum.inl (22, 29)),
    Sum.inr (Sum.inl (22, 31)),
    Sum.inr (Sum.inl (71, 54)),
    Sum.inr (Sum.inl (64, 6)),
    Sum.inr (Sum.inl (66, 21)),
    Sum.inr (Sum.inl (70, 54)),
    Sum.inr (Sum.inl (66, 13)),
    Sum.inr (Sum.inl (71, 8)),
    Sum.inr (Sum.inl (64, 7)),
    Sum.inr (Sum.inl (70, 41)),
    Sum.inr (Sum.inl (2, 37)),
    Sum.inr (Sum.inl (2, 21)),
    Sum.inr (Sum.inl (22, 21)),
    Sum.inr (Sum.inl (2, 53)),
    Sum.inr (Sum.inl (66, 29)),
    Sum.inr (Sum.inl (64, 39)),
    Sum.inr (Sum.inl (70, 8)),
    Sum.inr (Sum.inl (71, 25)),
    Sum.inr (Sum.inl (215, 20)),
    Sum.inr (Sum.inl (209, 36)),
    Sum.inr (Sum.inl (152, 5)),
    Sum.inr (Sum.inl (175, 22)),
    Sum.inr (Sum.inl (40, 6)),
    Sum.inr (Sum.inl (20, 0)),
    Sum.inr (Sum.inl (40, 12)),
    Sum.inr (Sum.inl (40, 14)),
    Sum.inr (Sum.inl (215, 5)),
    Sum.inr (Sum.inl (152, 21)),
    Sum.inr (Sum.inl (175, 6)),
    Sum.inr (Sum.inl (209, 5)),
    Sum.inr (Sum.inl (175, 4)),
    Sum.inr (Sum.inl (215, 21)),
    Sum.inr (Sum.inl (152, 1)),
    Sum.inr (Sum.inl (209, 4)),
    Sum.inr (Sum.inl (20, 32)),
    Sum.inr (Sum.inl (20, 16)),
    Sum.inr (Sum.inl (40, 4)),
    Sum.inr (Sum.inl (20, 48)),
    Sum.inr (Sum.inl (175, 20)),
    Sum.inr (Sum.inl (152, 17)),
    Sum.inr (Sum.inl (209, 37)),
    Sum.inr (Sum.inl (215, 4)),
    Sum.inr (Sum.inl (210, 51)),
    Sum.inr (Sum.inl (204, 14)),
    Sum.inr (Sum.inl (147, 30)),
    Sum.inr (Sum.inl (170, 62)),
    Sum.inr (Sum.inl (35, 38)),
    Sum.inr (Sum.inl (15, 10)),
    Sum.inr (Sum.inl (35, 46)),
    Sum.inr (Sum.inl (35, 34)),
    Sum.inr (Sum.inl (210, 28)),
    Sum.inr (Sum.inl (147, 12)),
    Sum.inr (Sum.inl (170, 46)),
    Sum.inr (Sum.inl (204, 44)),
    Sum.inr (Sum.inl (170, 44)),
    Sum.inr (Sum.inl (210, 8)),
    Sum.inr (Sum.inl (147, 14)),
    Sum.inr (Sum.inl (204, 51)),
    Sum.inr (Sum.inl (15, 42)),
    Sum.inr (Sum.inl (15, 26)),
    Sum.inr (Sum.inl (35, 42)),
    Sum.inr (Sum.inl (15, 58)),
    Sum.inr (Sum.inl (170, 60)),
    Sum.inr (Sum.inl (147, 28)),
    Sum.inr (Sum.inl (204, 17)),
    Sum.inr (Sum.inl (210, 39))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock101Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨25856 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock101InputMaskData : ℕ :=
  sixthHex% [
    "eb6700dd6700c66f00b06700d7a700c9af00eea700b0a700cfcf00e5c700",
    "dac700b0c700f3ff00f1ff00f2ff00b0f700fcef00f4ef00f8ef00b0e700",
    "801700a01f00901f00f01f00f17eefc776efdc76efaa76efcdb6efd3beef",
    "f4b6efaab6efd5deefffd6efc0d6efaad6efe9e6efebeeefe8e6efaae6ef",
    "e6f6efeefeefe2feefaafeef9a06efba0eef8a06efea06efa07eee9676ee",
    "8d76eefb76ee9cb6ee82beeea5b6eefbb6ee84deeeaed6ee91d6eefbd6ee",
    "b8eeeebae6eeb9eeeefbeeeeb7f6eebffeeeb3feeefbfeeecb0eeeeb06ee",
    "db0eeebb0eee9e7eeda876edb376edc576eda2b6edbcbeed9bb6edc5b6ed",
    "bad6ed90deedafdeedc5deed86e6ed84eeed87e6edc5e6ed89f6ed81feed",
    "8dfeedc5feedf50eedd506ede50eed850eed8f76ecb97eeca27eecd47eec",
    "b3beecadb6ec8abeecd4beecabdeec81d6ecbed6ecd4d6ec97e6ec95eeec",
    "96e6ecd4e6ec98feec90f6ec9cf6ecd4f6ece40eecc406ecf40eec940eec",
    "987eebae76ebb576ebc376eba4beebbab6eb9dbeebc3beebbcdeeb96d6eb",
    "a9d6ebc3d6eb80e6eb82eeeb81e6ebc3e6eb8ff6eb87feeb8bfeebc3feeb",
    "f30eebd306ebe30eeb830eeb8976eabf7eeaa47eead27eeab5b6eaabbeea",
    "8cb6ead2b6eaadd6ea87deeab8deead2deea91e6ea93eeea90e6ead2e6ea",
    "9efeea96f6ea9af6ead2f6eae20eeac206eaf20eea920eeab776e9817ee9",
    "9a7ee9ec7ee98bb6e995bee9b2b6e9ecb6e993dee9b9d6e986d6e9ecd6e9",
    "afeee9ade6e9aeeee9eceee9a0fee9a8f6e9a4f6e9ecf6e9dc0ee9fc06e9",
    "cc0ee9ac0ee9e676e8d07ee8cb7ee8bd7ee8dab6e8c4bee8e3b6e8bdb6e8",
    "c2dee8e8d6e8d7d6e8bdd6e8fee6e8fceee8ffe6e8bde6e8f1fee8f9f6e8",
    "f5f6e8bdf6e88d06e8ad0ee89d06e8fd06e8ba76e78c7ee7977ee7e17ee7",
    "86b6e798bee7bfb6e7e1b6e79edee7b4d6e78bd6e7e1d6e7a2e6e7a0eee7",
    "a3e6e7e1e6e7adf6e7a5fee7a9fee7e1fee7d10ee7f106e7c10ee7a10ee7",
    "ab7ee69d76e68676e6f076e697bee689b6e6aebee6f0bee68fd6e6a5dee6",
    "9adee6f0dee6b3e6e6b1eee6b2e6e6f0e6e6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock101InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock101InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock101OutputMaskData : ℕ :=
  sixthHex% [
    "64906e43d15f3f0a7f1c0b4572dc2b289c204bdc2b15dc2b20395f6dea7f",
    "55386e1cab451c095f2cdb450b927f3f006e1dd42015dc202cd42b209c20",
    "2c7345597a7f7fe95f0ea06e6602a13003903d98b06fd98a010ee45b4eef",
    "380ee4660ee453eb901e38b026eaa16f798a1e9b905f098a0900b04cd2a1",
    "1f46ef660eef5f06e4220eef5fa18a2aa8b07d7b900c32a125eb9173eaa0",
    "7e71802c30ba42e7d418a7df7be7d425e7d41002a05dd1806503912c90ba",
    "2c32a06da0ba3ba9807e7b915cafdf25e7df1cefd461e7df6d08ba180180",
    "4fd2a03e9b910109885708b95a939908d2a36605cd3c45c65f05cd0105cd",
    "45a0b908739930a1887932a37990b93802a36e0b992bd988784dc60105c6",
    "380dcd4505c649eaa33ce3996b30b91a798846a0b310a1821d3aa24f7b98",
    "21acf67becfd18acf646acf60209824fdaa27708b33e9b984f79820eeb98",
    "58e2a21d30b33fe4fd46acfd7fa4f602acfd7f03980a0aa25dd9822c90b3",
    "895b2edf5a1fd2c13f8080059f176bc55760a6176bf8176bbcb21ff1613f",
    "c9b32e802005f1c21fb05005e6593fa38b2ef01f60895760b05f6bcd5760",
    "c1b805b4b13fe3621f922b2ecef21598f324956804c7293ed8be5082fe5b",
    "e1be50bfbe50fb1b24b6c8048e1a15c7893ec72b2486b93ed0b004956215",
    "b7b65bcefe5bf7f6508afe5bf7513e825804d58b24a4c215ea100cbc113d",
    "b18a1de3cb27fc5c49a61c42c55c499b5c49aeb93de36a1ddbb80c922b27",
    "92893dd31b2785121dc0c00c935442ea1c42d31449ae1c42d3b327a6ba1d",
    "f1693d80200ca9f93cfff80df2632da02217bfb579e5f57286b579d8b579",
    "ed500da0832d98513cd1c217a0200de1b217b7bb2df2693cd0bd72a9f572",
    "90fd79edf572e11a1794132dc3c00db2893c42a0b314a182193aa24b7b98",
    "54ecf60eacfd6decf633ecf60609824bdaa27308b33a9b984b79820aeb98",
    "5ce2a21930b34aa4fd33ecfd0ae4f677ecfd7b03980e0aa259d9822890b3",
    "0509885308b95e93990cd2a31345cd4905c62a45cd7445cd41a0b90c7399",
    "34a1887d32a37d90b93c02a36a0b992fd988"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock101OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock101OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock101InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock101InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock101InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock101OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e17e16df8e37e185f8617df86186185f85f8617df96175d7df8617df7df",
    "85f7e17e17e17df7df6df8e385f7e17e185f7e185f85f7e17df8616df8e3",
    "7df8618618617e185f7e17e186186196175d85f7e185f7e185f7e185f7e1",
    "7e18616e18e386185f8617e186185f8617e185f86195f75d7e17df85f861",
    "7df7e17df7e17e18616e18e37df7e18617e186185f7df85f7e17df6e18e3",
    "7e17df7e17df86185f7df7e186186196175d85f7e185f7e185f7e185f7e1",
    "7df8616df8e37df861861861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock101OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock101OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block101_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock101Input a) =
      generatedSixthXiShortBlock101InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock101Output a) =
      generatedSixthXiShortBlock101OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock101Input a) =
      generatedSixthXiShortBlock101InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock101Output a) =
      generatedSixthXiShortBlock101OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block101_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock101InputMask a) =
      generatedSixthXiShortBlock101OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock101InputMask a)) *
      generatedSixthXiShortBlock101InputNumerator a =
        generatedSixthXiShortBlock101OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block101_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock101Input a
    let y := generatedSixthXiShortBlock101Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block101_cache a
  have hs := generatedSixth_xi_short_block101_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block101_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock101Input a
    let y := generatedSixthXiShortBlock101Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block101_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block101_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock101Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block101_certificate a).1
    (generatedSixth_xi_short_block101_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
