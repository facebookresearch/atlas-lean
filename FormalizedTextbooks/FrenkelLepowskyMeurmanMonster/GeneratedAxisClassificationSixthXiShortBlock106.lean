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
def generatedSixthXiShortBlock106Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (449, 16)),
    Sum.inr (Sum.inr (449, 17)),
    Sum.inr (Sum.inr (458, 6)),
    Sum.inr (Sum.inr (449, 19)),
    Sum.inr (Sum.inr (31, 20)),
    Sum.inr (Sum.inr (85, 9)),
    Sum.inr (Sum.inr (149, 15)),
    Sum.inr (Sum.inr (212, 0)),
    Sum.inr (Sum.inl (158, 48)),
    Sum.inr (Sum.inl (157, 61)),
    Sum.inr (Sum.inl (140, 34)),
    Sum.inr (Sum.inl (153, 29)),
    Sum.inr (Sum.inl (28, 32)),
    Sum.inr (Sum.inl (8, 56)),
    Sum.inr (Sum.inl (28, 40)),
    Sum.inr (Sum.inl (28, 42)),
    Sum.inr (Sum.inl (158, 31)),
    Sum.inr (Sum.inl (140, 13)),
    Sum.inr (Sum.inl (153, 63)),
    Sum.inr (Sum.inl (157, 31)),
    Sum.inr (Sum.inl (153, 31)),
    Sum.inr (Sum.inl (158, 11)),
    Sum.inr (Sum.inl (140, 48)),
    Sum.inr (Sum.inl (157, 34)),
    Sum.inr (Sum.inl (8, 24)),
    Sum.inr (Sum.inl (8, 40)),
    Sum.inr (Sum.inl (28, 34)),
    Sum.inr (Sum.inl (8, 8)),
    Sum.inr (Sum.inl (153, 61)),
    Sum.inr (Sum.inl (140, 31)),
    Sum.inr (Sum.inl (157, 0)),
    Sum.inr (Sum.inl (158, 36)),
    Sum.inr (Sum.inl (213, 45)),
    Sum.inr (Sum.inl (207, 29)),
    Sum.inr (Sum.inl (150, 15)),
    Sum.inr (Sum.inl (173, 62)),
    Sum.inr (Sum.inl (38, 30)),
    Sum.inr (Sum.inl (18, 6)),
    Sum.inr (Sum.inl (38, 22)),
    Sum.inr (Sum.inl (38, 20)),
    Sum.inr (Sum.inl (213, 50)),
    Sum.inr (Sum.inl (150, 47)),
    Sum.inr (Sum.inl (173, 28)),
    Sum.inr (Sum.inl (207, 60)),
    Sum.inr (Sum.inl (173, 30)),
    Sum.inr (Sum.inl (213, 12)),
    Sum.inr (Sum.inl (150, 7)),
    Sum.inr (Sum.inl (207, 35)),
    Sum.inr (Sum.inl (18, 38)),
    Sum.inr (Sum.inl (18, 22)),
    Sum.inr (Sum.inl (38, 28)),
    Sum.inr (Sum.inl (18, 54)),
    Sum.inr (Sum.inl (173, 60)),
    Sum.inr (Sum.inl (150, 39)),
    Sum.inr (Sum.inl (207, 2)),
    Sum.inr (Sum.inl (213, 19)),
    Sum.inr (Sum.inl (119, 13)),
    Sum.inr (Sum.inl (118, 60)),
    Sum.inr (Sum.inl (112, 30)),
    Sum.inr (Sum.inl (114, 33)),
    Sum.inr (Sum.inl (25, 49)),
    Sum.inr (Sum.inl (5, 61)),
    Sum.inr (Sum.inl (25, 57)),
    Sum.inr (Sum.inl (25, 59)),
    Sum.inr (Sum.inl (119, 28)),
    Sum.inr (Sum.inl (112, 12)),
    Sum.inr (Sum.inl (114, 49)),
    Sum.inr (Sum.inl (118, 35)),
    Sum.inr (Sum.inl (114, 51)),
    Sum.inr (Sum.inl (119, 34)),
    Sum.inr (Sum.inl (112, 35)),
    Sum.inr (Sum.inl (118, 11)),
    Sum.inr (Sum.inl (5, 29)),
    Sum.inr (Sum.inl (5, 45)),
    Sum.inr (Sum.inl (25, 51)),
    Sum.inr (Sum.inl (5, 13)),
    Sum.inr (Sum.inl (114, 35)),
    Sum.inr (Sum.inl (112, 49)),
    Sum.inr (Sum.inl (118, 20)),
    Sum.inr (Sum.inl (119, 51)),
    Sum.inr (Sum.inl (53, 30)),
    Sum.inr (Sum.inl (52, 46)),
    Sum.inr (Sum.inl (46, 14)),
    Sum.inr (Sum.inl (48, 3)),
    Sum.inr (Sum.inl (21, 15)),
    Sum.inr (Sum.inl (1, 3)),
    Sum.inr (Sum.inl (21, 7)),
    Sum.inr (Sum.inl (21, 5)),
    Sum.inr (Sum.inl (53, 15)),
    Sum.inr (Sum.inl (46, 31)),
    Sum.inr (Sum.inl (48, 19)),
    Sum.inr (Sum.inl (52, 14)),
    Sum.inr (Sum.inl (48, 7)),
    Sum.inr (Sum.inl (53, 31)),
    Sum.inr (Sum.inl (46, 30)),
    Sum.inr (Sum.inl (52, 15)),
    Sum.inr (Sum.inl (1, 35)),
    Sum.inr (Sum.inl (1, 19)),
    Sum.inr (Sum.inl (21, 13)),
    Sum.inr (Sum.inl (1, 51)),
    Sum.inr (Sum.inl (48, 23)),
    Sum.inr (Sum.inl (46, 15)),
    Sum.inr (Sum.inl (52, 47)),
    Sum.inr (Sum.inl (53, 14)),
    Sum.inr (Sum.inr (207, 13)),
    Sum.inr (Sum.inr (142, 22)),
    Sum.inr (Sum.inr (78, 9)),
    Sum.inr (Sum.inr (4, 3)),
    Sum.inr (Sum.inr (465, 6)),
    Sum.inr (Sum.inr (474, 5)),
    Sum.inr (Sum.inr (465, 4)),
    Sum.inr (Sum.inr (465, 18)),
    Sum.inr (Sum.inr (207, 23)),
    Sum.inr (Sum.inr (78, 2)),
    Sum.inr (Sum.inr (4, 10)),
    Sum.inr (Sum.inr (142, 15)),
    Sum.inr (Sum.inr (4, 12)),
    Sum.inr (Sum.inr (207, 0)),
    Sum.inr (Sum.inr (78, 21)),
    Sum.inr (Sum.inr (142, 11)),
    Sum.inr (Sum.inr (474, 16)),
    Sum.inr (Sum.inr (474, 17)),
    Sum.inr (Sum.inr (465, 7)),
    Sum.inr (Sum.inr (474, 19)),
    Sum.inr (Sum.inr (4, 20)),
    Sum.inr (Sum.inr (78, 14)),
    Sum.inr (Sum.inr (142, 1)),
    Sum.inr (Sum.inr (207, 8)),
    Sum.inr (Sum.inr (132, 23)),
    Sum.inr (Sum.inr (197, 15)),
    Sum.inr (Sum.inr (5, 2)),
    Sum.inr (Sum.inr (79, 10)),
    Sum.inr (Sum.inr (410, 6)),
    Sum.inr (Sum.inr (401, 5)),
    Sum.inr (Sum.inr (410, 4)),
    Sum.inr (Sum.inr (410, 18)),
    Sum.inr (Sum.inr (132, 13)),
    Sum.inr (Sum.inr (5, 9)),
    Sum.inr (Sum.inr (79, 3)),
    Sum.inr (Sum.inr (197, 22)),
    Sum.inr (Sum.inr (79, 20)),
    Sum.inr (Sum.inr (132, 8)),
    Sum.inr (Sum.inr (5, 14)),
    Sum.inr (Sum.inr (197, 1)),
    Sum.inr (Sum.inr (401, 16)),
    Sum.inr (Sum.inr (401, 17)),
    Sum.inr (Sum.inr (410, 7)),
    Sum.inr (Sum.inr (401, 19)),
    Sum.inr (Sum.inr (79, 12)),
    Sum.inr (Sum.inr (5, 21)),
    Sum.inr (Sum.inr (197, 11)),
    Sum.inr (Sum.inr (132, 0)),
    Sum.inr (Sum.inr (6, 0)),
    Sum.inr (Sum.inr (71, 11)),
    Sum.inr (Sum.inr (135, 21)),
    Sum.inr (Sum.inr (205, 12)),
    Sum.inr (Sum.inr (280, 6)),
    Sum.inr (Sum.inr (275, 5)),
    Sum.inr (Sum.inr (280, 4)),
    Sum.inr (Sum.inr (280, 18)),
    Sum.inr (Sum.inr (6, 8)),
    Sum.inr (Sum.inr (135, 14)),
    Sum.inr (Sum.inr (205, 20)),
    Sum.inr (Sum.inr (71, 1)),
    Sum.inr (Sum.inr (205, 3)),
    Sum.inr (Sum.inr (6, 13)),
    Sum.inr (Sum.inr (135, 9)),
    Sum.inr (Sum.inr (71, 22)),
    Sum.inr (Sum.inr (275, 16)),
    Sum.inr (Sum.inr (275, 17)),
    Sum.inr (Sum.inr (280, 7)),
    Sum.inr (Sum.inr (275, 19)),
    Sum.inr (Sum.inr (205, 10)),
    Sum.inr (Sum.inr (135, 2)),
    Sum.inr (Sum.inr (71, 15)),
    Sum.inr (Sum.inr (6, 23)),
    Sum.inr (Sum.inr (70, 8)),
    Sum.inr (Sum.inr (7, 1)),
    Sum.inr (Sum.inr (199, 14)),
    Sum.inr (Sum.inr (141, 20)),
    Sum.inr (Sum.inr (344, 6)),
    Sum.inr (Sum.inr (339, 5)),
    Sum.inr (Sum.inr (344, 4)),
    Sum.inr (Sum.inr (344, 18)),
    Sum.inr (Sum.inr (70, 0)),
    Sum.inr (Sum.inr (199, 21)),
    Sum.inr (Sum.inr (141, 12)),
    Sum.inr (Sum.inr (7, 11)),
    Sum.inr (Sum.inr (141, 10)),
    Sum.inr (Sum.inr (70, 23)),
    Sum.inr (Sum.inr (199, 2)),
    Sum.inr (Sum.inr (7, 15)),
    Sum.inr (Sum.inr (339, 16)),
    Sum.inr (Sum.inr (339, 17)),
    Sum.inr (Sum.inr (344, 7)),
    Sum.inr (Sum.inr (339, 19)),
    Sum.inr (Sum.inr (141, 3)),
    Sum.inr (Sum.inr (199, 9)),
    Sum.inr (Sum.inr (7, 22)),
    Sum.inr (Sum.inr (70, 13)),
    Sum.inr (Sum.inl (71, 5)),
    Sum.inr (Sum.inl (70, 5)),
    Sum.inr (Sum.inl (64, 5)),
    Sum.inr (Sum.inl (66, 25)),
    Sum.inr (Sum.inl (22, 6)),
    Sum.inr (Sum.inl (2, 0)),
    Sum.inr (Sum.inl (22, 12)),
    Sum.inr (Sum.inl (22, 14)),
    Sum.inr (Sum.inl (71, 20)),
    Sum.inr (Sum.inl (64, 37)),
    Sum.inr (Sum.inl (66, 9)),
    Sum.inr (Sum.inl (70, 36)),
    Sum.inr (Sum.inl (66, 17)),
    Sum.inr (Sum.inl (71, 42)),
    Sum.inr (Sum.inl (64, 36)),
    Sum.inr (Sum.inl (70, 59)),
    Sum.inr (Sum.inl (2, 32)),
    Sum.inr (Sum.inl (2, 16)),
    Sum.inr (Sum.inl (22, 4)),
    Sum.inr (Sum.inl (2, 48)),
    Sum.inr (Sum.inl (66, 1)),
    Sum.inr (Sum.inl (64, 4)),
    Sum.inr (Sum.inl (70, 26)),
    Sum.inr (Sum.inl (71, 59)),
    Sum.inr (Sum.inl (215, 54)),
    Sum.inr (Sum.inl (209, 54)),
    Sum.inr (Sum.inl (152, 25)),
    Sum.inr (Sum.inl (175, 5)),
    Sum.inr (Sum.inl (40, 23)),
    Sum.inr (Sum.inl (20, 5)),
    Sum.inr (Sum.inl (40, 29)),
    Sum.inr (Sum.inl (40, 31)),
    Sum.inr (Sum.inl (215, 39)),
    Sum.inr (Sum.inl (152, 9)),
    Sum.inr (Sum.inl (175, 21)),
    Sum.inr (Sum.inl (209, 23)),
    Sum.inr (Sum.inl (175, 23)),
    Sum.inr (Sum.inl (215, 55)),
    Sum.inr (Sum.inl (152, 29)),
    Sum.inr (Sum.inl (209, 22)),
    Sum.inr (Sum.inl (20, 37)),
    Sum.inr (Sum.inl (20, 21)),
    Sum.inr (Sum.inl (40, 21)),
    Sum.inr (Sum.inl (20, 53)),
    Sum.inr (Sum.inl (175, 7)),
    Sum.inr (Sum.inl (152, 13)),
    Sum.inr (Sum.inl (209, 55)),
    Sum.inr (Sum.inl (215, 38)),
    Sum.inr (Sum.inl (104, 42)),
    Sum.inr (Sum.inl (103, 53)),
    Sum.inr (Sum.inl (97, 58)),
    Sum.inr (Sum.inl (99, 5)),
    Sum.inr (Sum.inl (24, 39)),
    Sum.inr (Sum.inl (4, 9)),
    Sum.inr (Sum.inl (24, 45)),
    Sum.inr (Sum.inl (24, 47))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock106Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨27136 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock106InputMaskData : ℕ :=
  sixthHex% [
    "b8ffd6b0f7d6bcf7d6f4f7d6c407d6e40fd6d40fd6b40fd68777d5b17fd5",
    "aa77d5dc77d5bbbfd5a5b7d582bfd5dcbfd5a3d7d589d7d5b6dfd5dcd7d5",
    "9fefd59defd59ee7d5dcefd590ffd598f7d594f7d5dcf7d5ec07d5cc0fd5",
    "fc0fd59c0fd5f577d4c37fd4d877d4ae77d4c9bfd4d7b7d4f0bfd4aebfd4",
    "d1d7d4fbd7d4c4dfd4aed7d4ede7d4efe7d4ecefd4aee7d4e2ffd4eaf7d4",
    "e6f7d4aef7d49e0fd4be07d48e07d4ee07d49477d3a27fd3b977d3cf77d3",
    "a8b7d3b6bfd391b7d3cfb7d3b0dfd39adfd3a5d7d3cfdfd38cefd38eefd3",
    "8de7d3cfefd383ffd38bf7d387f7d3cff7d3ff07d3df0fd3ef0fd38f0fd3",
    "e677d2d07fd2cb77d2bd77d2dab7d2c4bfd2e3b7d2bdb7d2c2dfd2e8dfd2",
    "d7d7d2bddfd2fee7d2fce7d2ffefd2bde7d2f1ffd2f9f7d2f5f7d2bdf7d2",
    "8d0fd2ad07d29d07d2fd07d2ce77d1f87fd1e377d19577d1f2b7d1ecbfd1",
    "cbb7d195b7d1ead7d1c0d7d1ffdfd195d7d1d6efd1d4efd1d7e7d195efd1",
    "d9ffd1d1f7d1ddf7d195f7d1a50fd18507d1b507d1d507d1fc7fd0ca77d0",
    "d17fd0a77fd0c0bfd0deb7d0f9bfd0a7bfd0d8dfd0f2dfd0cdd7d0a7dfd0",
    "e4efd0e6efd0e5e7d0a7efd0ebf7d0e3ffd0efffd0a7ffd0970fd0b707d0",
    "8707d0e707d0f17fbfc777bfdc77bfaa77bfcdb7bfd3bfbff4b7bfaab7bf",
    "d5d7bfffdfbfc0d7bfaad7bfe9efbfebe7bfe8e7bfaae7bfe6ffbfeef7bf",
    "e2ffbfaaffbf9a0fbfba07bf8a07bfea07bf827fbeb477beaf77bed977be",
    "beb7bea0bfbe87b7bed9b7bea6d7be8cdfbeb3d7bed9d7be9ae7be98efbe",
    "9befbed9efbe95ffbe9df7be91ffbed9ffbee907bec90fbef90fbe990fbe",
    "947fbda277bdb977bdcf77bda8b7bdb6bfbd91b7bdcfb7bdb0dfbd9ad7bd",
    "a5dfbdcfdfbd8cefbd8ee7bd8de7bdcfe7bd83ffbd8bf7bd87ffbdcfffbd",
    "ff07bddf0fbdef0fbd8f0fbda777bc917fbc8a7fbcfc7fbc9bbfbc85b7bc",
    "a2bfbcfcbfbc83d7bca9dfbc96d7bcfcd7bcbfefbcbde7bcbee7bcfce7bc",
    "b0f7bcb8ffbcb4f7bcfcf7bccc07bcec0fbcdc0fbcbc0fbcb87fbb8e77bb",
    "9577bbe377bb84bfbb9ab7bbbdbfbbe3bfbb"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock106InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock106InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock106OutputMaskData : ℕ :=
  sixthHex% [
    "4944fd300cfd0904f6740cfd78e3980deaa22b79825a30b337eaa161eb90",
    "1d30b04f718a50e6e40aa6ef69e6e437e6e40203903e90b07702a14fd18a",
    "4f73907fa18a29a8b01d3aa14eaeef37e6ef0eeee473e6ef7f098a0a00b0",
    "2c93905ddaa15703910102a07dd9802f98ba300fd46a4fdf090fd4570fd4",
    "62eaa05e798017eb912f38ba5edaa06e08ba3801800c93912e47df570fdf",
    "6e07d4130fdf6ea0ba1ba9803d3aa04c7391bbf936edf807912327c3621d",
    "adb573f7f57894b573cab573ff5007c3c3278a5136b2821dc36007f3b21d",
    "a5bb27912936c2bd78bbf57882fd73fff578f31a1d861327a08007d1c936",
    "db10068d1137f1ca17a38b2dcd5c43971c48f45c43aa5c439fb937a32a17",
    "eab806d26b2dd2c937e21b2db41217808006a25448db1c48e214439f1c48",
    "e2b32d97ba17b12937c06006dcfa148afb25f62005a4613fcab65190f65a",
    "f3b651adb651e91325d580059c1214a4c13fa4632594b13fc2b805f62a14",
    "a5be5adcf65ae5fe5198f65ae5593f905005b6c325c78a14b8532fee521e",
    "92893ec0c804ae1f6af45f61971f6ac91f6a8dba1eb1293ef8bb2fc06804",
    "b18a1e815804d7513ee3c32fc11761b85f6181576afc5f61f0b00485b93e",
    "a32a1ed2632f1afbf14cfac04161e01320da7df7b427b7bf44f7b41af7b4",
    "5e52c01381e05a13f11380da1322c052b0da75f9e0302bf112ffbf6bb7bf",
    "23ffb45ef7bf5218da2711e00182c070cbf16d89e13b88d03613f06452ca",
    "0a85a450c5af3385a46d85a42920d064f3f02d61e164f2ca1510d05482ca",
    "73cbf03619e1658daf1cc5af548da42985af542aca2123f007b0d076f9e1",
    "452ac2132bf31eb0d34cf1e922268778668c1b268745268770c3f33d10d3",
    "7482c23d11e94cf3f30d61e92a28d36ffac24d2e8c34668c7c2e8701268c",
    "7c89e90980d32f13f35e5ac23618d96019e86d82c83fc3f251149c0b5497",
    "68149c36149c03f1e84e22c807b0d94e23f24e81e80f13f2285ac86d88d9",
    "3e1c974754970f1c9c7214977efbf20bf2c82d61e85c28d9f1eb44a7ea75",
    "aa7155f8306fe7a701bde70adea70180a701"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock106OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock106OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock106InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock106InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock106InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock106OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f7e185f8617df96175d7df8617df7df85f7e17e17e186186196175d",
    "7e185f85f7e185f7e17e185f7e18616e18e37df7e18617e186185f7df85f",
    "85f86195f75d85f86185f8617df7e186185f85f7df95f75d7df7e17df85f",
    "7df7e17df85f85f86195f75d7e17df85f8617df7e17df7e17df85f6e18e3",
    "7df7e17e18617e186186185f7df7e16e18e37e17df86185f7e18618617e1",
    "8617e195f75d7df7e185f7df85f7df86185f86185f95f75d7e17df7df7e1",
    "85f7df8617e185f7e196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock106OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock106OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block106_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock106Input a) =
      generatedSixthXiShortBlock106InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock106Output a) =
      generatedSixthXiShortBlock106OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock106Input a) =
      generatedSixthXiShortBlock106InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock106Output a) =
      generatedSixthXiShortBlock106OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block106_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock106InputMask a) =
      generatedSixthXiShortBlock106OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock106InputMask a)) *
      generatedSixthXiShortBlock106InputNumerator a =
        generatedSixthXiShortBlock106OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block106_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock106Input a
    let y := generatedSixthXiShortBlock106Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block106_cache a
  have hs := generatedSixth_xi_short_block106_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block106_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock106Input a
    let y := generatedSixthXiShortBlock106Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block106_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block106_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock106Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block106_certificate a).1
    (generatedSixth_xi_short_block106_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
