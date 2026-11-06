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
def generatedSixthXiShortBlock064Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (20, 17)),
    Sum.inr (Sum.inl (20, 33)),
    Sum.inr (Sum.inl (40, 1)),
    Sum.inr (Sum.inl (20, 1)),
    Sum.inr (Sum.inl (175, 17)),
    Sum.inr (Sum.inl (152, 4)),
    Sum.inr (Sum.inl (209, 35)),
    Sum.inr (Sum.inl (215, 2)),
    Sum.inr (Sum.inr (472, 0)),
    Sum.inr (Sum.inr (409, 11)),
    Sum.inr (Sum.inr (345, 21)),
    Sum.inr (Sum.inr (275, 12)),
    Sum.inr (Sum.inr (198, 6)),
    Sum.inr (Sum.inr (205, 5)),
    Sum.inr (Sum.inr (198, 4)),
    Sum.inr (Sum.inr (198, 18)),
    Sum.inr (Sum.inr (472, 8)),
    Sum.inr (Sum.inr (345, 14)),
    Sum.inr (Sum.inr (275, 20)),
    Sum.inr (Sum.inr (409, 1)),
    Sum.inr (Sum.inr (275, 3)),
    Sum.inr (Sum.inr (472, 13)),
    Sum.inr (Sum.inr (345, 9)),
    Sum.inr (Sum.inr (409, 22)),
    Sum.inr (Sum.inr (205, 16)),
    Sum.inr (Sum.inr (205, 17)),
    Sum.inr (Sum.inr (198, 7)),
    Sum.inr (Sum.inr (205, 19)),
    Sum.inr (Sum.inr (275, 10)),
    Sum.inr (Sum.inr (345, 2)),
    Sum.inr (Sum.inr (409, 15)),
    Sum.inr (Sum.inr (472, 23)),
    Sum.inr (Sum.inr (408, 8)),
    Sum.inr (Sum.inr (473, 1)),
    Sum.inr (Sum.inr (281, 14)),
    Sum.inr (Sum.inr (339, 20)),
    Sum.inr (Sum.inr (134, 6)),
    Sum.inr (Sum.inr (141, 5)),
    Sum.inr (Sum.inr (134, 4)),
    Sum.inr (Sum.inr (134, 18)),
    Sum.inr (Sum.inr (408, 0)),
    Sum.inr (Sum.inr (281, 21)),
    Sum.inr (Sum.inr (339, 12)),
    Sum.inr (Sum.inr (473, 11)),
    Sum.inr (Sum.inr (339, 10)),
    Sum.inr (Sum.inr (408, 23)),
    Sum.inr (Sum.inr (281, 2)),
    Sum.inr (Sum.inr (473, 15)),
    Sum.inr (Sum.inr (141, 16)),
    Sum.inr (Sum.inr (141, 17)),
    Sum.inr (Sum.inr (134, 7)),
    Sum.inr (Sum.inr (141, 19)),
    Sum.inr (Sum.inr (339, 3)),
    Sum.inr (Sum.inr (281, 9)),
    Sum.inr (Sum.inr (473, 22)),
    Sum.inr (Sum.inr (408, 13)),
    Sum.inr (Sum.inr (273, 13)),
    Sum.inr (Sum.inr (336, 22)),
    Sum.inr (Sum.inr (400, 9)),
    Sum.inr (Sum.inr (474, 3)),
    Sum.inr (Sum.inr (15, 6)),
    Sum.inr (Sum.inr (4, 5)),
    Sum.inr (Sum.inr (15, 4)),
    Sum.inr (Sum.inr (15, 18)),
    Sum.inr (Sum.inr (273, 23)),
    Sum.inr (Sum.inr (400, 2)),
    Sum.inr (Sum.inr (474, 10)),
    Sum.inr (Sum.inr (336, 15)),
    Sum.inr (Sum.inr (474, 12)),
    Sum.inr (Sum.inr (273, 0)),
    Sum.inr (Sum.inr (400, 21)),
    Sum.inr (Sum.inr (336, 11)),
    Sum.inr (Sum.inr (4, 16)),
    Sum.inr (Sum.inr (4, 17)),
    Sum.inr (Sum.inr (15, 7)),
    Sum.inr (Sum.inr (4, 19)),
    Sum.inr (Sum.inr (474, 20)),
    Sum.inr (Sum.inr (400, 14)),
    Sum.inr (Sum.inr (336, 1)),
    Sum.inr (Sum.inr (273, 8)),
    Sum.inr (Sum.inr (346, 23)),
    Sum.inr (Sum.inr (283, 15)),
    Sum.inr (Sum.inr (475, 2)),
    Sum.inr (Sum.inr (401, 10)),
    Sum.inr (Sum.inr (68, 6)),
    Sum.inr (Sum.inr (79, 5)),
    Sum.inr (Sum.inr (68, 4)),
    Sum.inr (Sum.inr (68, 18)),
    Sum.inr (Sum.inr (346, 13)),
    Sum.inr (Sum.inr (475, 9)),
    Sum.inr (Sum.inr (401, 3)),
    Sum.inr (Sum.inr (283, 22)),
    Sum.inr (Sum.inr (401, 20)),
    Sum.inr (Sum.inr (346, 8)),
    Sum.inr (Sum.inr (475, 14)),
    Sum.inr (Sum.inr (283, 1)),
    Sum.inr (Sum.inr (79, 16)),
    Sum.inr (Sum.inr (79, 17)),
    Sum.inr (Sum.inr (68, 7)),
    Sum.inr (Sum.inr (79, 19)),
    Sum.inr (Sum.inr (401, 12)),
    Sum.inr (Sum.inr (475, 21)),
    Sum.inr (Sum.inr (283, 11)),
    Sum.inr (Sum.inr (346, 0)),
    Sum.inr (Sum.inl (119, 41)),
    Sum.inr (Sum.inl (118, 57)),
    Sum.inr (Sum.inl (112, 58)),
    Sum.inr (Sum.inl (114, 55)),
    Sum.inr (Sum.inl (25, 37)),
    Sum.inr (Sum.inl (5, 9)),
    Sum.inr (Sum.inl (25, 45)),
    Sum.inr (Sum.inl (25, 47)),
    Sum.inr (Sum.inl (119, 56)),
    Sum.inr (Sum.inl (112, 40)),
    Sum.inr (Sum.inl (114, 39)),
    Sum.inr (Sum.inl (118, 38)),
    Sum.inr (Sum.inl (114, 37)),
    Sum.inr (Sum.inl (119, 6)),
    Sum.inr (Sum.inl (112, 7)),
    Sum.inr (Sum.inl (118, 14)),
    Sum.inr (Sum.inl (5, 41)),
    Sum.inr (Sum.inl (5, 25)),
    Sum.inr (Sum.inl (25, 39)),
    Sum.inr (Sum.inl (5, 57)),
    Sum.inr (Sum.inl (114, 53)),
    Sum.inr (Sum.inl (112, 21)),
    Sum.inr (Sum.inl (118, 17)),
    Sum.inr (Sum.inl (119, 23)),
    Sum.inr (Sum.inl (53, 24)),
    Sum.inr (Sum.inl (52, 40)),
    Sum.inr (Sum.inl (46, 8)),
    Sum.inr (Sum.inl (48, 22)),
    Sum.inr (Sum.inl (21, 10)),
    Sum.inr (Sum.inl (1, 50)),
    Sum.inr (Sum.inl (21, 2)),
    Sum.inr (Sum.inl (21, 0)),
    Sum.inr (Sum.inl (53, 9)),
    Sum.inr (Sum.inl (46, 25)),
    Sum.inr (Sum.inl (48, 6)),
    Sum.inr (Sum.inl (52, 8)),
    Sum.inr (Sum.inl (48, 18)),
    Sum.inr (Sum.inl (53, 25)),
    Sum.inr (Sum.inl (46, 24)),
    Sum.inr (Sum.inl (52, 9)),
    Sum.inr (Sum.inl (1, 18)),
    Sum.inr (Sum.inl (1, 34)),
    Sum.inr (Sum.inl (21, 8)),
    Sum.inr (Sum.inl (1, 2)),
    Sum.inr (Sum.inl (48, 2)),
    Sum.inr (Sum.inl (46, 9)),
    Sum.inr (Sum.inl (52, 41)),
    Sum.inr (Sum.inl (53, 8)),
    Sum.inr (Sum.inl (158, 49)),
    Sum.inr (Sum.inl (157, 57)),
    Sum.inr (Sum.inl (140, 38)),
    Sum.inr (Sum.inl (153, 59)),
    Sum.inr (Sum.inl (28, 27)),
    Sum.inr (Sum.inl (8, 55)),
    Sum.inr (Sum.inl (28, 19)),
    Sum.inr (Sum.inl (28, 17)),
    Sum.inr (Sum.inl (158, 30)),
    Sum.inr (Sum.inl (140, 9)),
    Sum.inr (Sum.inl (153, 25)),
    Sum.inr (Sum.inl (157, 27)),
    Sum.inr (Sum.inl (153, 57)),
    Sum.inr (Sum.inl (158, 10)),
    Sum.inr (Sum.inl (140, 52)),
    Sum.inr (Sum.inl (157, 38)),
    Sum.inr (Sum.inl (8, 23)),
    Sum.inr (Sum.inl (8, 39)),
    Sum.inr (Sum.inl (28, 25)),
    Sum.inr (Sum.inl (8, 7)),
    Sum.inr (Sum.inl (153, 27)),
    Sum.inr (Sum.inl (140, 27)),
    Sum.inr (Sum.inl (157, 4)),
    Sum.inr (Sum.inl (158, 37)),
    Sum.inr (Sum.inl (213, 57)),
    Sum.inr (Sum.inl (207, 25)),
    Sum.inr (Sum.inl (150, 30)),
    Sum.inr (Sum.inl (173, 24)),
    Sum.inr (Sum.inl (38, 58)),
    Sum.inr (Sum.inl (18, 62)),
    Sum.inr (Sum.inl (38, 50)),
    Sum.inr (Sum.inl (38, 48)),
    Sum.inr (Sum.inl (213, 38)),
    Sum.inr (Sum.inl (150, 62)),
    Sum.inr (Sum.inl (173, 58)),
    Sum.inr (Sum.inl (207, 56)),
    Sum.inr (Sum.inl (173, 56)),
    Sum.inr (Sum.inl (213, 24)),
    Sum.inr (Sum.inl (150, 22)),
    Sum.inr (Sum.inl (207, 39)),
    Sum.inr (Sum.inl (18, 30)),
    Sum.inr (Sum.inl (18, 46)),
    Sum.inr (Sum.inl (38, 56)),
    Sum.inr (Sum.inl (18, 14)),
    Sum.inr (Sum.inl (173, 26)),
    Sum.inr (Sum.inl (150, 54)),
    Sum.inr (Sum.inl (207, 6)),
    Sum.inr (Sum.inl (213, 7)),
    Sum.inr (Sum.inr (385, 13)),
    Sum.inr (Sum.inr (448, 1)),
    Sum.inr (Sum.inr (256, 21)),
    Sum.inr (Sum.inr (330, 10)),
    Sum.inr (Sum.inr (159, 7)),
    Sum.inr (Sum.inr (148, 5)),
    Sum.inr (Sum.inr (159, 18)),
    Sum.inr (Sum.inr (159, 4)),
    Sum.inr (Sum.inr (385, 23)),
    Sum.inr (Sum.inr (256, 14)),
    Sum.inr (Sum.inr (330, 3)),
    Sum.inr (Sum.inr (448, 11)),
    Sum.inr (Sum.inr (330, 20)),
    Sum.inr (Sum.inr (385, 0)),
    Sum.inr (Sum.inr (256, 9)),
    Sum.inr (Sum.inr (448, 15)),
    Sum.inr (Sum.inr (148, 16)),
    Sum.inr (Sum.inr (148, 17)),
    Sum.inr (Sum.inr (159, 6)),
    Sum.inr (Sum.inr (148, 19)),
    Sum.inr (Sum.inr (330, 12)),
    Sum.inr (Sum.inr (256, 2)),
    Sum.inr (Sum.inr (448, 22)),
    Sum.inr (Sum.inr (385, 8)),
    Sum.inr (Sum.inr (266, 23)),
    Sum.inr (Sum.inr (331, 11)),
    Sum.inr (Sum.inr (395, 14)),
    Sum.inr (Sum.inr (449, 3)),
    Sum.inr (Sum.inr (20, 7)),
    Sum.inr (Sum.inr (31, 5)),
    Sum.inr (Sum.inr (20, 18)),
    Sum.inr (Sum.inr (20, 4)),
    Sum.inr (Sum.inr (266, 13)),
    Sum.inr (Sum.inr (395, 21)),
    Sum.inr (Sum.inr (449, 10)),
    Sum.inr (Sum.inr (331, 1)),
    Sum.inr (Sum.inr (449, 12)),
    Sum.inr (Sum.inr (266, 8)),
    Sum.inr (Sum.inr (395, 2)),
    Sum.inr (Sum.inr (331, 22)),
    Sum.inr (Sum.inr (31, 16)),
    Sum.inr (Sum.inr (31, 17)),
    Sum.inr (Sum.inr (20, 6)),
    Sum.inr (Sum.inr (31, 19)),
    Sum.inr (Sum.inr (449, 20)),
    Sum.inr (Sum.inr (395, 9)),
    Sum.inr (Sum.inr (331, 15)),
    Sum.inr (Sum.inr (266, 0)),
    Sum.inr (Sum.inr (450, 0)),
    Sum.inr (Sum.inr (387, 15)),
    Sum.inr (Sum.inr (323, 9)),
    Sum.inr (Sum.inr (265, 20)),
    Sum.inr (Sum.inr (220, 7)),
    Sum.inr (Sum.inr (215, 5)),
    Sum.inr (Sum.inr (220, 18)),
    Sum.inr (Sum.inr (220, 4))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock064Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨16384 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock064InputMaskData : ℕ :=
  sixthHex% [
    "c928d6c120d6cd20d68528d6b5d8d695d8d6a5d8d6c5d8d6c998d5ff90d5",
    "e490d59298d5f550d5eb50d5cc50d59250d5ed30d5c738d5f830d59238d5",
    "d108d5d308d5d000d59200d5de18d5d610d5da10d59218d5a2e8d582e8d5",
    "b2e8d5d2e8d58b78d4bd70d4a670d4d078d4b7b0d4a9b0d48eb0d4d0b0d4",
    "afd0d485d8d4bad0d4d0d8d493e0d491e0d492e8d4d0e8d49cf8d494f0d4",
    "98f0d4d0f8d4e000d4c000d4f000d49000d4dcf0d3eaf8d3f1f8d387f0d3",
    "e030d3fe30d3d930d38730d3f850d3d258d3ed50d38758d3c460d3c660d3",
    "c568d38768d3cb70d3c378d3cf78d38770d3b780d39780d3a780d3c780d3",
    "9e10d2a818d2b318d2c510d2a2d0d2bcd0d29bd0d2c5d0d2bab0d290b8d2",
    "afb0d2c5b8d28688d28488d28780d2c580d28990d28198d28d98d2c590d2",
    "f568d2d568d2e568d28568d28920d1bf28d1a428d1d220d1b5e0d1abe0d1",
    "8ce0d1d2e0d1ad88d18780d1b888d1d280d191b0d193b0d190b8d1d2b8d1",
    "9ea0d196a8d19aa8d1d2a0d1e258d1c258d1f258d19258d18bc0d0bdc8d0",
    "a6c8d0d0c0d0b700d0a900d08e00d0d000d0af68d08560d0ba68d0d060d0",
    "9358d09158d09250d0d050d09c40d09448d09848d0d040d0e0b0d0c0b0d0",
    "f0b0d090b0d0bf38bf8930bf9238bfe430bf83f0bf9df0bfbaf0bfe4f0bf",
    "9b98bfb198bf8e90bfe490bfa7a0bfa5a8bfa6a8bfe4a0bfa8b0bfa0b8bf",
    "acb0bfe4b8bfd448bff448bfc448bfa448bffcd8becad0bed1d8bea7d0be",
    "c010bede10bef910bea710bed878bef278becd70bea770bee448bee640be",
    "e540bea748beeb50bee358beef50bea758be97a0beb7a0be87a0bee7a0be",
    "d5e8bde3e0bdf8e8bd8ee0bde920bdf720bdd020bd8e20bdf140bddb40bd",
    "e448bd8e48bdcd70bdcf78bdcc78bd8e70bdc260bdca68bdc660bd8e68bd",
    "be90bd9e90bdae90bdce90bdd608bce000bcfb08bc8d00bceac0bcf4c0bc",
    "d3c0bc8dc0bcf2a0bcd8a0bce7a8bc8da8bcce98bccc90bccf90bc8d98bc",
    "c180bcc988bcc580bc8d88bcbd78bc9d78bcad78bccd78bcff80bbc988bb",
    "d280bba488bbc340bbdd40bbfa40bba440bb"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock064InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock064InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock064OutputMaskData : ℕ :=
  sixthHex% [
    "ec6b4c95234cac2b47a0634cac8c29a8c5138e5633ff1f02f8fc2aaefd1b",
    "a3663b8067019ff06fb4f064a6f06ff8f06fbc551bf1863bb8142a80c701",
    "f1251bc1f70197fe3bd22c2af0f86489b064b0b86fbcf064b01f01b4563b",
    "92c51be38c2a8b6631dd6700d0fc20f3fd1aec6a74c76a7fd56a748b6a74",
    "cfcf00821c20cb8e31f35d1af3ff00c32d1a952420d0f63183627ffa2a7f",
    "c32274cf6a7fb2c51ab68c20901f00e156310d0ac25b0bf35690d37591e9",
    "1b468730468c2246877c468738e3f37530d33ca2c20471e904d3f33401e9",
    "6208d327dac2050e8c7c468c454e8749068c45e9e941a0d36733f3167ac2",
    "7e90d92891e8250ac8060bf268dc9c43dc9751dc9c0fdc9c4b79e806aac8",
    "4f38d977ebf20609e836dbf260d2c82500d97694970fdc9736d49c3a9c97",
    "4733f2437ac865e9e814a0d96203f13402c03999e01a98da744fb45f4fbf",
    "4d4fb4134fb426aac06b79e022ebf11a38da6bdac05b08da0d01e048d3f1",
    "6a07bf134fbf2a47b4260fbf5ba0da5fe9e0797ac00833f16499e13298d0",
    "3f03f01c02ca72d5a459d5af4bd5a415d5a42030d06de3f02471e11ca2ca",
    "1c00d02cd2ca7adbf03f09e16c9daf15d5af2cdda42095af2c7aca2833f0",
    "0ea0d07fe9e1a40d7af20c4b8ed76badd651c3013fe80134fa013fa4013f",
    "91e44bad776be4e57aad7651dc944b9d0651ba4f6b8edd7add4934a40134",
    "ec493fe00134ecee51e8a76bce344bbf7d7ac00c41960d70ead650c9d76a",
    "a700048c000f9e0004c00004f5e570c9765080e441c9776ac9d57088476a",
    "af0e509b9c41b9480fc0000f88480484000ff9af6afde650db7570aa3c41",
    "f3d658a5d769d90c49fa0d7394da1dbfda16adda1df3da1db77f698bec49",
    "c27e588bed738b4f69cadd73ed9449d906588a9216f3da16bb921db7da16",
    "ca7573ce3c49e8af6999e658e2d768b4d659c80d79eb0c4385db2daedb26",
    "bcdb2de2db2da67e599aed79d37f689aec43eb0e59aa9c438dd579b94768",
    "9b9326e2db26aa932da6db26aa3443ae7d7988ee59f9a7683ef2a168f390",
    "1428b037298a28bee403beef11bee44fbee4"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock064OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock064OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock064InputNumeratorData : ℕ :=
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
def generatedSixthXiShortBlock064InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock064InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock064OutputNumeratorData : ℕ :=
  sixthHex% [
    "8618617e17e185f7e196175d8617df85f85f7df7df7e185f85f85f96175d",
    "85f7e17df8617df7df7e17e17df85f6e18e386185f7e18617e18617df7e1",
    "7df7e16e18e385f86186185f7e18617df85f7df85f6e18e37df7e17e1861",
    "7e186186185f86185f95f75d85f8617df7e185f7df7df85f85f7df95f75d",
    "7df7e17df85f7df7e17df85f85f86195f75d7e17df85f8617df7e17df7e1",
    "7e18616e18e37df7e18617e186185f7df85f7e17df6e18e37e17df7e17df",
    "86185f7df7e18617df96175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock064OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock064OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block064_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock064Input a) =
      generatedSixthXiShortBlock064InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock064Output a) =
      generatedSixthXiShortBlock064OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock064Input a) =
      generatedSixthXiShortBlock064InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock064Output a) =
      generatedSixthXiShortBlock064OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block064_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock064InputMask a) =
      generatedSixthXiShortBlock064OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock064InputMask a)) *
      generatedSixthXiShortBlock064InputNumerator a =
        generatedSixthXiShortBlock064OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block064_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock064Input a
    let y := generatedSixthXiShortBlock064Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block064_cache a
  have hs := generatedSixth_xi_short_block064_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block064_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock064Input a
    let y := generatedSixthXiShortBlock064Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block064_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block064_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock064Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block064_certificate a).1
    (generatedSixth_xi_short_block064_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
