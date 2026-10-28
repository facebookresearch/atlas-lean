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
def generatedSixthXiShortBlock055Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (379, 8)),
    Sum.inr (Sum.inr (101, 0)),
    Sum.inr (Sum.inr (368, 8)),
    Sum.inr (Sum.inr (110, 0)),
    Sum.inr (Sum.inr (228, 8)),
    Sum.inr (Sum.inr (506, 0)),
    Sum.inr (Sum.inr (239, 8)),
    Sum.inr (Sum.inr (497, 0)),
    Sum.inr (Sum.inr (239, 13)),
    Sum.inr (Sum.inr (497, 23)),
    Sum.inr (Sum.inr (228, 13)),
    Sum.inr (Sum.inr (506, 23)),
    Sum.inr (Sum.inr (368, 13)),
    Sum.inr (Sum.inr (110, 23)),
    Sum.inr (Sum.inr (379, 13)),
    Sum.inr (Sum.inr (101, 23)),
    Sum.inr (Sum.inr (314, 13)),
    Sum.inr (Sum.inr (36, 23)),
    Sum.inr (Sum.inr (305, 13)),
    Sum.inr (Sum.inr (47, 23)),
    Sum.inr (Sum.inr (165, 13)),
    Sum.inr (Sum.inr (443, 23)),
    Sum.inr (Sum.inr (174, 13)),
    Sum.inr (Sum.inr (432, 23)),
    Sum.inr (Sum.inr (432, 13)),
    Sum.inr (Sum.inr (174, 23)),
    Sum.inr (Sum.inr (443, 13)),
    Sum.inr (Sum.inr (165, 23)),
    Sum.inr (Sum.inr (47, 13)),
    Sum.inr (Sum.inr (305, 23)),
    Sum.inr (Sum.inr (36, 13)),
    Sum.inr (Sum.inr (314, 23)),
    Sum.inr (Sum.inr (101, 13)),
    Sum.inr (Sum.inr (379, 23)),
    Sum.inr (Sum.inr (110, 13)),
    Sum.inr (Sum.inr (368, 23)),
    Sum.inr (Sum.inr (506, 13)),
    Sum.inr (Sum.inr (228, 23)),
    Sum.inr (Sum.inr (497, 13)),
    Sum.inr (Sum.inr (239, 23)),
    Sum.inr (Sum.inr (504, 23)),
    Sum.inr (Sum.inr (377, 0)),
    Sum.inr (Sum.inr (108, 23)),
    Sum.inr (Sum.inr (237, 0)),
    Sum.inr (Sum.inr (377, 8)),
    Sum.inr (Sum.inr (504, 13)),
    Sum.inr (Sum.inr (237, 8)),
    Sum.inr (Sum.inr (108, 13)),
    Sum.inr (Sum.inr (377, 13)),
    Sum.inr (Sum.inr (504, 8)),
    Sum.inr (Sum.inr (237, 13)),
    Sum.inr (Sum.inr (108, 8)),
    Sum.inr (Sum.inr (504, 0)),
    Sum.inr (Sum.inr (377, 23)),
    Sum.inr (Sum.inr (108, 0)),
    Sum.inr (Sum.inr (237, 23)),
    Sum.inr (Sum.inr (103, 23)),
    Sum.inr (Sum.inr (230, 0)),
    Sum.inr (Sum.inr (499, 23)),
    Sum.inr (Sum.inr (370, 0)),
    Sum.inr (Sum.inr (230, 8)),
    Sum.inr (Sum.inr (103, 13)),
    Sum.inr (Sum.inr (370, 8)),
    Sum.inr (Sum.inr (499, 13)),
    Sum.inr (Sum.inr (230, 13)),
    Sum.inr (Sum.inr (103, 8)),
    Sum.inr (Sum.inr (370, 13)),
    Sum.inr (Sum.inr (499, 8)),
    Sum.inr (Sum.inr (103, 0)),
    Sum.inr (Sum.inr (230, 23)),
    Sum.inr (Sum.inr (499, 0)),
    Sum.inr (Sum.inr (370, 23)),
    Sum.inr (Sum.inr (434, 23)),
    Sum.inr (Sum.inr (307, 0)),
    Sum.inr (Sum.inr (38, 23)),
    Sum.inr (Sum.inr (167, 0)),
    Sum.inr (Sum.inr (307, 8)),
    Sum.inr (Sum.inr (434, 13)),
    Sum.inr (Sum.inr (167, 8)),
    Sum.inr (Sum.inr (38, 13)),
    Sum.inr (Sum.inr (307, 13)),
    Sum.inr (Sum.inr (434, 8)),
    Sum.inr (Sum.inr (167, 13)),
    Sum.inr (Sum.inr (38, 8)),
    Sum.inr (Sum.inr (434, 0)),
    Sum.inr (Sum.inr (307, 23)),
    Sum.inr (Sum.inr (38, 0)),
    Sum.inr (Sum.inr (167, 23)),
    Sum.inr (Sum.inr (45, 23)),
    Sum.inr (Sum.inr (172, 0)),
    Sum.inr (Sum.inr (441, 23)),
    Sum.inr (Sum.inr (312, 0)),
    Sum.inr (Sum.inr (172, 8)),
    Sum.inr (Sum.inr (45, 13)),
    Sum.inr (Sum.inr (312, 8)),
    Sum.inr (Sum.inr (441, 13)),
    Sum.inr (Sum.inr (172, 13)),
    Sum.inr (Sum.inr (45, 8)),
    Sum.inr (Sum.inr (312, 13)),
    Sum.inr (Sum.inr (441, 8)),
    Sum.inr (Sum.inr (45, 0)),
    Sum.inr (Sum.inr (172, 23)),
    Sum.inr (Sum.inr (441, 0)),
    Sum.inr (Sum.inr (312, 23)),
    Sum.inr (Sum.inr (83, 8)),
    Sum.inr (Sum.inr (18, 0)),
    Sum.inr (Sum.inr (147, 8)),
    Sum.inr (Sum.inr (210, 0)),
    Sum.inr (Sum.inr (263, 8)),
    Sum.inr (Sum.inr (326, 0)),
    Sum.inr (Sum.inr (455, 8)),
    Sum.inr (Sum.inr (390, 0)),
    Sum.inr (Sum.inr (268, 8)),
    Sum.inr (Sum.inr (333, 0)),
    Sum.inr (Sum.inr (460, 8)),
    Sum.inr (Sum.inr (397, 0)),
    Sum.inr (Sum.inr (88, 8)),
    Sum.inr (Sum.inr (25, 0)),
    Sum.inr (Sum.inr (152, 8)),
    Sum.inr (Sum.inr (217, 0)),
    Sum.inr (Sum.inr (217, 8)),
    Sum.inr (Sum.inr (152, 0)),
    Sum.inr (Sum.inr (25, 8)),
    Sum.inr (Sum.inr (88, 0)),
    Sum.inr (Sum.inr (397, 8)),
    Sum.inr (Sum.inr (460, 0)),
    Sum.inr (Sum.inr (333, 8)),
    Sum.inr (Sum.inr (268, 0)),
    Sum.inr (Sum.inr (390, 8)),
    Sum.inr (Sum.inr (455, 0)),
    Sum.inr (Sum.inr (326, 8)),
    Sum.inr (Sum.inr (263, 0)),
    Sum.inr (Sum.inr (210, 8)),
    Sum.inr (Sum.inr (147, 0)),
    Sum.inr (Sum.inr (18, 8)),
    Sum.inr (Sum.inr (83, 0)),
    Sum.inr (Sum.inr (18, 13)),
    Sum.inr (Sum.inr (83, 23)),
    Sum.inr (Sum.inr (210, 13)),
    Sum.inr (Sum.inr (147, 23)),
    Sum.inr (Sum.inr (326, 13)),
    Sum.inr (Sum.inr (263, 23)),
    Sum.inr (Sum.inr (390, 13)),
    Sum.inr (Sum.inr (455, 23)),
    Sum.inr (Sum.inr (333, 13)),
    Sum.inr (Sum.inr (268, 23)),
    Sum.inr (Sum.inr (397, 13)),
    Sum.inr (Sum.inr (460, 23)),
    Sum.inr (Sum.inr (25, 13)),
    Sum.inr (Sum.inr (88, 23)),
    Sum.inr (Sum.inr (217, 13)),
    Sum.inr (Sum.inr (152, 23)),
    Sum.inr (Sum.inr (152, 13)),
    Sum.inr (Sum.inr (217, 23)),
    Sum.inr (Sum.inr (88, 13)),
    Sum.inr (Sum.inr (25, 23)),
    Sum.inr (Sum.inr (460, 13)),
    Sum.inr (Sum.inr (397, 23)),
    Sum.inr (Sum.inr (268, 13)),
    Sum.inr (Sum.inr (333, 23)),
    Sum.inr (Sum.inr (455, 13)),
    Sum.inr (Sum.inr (390, 23)),
    Sum.inr (Sum.inr (263, 13)),
    Sum.inr (Sum.inr (326, 23)),
    Sum.inr (Sum.inr (147, 13)),
    Sum.inr (Sum.inr (210, 23)),
    Sum.inr (Sum.inr (83, 13)),
    Sum.inr (Sum.inr (18, 23)),
    Sum.inr (Sum.inr (496, 0)),
    Sum.inr (Sum.inr (175, 0)),
    Sum.inr (Sum.inr (111, 0)),
    Sum.inr (Sum.inr (304, 0)),
    Sum.inr (Sum.inr (37, 0)),
    Sum.inr (Sum.inr (378, 0)),
    Sum.inr (Sum.inr (442, 0)),
    Sum.inr (Sum.inr (229, 0)),
    Sum.inr (Sum.inr (507, 0)),
    Sum.inr (Sum.inr (164, 0)),
    Sum.inr (Sum.inr (100, 0)),
    Sum.inr (Sum.inr (315, 0)),
    Sum.inr (Sum.inr (46, 0)),
    Sum.inr (Sum.inr (369, 0)),
    Sum.inr (Sum.inr (433, 0)),
    Sum.inr (Sum.inr (238, 0)),
    Sum.inr (Sum.inr (238, 8)),
    Sum.inr (Sum.inr (433, 8)),
    Sum.inr (Sum.inr (369, 8)),
    Sum.inr (Sum.inr (46, 8)),
    Sum.inr (Sum.inr (315, 8)),
    Sum.inr (Sum.inr (100, 8)),
    Sum.inr (Sum.inr (164, 8)),
    Sum.inr (Sum.inr (507, 8)),
    Sum.inr (Sum.inr (229, 8)),
    Sum.inr (Sum.inr (442, 8)),
    Sum.inr (Sum.inr (378, 8)),
    Sum.inr (Sum.inr (37, 8)),
    Sum.inr (Sum.inr (304, 8)),
    Sum.inr (Sum.inr (111, 8)),
    Sum.inr (Sum.inr (175, 8)),
    Sum.inr (Sum.inr (496, 8)),
    Sum.inr (Sum.inr (238, 13)),
    Sum.inr (Sum.inr (433, 13)),
    Sum.inr (Sum.inr (369, 13)),
    Sum.inr (Sum.inr (46, 13)),
    Sum.inr (Sum.inr (315, 13)),
    Sum.inr (Sum.inr (100, 13)),
    Sum.inr (Sum.inr (164, 13)),
    Sum.inr (Sum.inr (507, 13)),
    Sum.inr (Sum.inr (229, 13)),
    Sum.inr (Sum.inr (442, 13)),
    Sum.inr (Sum.inr (378, 13)),
    Sum.inr (Sum.inr (37, 13)),
    Sum.inr (Sum.inr (304, 13)),
    Sum.inr (Sum.inr (111, 13)),
    Sum.inr (Sum.inr (175, 13)),
    Sum.inr (Sum.inr (496, 13)),
    Sum.inr (Sum.inr (496, 23)),
    Sum.inr (Sum.inr (175, 23)),
    Sum.inr (Sum.inr (111, 23)),
    Sum.inr (Sum.inr (304, 23)),
    Sum.inr (Sum.inr (37, 23)),
    Sum.inr (Sum.inr (378, 23)),
    Sum.inr (Sum.inr (442, 23)),
    Sum.inr (Sum.inr (229, 23)),
    Sum.inr (Sum.inr (507, 23)),
    Sum.inr (Sum.inr (164, 23)),
    Sum.inr (Sum.inr (100, 23)),
    Sum.inr (Sum.inr (315, 23)),
    Sum.inr (Sum.inr (46, 23)),
    Sum.inr (Sum.inr (369, 23)),
    Sum.inr (Sum.inr (433, 23)),
    Sum.inr (Sum.inr (238, 23)),
    Sum.inr (Sum.inr (64, 23)),
    Sum.inr (Sum.inr (64, 8)),
    Sum.inr (Sum.inr (193, 13)),
    Sum.inr (Sum.inr (193, 0)),
    Sum.inr (Sum.inr (341, 13)),
    Sum.inr (Sum.inr (341, 0)),
    Sum.inr (Sum.inr (468, 23)),
    Sum.inr (Sum.inr (468, 8)),
    Sum.inr (Sum.inr (350, 13)),
    Sum.inr (Sum.inr (350, 0)),
    Sum.inr (Sum.inr (479, 23)),
    Sum.inr (Sum.inr (479, 8)),
    Sum.inr (Sum.inr (75, 23)),
    Sum.inr (Sum.inr (75, 8)),
    Sum.inr (Sum.inr (202, 13)),
    Sum.inr (Sum.inr (202, 0)),
    Sum.inr (Sum.inr (64, 0)),
    Sum.inr (Sum.inr (64, 13)),
    Sum.inr (Sum.inr (193, 8)),
    Sum.inr (Sum.inr (193, 23)),
    Sum.inr (Sum.inr (341, 8)),
    Sum.inr (Sum.inr (341, 23)),
    Sum.inr (Sum.inr (468, 0)),
    Sum.inr (Sum.inr (468, 13))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock055Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨14080 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock055InputMaskData : ℕ :=
  sixthHex% [
    "5c3aa176eaa126eaa10c32a17e1aa154c2a104c2a12e12a1102aa13afaa1",
    "6afaa14022a1320aa118d2a148d2a16202a1360aa11cd2a14cd2a16602a1",
    "1422a13ef2a16ef2a1442aa1222c417b9c414b9c411224416b9c41322441",
    "0224415b9441136c414ad4417ad4412364415ad4410364413364416adc41",
    "5b7c4102c44132c4416b744112c4414b74417b744122cc416a3441338441",
    "0384415a3c412384417a3c414a3c41138c41314c4168f44158f441014441",
    "78f44121444111444148fc4100044159b44169b441300c4149b441100c41",
    "200c4179bc4148144111a44121a441781c4101a441581c41681c4131ac41",
    "79544120ec4110ec41495c4130ec41695c41595c4100e4414e82c263f2c2",
    "33f2c21e8ac26b02c2467ac2167ac23b0ac26702c24a7ac21a7ac2370ac2",
    "428ac26ffac23ffac21282c22322c20e5ac25e5ac2732ac206aac22bdac2",
    "7bdac256a2c20aaac227dac277dac25aa2c22f2ac20252c25252c27f22c2",
    "4922c2645ac2345ac2192ac26caac241dac211dac23ca2c260aac24ddac2",
    "1ddac230a2c2452ac26852c23852c21522c2248ac209fac259fac27482c2",
    "010ac22c72c27c72c25102c20d0ac22072c27072c25d02c22882c205f2c2",
    "55f2c2788ac240e4497694497e6449481c49367449000c4908fc493e8c49",
    "5c44496a3c4962cc4954bc492adc491cac49145c492224494f2449795c49",
    "71ac4947dc4939bc490fcc49073c49314449538c4965fc496d0c495b7449",
    "251c491364491b94492de44936e449009c49086c493e1c49407c49760c49",
    "7efc494884492a4c491c3c4914cc4922b4495cdc496aa449625449542449",
    "392c490f5c4907ac4931d4494fbc4979c449713449474449258c4913f449",
    "1b04492d74495314496564496d94495bec492224401b94401364402adc40",
    "19744020cc40283c40118c401a744023cc402b3c40128c40212c40189c40",
    "106c4029d44018744021cc40293c40108c40232c401a9c40126c402bd440",
    "202c40199c40116c4028d4401b7c4022c4402a344013844031444008fc40",
    "000c4039bc400a1c4033ac403b5c4002e440"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock055InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock055InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock055OutputMaskData : ℕ :=
  sixthHex% [
    "ea7764c0af64977575cced75e2db21b94321ee9930c44130b9e32a933b2a",
    "c4e13b9f793bb14f6fead76fbd0d7e97d57e804f64dbd7648c0d75a6d575",
    "f9a321d37b2184a130df3930ab0b9efc7ee1daedc1fcd8bedea4fbf89184",
    "de02a48977dbaf43958976eaafe5caf890b5abacf0fcd98fda4aaffc7fd0",
    "cdd7d0ebe2afcd718f9a04f0c938b59e4dcab8deea9eeb95b8dfdbefaaa4",
    "c93984ef0cfbcd70beeb45c1cdd6e19aa39ea7efd081daafa7498ff03cf0",
    "a300b5f475cad2e6eaf4d395d2e7db8592a4a301848534fba748be817dc1",
    "a7eee1f09b9eb0739ee706e1c195c1e7a0bec5dcfbe3e984c57aa4920fdb",
    "b43b95920eeab49dcae3e8b5b0d4f0e7a18fc132afe707d0941862a82953",
    "fff342b282738a5d16c72c2790f636acc707b3551dfe242ca9fe3d95cf0c",
    "dc5069e06158b7bb49faca78cb6278861349d1c958edf869a4670c98563d",
    "cf8c2c82fd1d9d6f07a15e36f68427bbf516832a73ce5b42998153a5b062",
    "82f153cf8062985a73a46b42edf427d1c516861f07cb6e36d4fc2ce8cd1d",
    "bf170cf2663dcab95887c869d01278ec2349accb4990fa78c720698a5158",
    "b28e3dffff0ca8251d94142c8b8636c6f707912d16ad1c27e48342d8b273",
    "8f6862c219539da4f8ac0ee98e7aacce90bdeceee9ac04f88e70bdbfdaac",
    "86d6e9c63cf8e448bdd5e2ac86dcf8b776e99502acd5e8bd8a32a7cad8b6",
    "e8acf3d906e28a38b6bb92a799e6e2d90cf3e000b6d1aaa7f3dee2b334f3",
    "914aa7d1a0b6f3d4f3c27ee2cfe5c28f0fd3ad7b969cd187cfefd3fe45c2",
    "dc31879cdb96a5d7d3947dc2b60987f6e396d49dc29477d3b6039687a987",
    "a9339d98998cbaedc9fa07d8d8798c98939dbae7d88b4dc9b2418cf2ab9d",
    "d0dfd8e175c9b24b9d83e18ca195c9e17fd8d9e39fffdfd1ddab948ad7da",
    "faedc0ad918e8fe5cba9d985dda4fa8ad8b4a8acf18e90bf8feaa5a9d6eb",
    "8ba2aedcdee0ed76e0ba0aae987eebbe42a5bf38bf9904f1bb70b4ec0cfa",
    "987185be4dcb9c398ecb45c0bb7fdaec0394ce77d1e84b9fd507d1827b9f",
    "a00fda86339487498ea175c0830185d47dcb"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock055OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock055OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock055InputNumeratorData : ℕ :=
  sixthHex% [
    "7e186186185f85f7df7df7e17df7e17e18617df7e185f7df7e18617df7e1",
    "85f7df86185f7df7e185f7df85f7df86185f7df7e185f7df86185f7e1861",
    "85f7df86185f7df7e17e186185f7df7df7e185f7df7df7e186185f85f7df",
    "85f7df7df7e186185f85f7df86185f85f7df7e186186185f7df7e185f7df",
    "85f7df86185f7e18617df7e17df7e185f7df7e18617df7e17df7e185f7df",
    "86185f7e18617e18617df7e17df7e185f7df85f7df86185f7e18617df7e1",
    "7df7e185f7df85f7df86185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock055InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock055InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock055OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7df86185f7e18617df7e186185f7e18617e186186185f86185f85f7df",
    "7df7e17e18617e186186185f7df7e17e18617e186186185f85f7df7df7e1",
    "7df7e17e18618617e185f8617e17df8617e185f8617df85f8617e185f861",
    "7e17df8617e17df85f7e17df8617e185f8617e17df8617e17e17df7df85f",
    "7df85f85f8618617e17e17df7e17df7df85f8617e17e17df7e17df7df85f",
    "85f8618617e18617e17e17df7e186186185f7df7e17e186186185f85f7df",
    "7e186186185f7df7e17e1861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock055OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock055OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block055_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock055Input a) =
      generatedSixthXiShortBlock055InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock055Output a) =
      generatedSixthXiShortBlock055OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock055Input a) =
      generatedSixthXiShortBlock055InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock055Output a) =
      generatedSixthXiShortBlock055OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block055_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock055InputMask a) =
      generatedSixthXiShortBlock055OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock055InputMask a)) *
      generatedSixthXiShortBlock055InputNumerator a =
        generatedSixthXiShortBlock055OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block055_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock055Input a
    let y := generatedSixthXiShortBlock055Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block055_cache a
  have hs := generatedSixth_xi_short_block055_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block055_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock055Input a
    let y := generatedSixthXiShortBlock055Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block055_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block055_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock055Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block055_certificate a).1
    (generatedSixth_xi_short_block055_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
