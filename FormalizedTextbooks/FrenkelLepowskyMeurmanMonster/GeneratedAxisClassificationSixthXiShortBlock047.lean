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
def generatedSixthXiShortBlock047Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (407, 13)),
    Sum.inr (Sum.inr (348, 23)),
    Sum.inr (Sum.inr (285, 13)),
    Sum.inr (Sum.inr (470, 23)),
    Sum.inr (Sum.inr (73, 13)),
    Sum.inr (Sum.inr (130, 23)),
    Sum.inr (Sum.inr (195, 13)),
    Sum.inr (Sum.inr (8, 23)),
    Sum.inr (Sum.inr (195, 8)),
    Sum.inr (Sum.inr (8, 0)),
    Sum.inr (Sum.inr (73, 8)),
    Sum.inr (Sum.inr (130, 0)),
    Sum.inr (Sum.inr (285, 8)),
    Sum.inr (Sum.inr (470, 0)),
    Sum.inr (Sum.inr (407, 8)),
    Sum.inr (Sum.inr (348, 0)),
    Sum.inr (Sum.inr (278, 8)),
    Sum.inr (Sum.inr (477, 0)),
    Sum.inr (Sum.inr (412, 8)),
    Sum.inr (Sum.inr (343, 0)),
    Sum.inr (Sum.inr (200, 8)),
    Sum.inr (Sum.inr (3, 0)),
    Sum.inr (Sum.inr (66, 8)),
    Sum.inr (Sum.inr (137, 0)),
    Sum.inr (Sum.inr (8, 13)),
    Sum.inr (Sum.inr (195, 23)),
    Sum.inr (Sum.inr (130, 13)),
    Sum.inr (Sum.inr (73, 23)),
    Sum.inr (Sum.inr (470, 13)),
    Sum.inr (Sum.inr (285, 23)),
    Sum.inr (Sum.inr (348, 13)),
    Sum.inr (Sum.inr (407, 23)),
    Sum.inr (Sum.inr (477, 13)),
    Sum.inr (Sum.inr (278, 23)),
    Sum.inr (Sum.inr (343, 13)),
    Sum.inr (Sum.inr (412, 23)),
    Sum.inr (Sum.inr (3, 13)),
    Sum.inr (Sum.inr (200, 23)),
    Sum.inr (Sum.inr (137, 13)),
    Sum.inr (Sum.inr (66, 23)),
    Sum.inr (Sum.inl (50, 17)),
    Sum.inr (Sum.inl (160, 12)),
    Sum.inr (Sum.inl (122, 12)),
    Sum.inr (Sum.inl (228, 20)),
    Sum.inr (Sum.inl (94, 20)),
    Sum.inr (Sum.inl (96, 18)),
    Sum.inr (Sum.inl (69, 34)),
    Sum.inr (Sum.inl (180, 48)),
    Sum.inr (Sum.inl (94, 23)),
    Sum.inr (Sum.inl (96, 30)),
    Sum.inr (Sum.inl (69, 46)),
    Sum.inr (Sum.inl (180, 60)),
    Sum.inr (Sum.inl (50, 19)),
    Sum.inr (Sum.inl (160, 14)),
    Sum.inr (Sum.inl (122, 30)),
    Sum.inr (Sum.inl (228, 28)),
    Sum.inr (Sum.inl (160, 9)),
    Sum.inr (Sum.inl (50, 62)),
    Sum.inr (Sum.inl (228, 5)),
    Sum.inr (Sum.inl (122, 59)),
    Sum.inr (Sum.inl (96, 3)),
    Sum.inr (Sum.inl (94, 59)),
    Sum.inr (Sum.inl (180, 33)),
    Sum.inr (Sum.inl (69, 61)),
    Sum.inr (Sum.inl (96, 15)),
    Sum.inr (Sum.inl (94, 56)),
    Sum.inr (Sum.inl (180, 45)),
    Sum.inr (Sum.inl (69, 49)),
    Sum.inr (Sum.inl (160, 11)),
    Sum.inr (Sum.inl (50, 60)),
    Sum.inr (Sum.inl (228, 13)),
    Sum.inr (Sum.inl (122, 41)),
    Sum.inr (Sum.inl (50, 24)),
    Sum.inr (Sum.inl (160, 59)),
    Sum.inr (Sum.inl (122, 40)),
    Sum.inr (Sum.inl (228, 48)),
    Sum.inr (Sum.inl (94, 16)),
    Sum.inr (Sum.inl (96, 16)),
    Sum.inr (Sum.inl (69, 48)),
    Sum.inr (Sum.inl (180, 16)),
    Sum.inr (Sum.inl (94, 19)),
    Sum.inr (Sum.inl (96, 28)),
    Sum.inr (Sum.inl (69, 60)),
    Sum.inr (Sum.inl (180, 28)),
    Sum.inr (Sum.inl (50, 26)),
    Sum.inr (Sum.inl (160, 57)),
    Sum.inr (Sum.inl (122, 58)),
    Sum.inr (Sum.inl (228, 56)),
    Sum.inr (Sum.inl (160, 62)),
    Sum.inr (Sum.inl (50, 55)),
    Sum.inr (Sum.inl (228, 33)),
    Sum.inr (Sum.inl (122, 31)),
    Sum.inr (Sum.inl (96, 1)),
    Sum.inr (Sum.inl (94, 63)),
    Sum.inr (Sum.inl (180, 1)),
    Sum.inr (Sum.inl (69, 47)),
    Sum.inr (Sum.inl (96, 13)),
    Sum.inr (Sum.inl (94, 60)),
    Sum.inr (Sum.inl (180, 13)),
    Sum.inr (Sum.inl (69, 35)),
    Sum.inr (Sum.inl (160, 60)),
    Sum.inr (Sum.inl (50, 53)),
    Sum.inr (Sum.inl (228, 41)),
    Sum.inr (Sum.inl (122, 13)),
    Sum.inr (Sum.inl (137, 61)),
    Sum.inr (Sum.inl (109, 20)),
    Sum.inr (Sum.inl (137, 49)),
    Sum.inr (Sum.inl (109, 28)),
    Sum.inr (Sum.inl (68, 42)),
    Sum.inr (Sum.inl (51, 13)),
    Sum.inr (Sum.inl (68, 40)),
    Sum.inr (Sum.inl (51, 1)),
    Sum.inr (Sum.inl (227, 31)),
    Sum.inr (Sum.inl (79, 32)),
    Sum.inr (Sum.inl (227, 13)),
    Sum.inr (Sum.inl (79, 44)),
    Sum.inr (Sum.inl (159, 43)),
    Sum.inr (Sum.inl (181, 11)),
    Sum.inr (Sum.inl (159, 40)),
    Sum.inr (Sum.inl (181, 9)),
    Sum.inr (Sum.inl (109, 5)),
    Sum.inr (Sum.inl (137, 34)),
    Sum.inr (Sum.inl (109, 13)),
    Sum.inr (Sum.inl (137, 46)),
    Sum.inr (Sum.inl (51, 44)),
    Sum.inr (Sum.inl (68, 53)),
    Sum.inr (Sum.inl (51, 32)),
    Sum.inr (Sum.inl (68, 55)),
    Sum.inr (Sum.inl (79, 1)),
    Sum.inr (Sum.inl (227, 40)),
    Sum.inr (Sum.inl (79, 13)),
    Sum.inr (Sum.inl (227, 58)),
    Sum.inr (Sum.inl (181, 26)),
    Sum.inr (Sum.inl (159, 52)),
    Sum.inr (Sum.inl (181, 24)),
    Sum.inr (Sum.inl (159, 55)),
    Sum.inr (Sum.inl (68, 62)),
    Sum.inr (Sum.inl (51, 34)),
    Sum.inr (Sum.inl (68, 60)),
    Sum.inr (Sum.inl (51, 46)),
    Sum.inr (Sum.inl (137, 60)),
    Sum.inr (Sum.inl (109, 41)),
    Sum.inr (Sum.inl (137, 48)),
    Sum.inr (Sum.inl (109, 33)),
    Sum.inr (Sum.inl (159, 63)),
    Sum.inr (Sum.inl (181, 47)),
    Sum.inr (Sum.inl (159, 60)),
    Sum.inr (Sum.inl (181, 45)),
    Sum.inr (Sum.inl (227, 30)),
    Sum.inr (Sum.inl (79, 29)),
    Sum.inr (Sum.inl (227, 12)),
    Sum.inr (Sum.inl (79, 17)),
    Sum.inr (Sum.inl (51, 3)),
    Sum.inr (Sum.inl (68, 33)),
    Sum.inr (Sum.inl (51, 15)),
    Sum.inr (Sum.inl (68, 35)),
    Sum.inr (Sum.inl (109, 56)),
    Sum.inr (Sum.inl (137, 35)),
    Sum.inr (Sum.inl (109, 48)),
    Sum.inr (Sum.inl (137, 47)),
    Sum.inr (Sum.inl (181, 62)),
    Sum.inr (Sum.inl (159, 32)),
    Sum.inr (Sum.inl (181, 60)),
    Sum.inr (Sum.inl (159, 35)),
    Sum.inr (Sum.inl (79, 60)),
    Sum.inr (Sum.inl (227, 41)),
    Sum.inr (Sum.inl (79, 48)),
    Sum.inr (Sum.inl (227, 59)),
    Sum.inr (Sum.inl (82, 16)),
    Sum.inr (Sum.inl (82, 15)),
    Sum.inr (Sum.inl (76, 5)),
    Sum.inr (Sum.inl (76, 56)),
    Sum.inr (Sum.inl (200, 30)),
    Sum.inr (Sum.inl (200, 31)),
    Sum.inr (Sum.inl (224, 53)),
    Sum.inr (Sum.inl (224, 5)),
    Sum.inr (Sum.inl (120, 45)),
    Sum.inr (Sum.inl (120, 16)),
    Sum.inr (Sum.inl (101, 53)),
    Sum.inr (Sum.inl (101, 17)),
    Sum.inr (Sum.inl (45, 63)),
    Sum.inr (Sum.inl (45, 23)),
    Sum.inr (Sum.inl (182, 12)),
    Sum.inr (Sum.inl (182, 13)),
    Sum.inr (Sum.inl (76, 13)),
    Sum.inr (Sum.inl (76, 48)),
    Sum.inr (Sum.inl (82, 28)),
    Sum.inr (Sum.inl (82, 3)),
    Sum.inr (Sum.inl (224, 55)),
    Sum.inr (Sum.inl (224, 7)),
    Sum.inr (Sum.inl (200, 18)),
    Sum.inr (Sum.inl (200, 19)),
    Sum.inr (Sum.inl (101, 55)),
    Sum.inr (Sum.inl (101, 19)),
    Sum.inr (Sum.inl (120, 33)),
    Sum.inr (Sum.inl (120, 28)),
    Sum.inr (Sum.inl (182, 30)),
    Sum.inr (Sum.inl (182, 31)),
    Sum.inr (Sum.inl (45, 60)),
    Sum.inr (Sum.inl (45, 20)),
    Sum.inr (Sum.inl (120, 13)),
    Sum.inr (Sum.inl (120, 48)),
    Sum.inr (Sum.inl (101, 26)),
    Sum.inr (Sum.inl (101, 62)),
    Sum.inr (Sum.inl (45, 47)),
    Sum.inr (Sum.inl (45, 7)),
    Sum.inr (Sum.inl (182, 36)),
    Sum.inr (Sum.inl (182, 37)),
    Sum.inr (Sum.inl (82, 2)),
    Sum.inr (Sum.inl (82, 29)),
    Sum.inr (Sum.inl (76, 17)),
    Sum.inr (Sum.inl (76, 44)),
    Sum.inr (Sum.inl (200, 60)),
    Sum.inr (Sum.inl (200, 61)),
    Sum.inr (Sum.inl (224, 60)),
    Sum.inr (Sum.inl (224, 12)),
    Sum.inr (Sum.inl (101, 24)),
    Sum.inr (Sum.inl (101, 60)),
    Sum.inr (Sum.inl (120, 1)),
    Sum.inr (Sum.inl (120, 60)),
    Sum.inr (Sum.inl (182, 54)),
    Sum.inr (Sum.inl (182, 55)),
    Sum.inr (Sum.inl (45, 44)),
    Sum.inr (Sum.inl (45, 4)),
    Sum.inr (Sum.inl (76, 25)),
    Sum.inr (Sum.inl (76, 36)),
    Sum.inr (Sum.inl (82, 14)),
    Sum.inr (Sum.inl (82, 17)),
    Sum.inr (Sum.inl (224, 62)),
    Sum.inr (Sum.inl (224, 14)),
    Sum.inr (Sum.inl (200, 48)),
    Sum.inr (Sum.inl (200, 49)),
    Sum.inr (Sum.inl (135, 5)),
    Sum.inr (Sum.inl (199, 12)),
    Sum.inr (Sum.inl (85, 24)),
    Sum.inr (Sum.inl (219, 36)),
    Sum.inr (Sum.inl (98, 20)),
    Sum.inr (Sum.inl (62, 18)),
    Sum.inr (Sum.inl (59, 2)),
    Sum.inr (Sum.inl (183, 48)),
    Sum.inr (Sum.inl (98, 23)),
    Sum.inr (Sum.inl (62, 30)),
    Sum.inr (Sum.inl (59, 14)),
    Sum.inr (Sum.inl (183, 60)),
    Sum.inr (Sum.inl (135, 7)),
    Sum.inr (Sum.inl (199, 30)),
    Sum.inr (Sum.inl (85, 26)),
    Sum.inr (Sum.inl (219, 44)),
    Sum.inr (Sum.inl (135, 12)),
    Sum.inr (Sum.inl (199, 36)),
    Sum.inr (Sum.inl (85, 47)),
    Sum.inr (Sum.inl (219, 48)),
    Sum.inr (Sum.inl (98, 4)),
    Sum.inr (Sum.inl (62, 48)),
    Sum.inr (Sum.inl (59, 16)),
    Sum.inr (Sum.inl (183, 32))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock047Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨12032 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock047InputMaskData : ℕ :=
  sixthHex% [
    "4dd34a6da34a5da34a7ddb4a09534a292b4a192b4a395b4a01f34a21834a",
    "11834a31fb4a45734a650b4a550b4a757b4a4d734a6d0b4a5d0b4a7d7b4a",
    "09fb4a298b4a198b4a39f34a779dc13aedc1561dc11b65c11a0dc15775c1",
    "3b85c176f5c14f3dc10245c16eb5c123c5c122a5c16fd5c10325c14e5dc1",
    "635dc12e25c142d5c10fa5c10ec5c143b5c12f45c1623dc15bf5c11685c1",
    "7a75c1370dc13665c17b1dc117edc15a9dc16c9dc121e5c14d15c10065c1",
    "0105c14c75c12085c16dfdc15435c11945c175b5c138cdc139a5c174ddc1",
    "182dc1555dc17855c13525c159d5c114adc115c5c158bdc1344dc1793dc1",
    "40f5c10d8dc1617dc12c0dc12d6dc1601dc10cedc14195c1385dc861edc8",
    "0d1dc854a5c8030dc85ab5c83645c86ff5c8000dc859b5c83545c86cf5c8",
    "3b55c862e5c80e15c857adc8020dc85bb5c83745c86ef5c83955c860e5c8",
    "0c15c855adc83a55c863e5c80f15c856adc80105c858bdc8344dc86dfdc8",
    "143dc84d85c82175c878c5c82f65c876d5c81a25c8439dc82c65c875d5c8",
    "1925c8409dc81735c84e8dc8227dc87bcdc82e65c877d5c81b25c8429dc8",
    "1535c84c8dc8207dc879cdc81635c84f8dc8237dc87acdc82d6dc874ddc8",
    "182dc84195c84001e60071e66071e62009e64081e600f9e660f9e62089e6",
    "0c81e64cf9e62cf9e66c89e60c09e64c79e62c79e66c01e64091e600e9e6",
    "60e9e62099e64019e60069e66069e62011e60c19e64c69e62c69e66c11e6",
    "0c99e64ce1e62ce1e66c91e60191e641e9e621e9e66199e60119e64169e6",
    "2169e66111e64d19e60d69e66d69e62d11e64d99e60de1e66de1e62d91e6",
    "0109e64179e62179e66101e60189e641f1e621f1e66181e64d89e60df1e6",
    "6df1e62d81e64d01e60d71e66d71e62d09e6232188635188035188432988",
    "6ba1882bd9884bd9880ba9886fa1882fd9884fd9880fa988272988675988",
    "07598847218849818809f98869f988298988010988417988217988610188",
    "0509884579882579886501884d89880df1886df1882d818876818836f988",
    "56f9881689883e09887e79881e79885e0188"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock047InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock047InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock047OutputMaskData : ℕ :=
  sixthHex% [
    "6c5b4a7ef950586a703b886a14cc2f772e3551bd15431f0f1c642f0ec635",
    "2855154bb70f64f34a07115021827033206a6cfb4a0f1950298a703b286a",
    "652c2f778e35511d1532ff0f3f039e727b9e1046e12c7ee143d2af7feaaf",
    "1dd7d050afd01138be2d00be4f3dc10245c11ca98f51d18f33ecf00fd4f0",
    "250ee11936e17b0b9e36739e289fd065e7d007daaf3be2af7a75c1370dc1",
    "5530be6908be06a4f03a9cf058a18f15d98f3298be0ea0be6c9dc121e5c1",
    "3f098f72718f104cf02c74f06de39e209b9e42a6e17e9ee11132af2d0aaf",
    "4f37d0024fd059d5c114adc17690be4aa8be2504f0193cf07b018f36798f",
    "77eee14bd6e129eb9e64939e7a7fd03707d0553aaf6902af519ee806eb97",
    "64d6e842e3977290b754a5c83698b761edc855d98d73ecf211d18d46a4f2",
    "0797d250e2ad32dfd214eaad650b97433ee82103977676e83745c86030b7",
    "020dc82438b7100cf247798d2544f203718d3302ad1537d2770aad207fd2",
    "65a8b7439dc821a0b776d5c837e6e860939702aee8249b9710afd247daad",
    "25e7d203d2ad33a18d1594f277a98d20dcf2207dc87708b71535c83300b7",
    "0373972546e8477b97100ee8243aad020fd26032ad3747d27674f221018d",
    "433cf265098d0f45a86cae831de7b20f4c9933d2cd2179e65030d733dbfc",
    "7fdacd6d71e61c38d77fd3fc320da851e68320afb23204992c4e833ee5a8",
    "4fac992c47b26199e60272cd733bfc6190d72d91e64e7acd3f33fc2d98d7",
    "11068303ada872e499110fb24ed5a85c7e832d37b24edc990302cd60e9e6",
    "11a0d7030bfc4f0acd2ce1e65da8d74f03fc739da8613683107fb2739499",
    "1c9e837f75a80e3c991c97b22009e632a2cd43ebfc2000d76c01e67eaacd",
    "0fe3fc6c08d721d683423da833749921dfb2eae132890a19f84328eae803",
    "ab7e5cb9d577c89c46ab776d9a7e5788d57cf99c4d9a7766aaa139c94a12",
    "b80323aaa808a3d219b17932c03003a3db28930d77f0e65c81af6d930446",
    "a20d7cc1e657b0af66a2044de39212f13939807008e39b239b000889ab23",
    "f8e2129b0939abdf66c8344db97d7cabd657"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock047OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock047OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock047InputNumeratorData : ℕ :=
  sixthHex% [
    "8617e185f8618617e185f86185f8617df85f85f7df7df7e17df7e17e1861",
    "86185f85f7df85f7df7df7e186185f85f7df85f7df7df7e17e186186185f",
    "86185f85f7df7e186186185f86185f85f7df7df7e17e18617e186186185f",
    "86185f85f7df85f7df7df7e17e186186185f86185f85f7df86185f7e1861",
    "85f7df86185f85f7df86185f7df7e185f7df85f7df86185f7df7e185f7df",
    "7df7e185f7df7e18617df7e17df7e17e18617e186186185f85f7df7df7e1",
    "7df7e17e18617e186186185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock047InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock047InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock047OutputNumeratorData : ℕ :=
  sixthHex% [
    "86185f7e186186185f7e186185f7df86185f7df7e17e186185f7df7df7e1",
    "7e186186185f7df7e17e18617e186186185f7df7e17e186186185f85f7df",
    "7e186186185f7e17df8617e17df85f7e17df7df85f7e17df85f8617df85f",
    "7df85f7e17df85f8617df85f85f8617df85f8617e185f8617e17df7df85f",
    "7df85f85f8618617e17e17df7e17df7df85f7df85f85f86185f8618617e1",
    "7e17df7df85f7df85f85f8617e17df8617e17df85f7e17df7df85f7e17df",
    "85f8617df85f7df85f7e17df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock047OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock047OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block047_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock047Input a) =
      generatedSixthXiShortBlock047InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock047Output a) =
      generatedSixthXiShortBlock047OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock047Input a) =
      generatedSixthXiShortBlock047InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock047Output a) =
      generatedSixthXiShortBlock047OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block047_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock047InputMask a) =
      generatedSixthXiShortBlock047OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock047InputMask a)) *
      generatedSixthXiShortBlock047InputNumerator a =
        generatedSixthXiShortBlock047OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block047_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock047Input a
    let y := generatedSixthXiShortBlock047Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block047_cache a
  have hs := generatedSixth_xi_short_block047_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block047_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock047Input a
    let y := generatedSixthXiShortBlock047Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block047_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block047_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock047Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block047_certificate a).1
    (generatedSixth_xi_short_block047_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
