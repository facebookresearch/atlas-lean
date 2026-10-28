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
def generatedSixthXiShortBlock053Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inl 398,
    Sum.inr (Sum.inl (203, 9)),
    Sum.inl 445,
    Sum.inr (Sum.inl (203, 11)),
    Sum.inr (Sum.inl (203, 12)),
    Sum.inl 418,
    Sum.inr (Sum.inl (203, 14)),
    Sum.inl 495,
    Sum.inr (Sum.inl (203, 26)),
    Sum.inl 29,
    Sum.inr (Sum.inl (203, 24)),
    Sum.inl 20,
    Sum.inl 325,
    Sum.inr (Sum.inl (203, 53)),
    Sum.inl 316,
    Sum.inr (Sum.inl (203, 55)),
    Sum.inr (Sum.inl (203, 18)),
    Sum.inl 0,
    Sum.inr (Sum.inl (203, 58)),
    Sum.inl 43,
    Sum.inl 58,
    Sum.inr (Sum.inl (203, 61)),
    Sum.inl 339,
    Sum.inr (Sum.inl (203, 21)),
    Sum.inl 444,
    Sum.inr (Sum.inl (203, 33)),
    Sum.inl 399,
    Sum.inr (Sum.inl (203, 35)),
    Sum.inr (Sum.inl (203, 36)),
    Sum.inl 494,
    Sum.inr (Sum.inl (203, 38)),
    Sum.inl 419,
    Sum.inl 69,
    Sum.inr (Sum.inl (203, 41)),
    Sum.inl 458,
    Sum.inr (Sum.inl (203, 1)),
    Sum.inr (Sum.inl (203, 44)),
    Sum.inl 89,
    Sum.inr (Sum.inl (203, 4)),
    Sum.inl 550,
    Sum.inr (Sum.inr (255, 22)),
    Sum.inr (Sum.inr (126, 22)),
    Sum.inr (Sum.inr (63, 1)),
    Sum.inr (Sum.inr (190, 1)),
    Sum.inr (Sum.inr (352, 22)),
    Sum.inr (Sum.inr (481, 22)),
    Sum.inr (Sum.inr (416, 1)),
    Sum.inr (Sum.inr (289, 1)),
    Sum.inr (Sum.inr (363, 22)),
    Sum.inr (Sum.inr (490, 22)),
    Sum.inr (Sum.inr (427, 1)),
    Sum.inr (Sum.inr (298, 1)),
    Sum.inr (Sum.inr (244, 22)),
    Sum.inr (Sum.inr (117, 22)),
    Sum.inr (Sum.inr (52, 1)),
    Sum.inr (Sum.inr (181, 1)),
    Sum.inr (Sum.inr (181, 22)),
    Sum.inr (Sum.inr (52, 22)),
    Sum.inr (Sum.inr (117, 1)),
    Sum.inr (Sum.inr (244, 1)),
    Sum.inr (Sum.inr (298, 22)),
    Sum.inr (Sum.inr (427, 22)),
    Sum.inr (Sum.inr (490, 1)),
    Sum.inr (Sum.inr (363, 1)),
    Sum.inr (Sum.inr (289, 22)),
    Sum.inr (Sum.inr (416, 22)),
    Sum.inr (Sum.inr (481, 1)),
    Sum.inr (Sum.inr (352, 1)),
    Sum.inr (Sum.inr (190, 22)),
    Sum.inr (Sum.inr (63, 22)),
    Sum.inr (Sum.inr (126, 1)),
    Sum.inr (Sum.inr (255, 1)),
    Sum.inr (Sum.inr (63, 11)),
    Sum.inr (Sum.inr (190, 11)),
    Sum.inr (Sum.inr (255, 15)),
    Sum.inr (Sum.inr (126, 15)),
    Sum.inr (Sum.inr (416, 11)),
    Sum.inr (Sum.inr (289, 11)),
    Sum.inr (Sum.inr (352, 15)),
    Sum.inr (Sum.inr (481, 15)),
    Sum.inr (Sum.inr (427, 11)),
    Sum.inr (Sum.inr (298, 11)),
    Sum.inr (Sum.inr (363, 15)),
    Sum.inr (Sum.inr (490, 15)),
    Sum.inr (Sum.inr (52, 11)),
    Sum.inr (Sum.inr (181, 11)),
    Sum.inr (Sum.inr (244, 15)),
    Sum.inr (Sum.inr (117, 15)),
    Sum.inr (Sum.inr (117, 11)),
    Sum.inr (Sum.inr (244, 11)),
    Sum.inr (Sum.inr (181, 15)),
    Sum.inr (Sum.inr (52, 15)),
    Sum.inr (Sum.inr (490, 11)),
    Sum.inr (Sum.inr (363, 11)),
    Sum.inr (Sum.inr (298, 15)),
    Sum.inr (Sum.inr (427, 15)),
    Sum.inr (Sum.inr (481, 11)),
    Sum.inr (Sum.inr (352, 11)),
    Sum.inr (Sum.inr (289, 15)),
    Sum.inr (Sum.inr (416, 15)),
    Sum.inr (Sum.inr (126, 11)),
    Sum.inr (Sum.inr (255, 11)),
    Sum.inr (Sum.inr (190, 15)),
    Sum.inr (Sum.inr (63, 15)),
    Sum.inr (Sum.inr (497, 11)),
    Sum.inr (Sum.inr (174, 1)),
    Sum.inr (Sum.inr (506, 11)),
    Sum.inr (Sum.inr (165, 1)),
    Sum.inr (Sum.inr (239, 11)),
    Sum.inr (Sum.inr (432, 1)),
    Sum.inr (Sum.inr (228, 11)),
    Sum.inr (Sum.inr (443, 1)),
    Sum.inr (Sum.inr (110, 11)),
    Sum.inr (Sum.inr (305, 1)),
    Sum.inr (Sum.inr (101, 11)),
    Sum.inr (Sum.inr (314, 1)),
    Sum.inr (Sum.inr (368, 11)),
    Sum.inr (Sum.inr (47, 1)),
    Sum.inr (Sum.inr (379, 11)),
    Sum.inr (Sum.inr (36, 1)),
    Sum.inr (Sum.inr (36, 11)),
    Sum.inr (Sum.inr (379, 1)),
    Sum.inr (Sum.inr (47, 11)),
    Sum.inr (Sum.inr (368, 1)),
    Sum.inr (Sum.inr (314, 11)),
    Sum.inr (Sum.inr (101, 1)),
    Sum.inr (Sum.inr (305, 11)),
    Sum.inr (Sum.inr (110, 1)),
    Sum.inr (Sum.inr (443, 11)),
    Sum.inr (Sum.inr (228, 1)),
    Sum.inr (Sum.inr (432, 11)),
    Sum.inr (Sum.inr (239, 1)),
    Sum.inr (Sum.inr (165, 11)),
    Sum.inr (Sum.inr (506, 1)),
    Sum.inr (Sum.inr (174, 11)),
    Sum.inr (Sum.inr (497, 1)),
    Sum.inr (Sum.inr (174, 15)),
    Sum.inr (Sum.inr (497, 22)),
    Sum.inr (Sum.inr (165, 15)),
    Sum.inr (Sum.inr (506, 22)),
    Sum.inr (Sum.inr (432, 15)),
    Sum.inr (Sum.inr (239, 22)),
    Sum.inr (Sum.inr (443, 15)),
    Sum.inr (Sum.inr (228, 22)),
    Sum.inr (Sum.inr (305, 15)),
    Sum.inr (Sum.inr (110, 22)),
    Sum.inr (Sum.inr (314, 15)),
    Sum.inr (Sum.inr (101, 22)),
    Sum.inr (Sum.inr (47, 15)),
    Sum.inr (Sum.inr (368, 22)),
    Sum.inr (Sum.inr (36, 15)),
    Sum.inr (Sum.inr (379, 22)),
    Sum.inr (Sum.inr (379, 15)),
    Sum.inr (Sum.inr (36, 22)),
    Sum.inr (Sum.inr (368, 15)),
    Sum.inr (Sum.inr (47, 22)),
    Sum.inr (Sum.inr (101, 15)),
    Sum.inr (Sum.inr (314, 22)),
    Sum.inr (Sum.inr (110, 15)),
    Sum.inr (Sum.inr (305, 22)),
    Sum.inr (Sum.inr (228, 15)),
    Sum.inr (Sum.inr (443, 22)),
    Sum.inr (Sum.inr (239, 15)),
    Sum.inr (Sum.inr (432, 22)),
    Sum.inr (Sum.inr (506, 15)),
    Sum.inr (Sum.inr (165, 22)),
    Sum.inr (Sum.inr (497, 15)),
    Sum.inr (Sum.inr (174, 22)),
    Sum.inr (Sum.inr (504, 22)),
    Sum.inr (Sum.inr (312, 1)),
    Sum.inr (Sum.inr (108, 22)),
    Sum.inr (Sum.inr (172, 1)),
    Sum.inr (Sum.inr (312, 11)),
    Sum.inr (Sum.inr (504, 15)),
    Sum.inr (Sum.inr (172, 11)),
    Sum.inr (Sum.inr (108, 15)),
    Sum.inr (Sum.inr (312, 15)),
    Sum.inr (Sum.inr (504, 11)),
    Sum.inr (Sum.inr (172, 15)),
    Sum.inr (Sum.inr (108, 11)),
    Sum.inr (Sum.inr (504, 1)),
    Sum.inr (Sum.inr (312, 22)),
    Sum.inr (Sum.inr (108, 1)),
    Sum.inr (Sum.inr (172, 22)),
    Sum.inr (Sum.inr (103, 22)),
    Sum.inr (Sum.inr (167, 1)),
    Sum.inr (Sum.inr (499, 22)),
    Sum.inr (Sum.inr (307, 1)),
    Sum.inr (Sum.inr (167, 11)),
    Sum.inr (Sum.inr (103, 15)),
    Sum.inr (Sum.inr (307, 11)),
    Sum.inr (Sum.inr (499, 15)),
    Sum.inr (Sum.inr (167, 15)),
    Sum.inr (Sum.inr (103, 11)),
    Sum.inr (Sum.inr (307, 15)),
    Sum.inr (Sum.inr (499, 11)),
    Sum.inr (Sum.inr (103, 1)),
    Sum.inr (Sum.inr (167, 22)),
    Sum.inr (Sum.inr (499, 1)),
    Sum.inr (Sum.inr (307, 22)),
    Sum.inr (Sum.inr (434, 22)),
    Sum.inr (Sum.inr (370, 1)),
    Sum.inr (Sum.inr (38, 22)),
    Sum.inr (Sum.inr (230, 1)),
    Sum.inr (Sum.inr (370, 11)),
    Sum.inr (Sum.inr (434, 15)),
    Sum.inr (Sum.inr (230, 11)),
    Sum.inr (Sum.inr (38, 15)),
    Sum.inr (Sum.inr (370, 15)),
    Sum.inr (Sum.inr (434, 11)),
    Sum.inr (Sum.inr (230, 15)),
    Sum.inr (Sum.inr (38, 11)),
    Sum.inr (Sum.inr (434, 1)),
    Sum.inr (Sum.inr (370, 22)),
    Sum.inr (Sum.inr (38, 1)),
    Sum.inr (Sum.inr (230, 22)),
    Sum.inr (Sum.inr (45, 22)),
    Sum.inr (Sum.inr (237, 1)),
    Sum.inr (Sum.inr (441, 22)),
    Sum.inr (Sum.inr (377, 1)),
    Sum.inr (Sum.inr (237, 11)),
    Sum.inr (Sum.inr (45, 15)),
    Sum.inr (Sum.inr (377, 11)),
    Sum.inr (Sum.inr (441, 15)),
    Sum.inr (Sum.inr (237, 15)),
    Sum.inr (Sum.inr (45, 11)),
    Sum.inr (Sum.inr (377, 15)),
    Sum.inr (Sum.inr (441, 11)),
    Sum.inr (Sum.inr (45, 1)),
    Sum.inr (Sum.inr (237, 22)),
    Sum.inr (Sum.inr (441, 1)),
    Sum.inr (Sum.inr (377, 22)),
    Sum.inr (Sum.inr (83, 22)),
    Sum.inr (Sum.inr (217, 1)),
    Sum.inr (Sum.inr (25, 22)),
    Sum.inr (Sum.inr (147, 1)),
    Sum.inr (Sum.inr (397, 22)),
    Sum.inr (Sum.inr (263, 1)),
    Sum.inr (Sum.inr (455, 22)),
    Sum.inr (Sum.inr (333, 1)),
    Sum.inr (Sum.inr (390, 22)),
    Sum.inr (Sum.inr (268, 1)),
    Sum.inr (Sum.inr (460, 22)),
    Sum.inr (Sum.inr (326, 1)),
    Sum.inr (Sum.inr (88, 22)),
    Sum.inr (Sum.inr (210, 1)),
    Sum.inr (Sum.inr (18, 22)),
    Sum.inr (Sum.inr (152, 1)),
    Sum.inr (Sum.inr (152, 22)),
    Sum.inr (Sum.inr (18, 1)),
    Sum.inr (Sum.inr (210, 22)),
    Sum.inr (Sum.inr (88, 1)),
    Sum.inr (Sum.inr (326, 22)),
    Sum.inr (Sum.inr (460, 1)),
    Sum.inr (Sum.inr (268, 22)),
    Sum.inr (Sum.inr (390, 1))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock053Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨13568 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock053InputMaskData : ℕ :=
  sixthHex% [
    "7be3f35b33f36b33f34bebf333c3f3131bf3231bf303cbf33ff3f31f23f3",
    "2f23f30ffbf377d3f3570bf3670bf347dbf37bd3f35b0bf36b0bf34bdbf3",
    "33fbf3132bf3232bf303f3f3560d78007d78688d783ef578639d7835e578",
    "5d15780b65785fad7809d5786125783755786a35783c457854b57802cd78",
    "59cd780fb5786745783135786c55783a257852d57804ad78506578061578",
    "6ee578389d7865f578338d785b7d780d0d78200d787675781e857848f578",
    "15957843e5782b15787d6d7829a5787fd578172578415d781c35784a4d78",
    "22bd7874cd782fc57879b578114578473d781a55784c2d7824dd7872ad78",
    "266578701d7818ed784e9d7813fd78458d782d7d787b057841cd71187d71",
    "708d71293571389d7161257109d5715065717a9d712325714bd571126571",
    "03c5715a75713285716b3d71799d7120257148d57111657100c571597571",
    "318571683d7142c5711b75717385712a3d713b9571622d710add71536d71",
    "47ad711e157176e5712f55713ef5716745710fb571560d717cf571254571",
    "4db571140d7105a5715c1d7134ed716d5d717ff5712645714eb571170d71",
    "06a5715f1d7137ed716e5d7144a5711d1d7175ed712c5d713dfd71644d71",
    "0cbd7155057168315f7de15f1de15f08395f3d115f28c95f48c95f5d195f",
    "75115f60c95f00c95f15195f20395f35e95f55e95f40315f7c015f69d95f",
    "09d95f1c095f29295f3cf95f5cf95f49215f61295f74f95f14f95f01215f",
    "34095f21d15f41d15f54015f7e015f6bd95f0bd95f1e095f2b295f3ef95f",
    "5ef95f4b215f63295f76f95f16f95f03215f36095f23d15f43d15f56015f",
    "6a395f7fe95f1fe95f0a315f3f195f2ac15f4ac15f5f115f77195f62c15f",
    "02c15f17115f22315f37e15f57e15f42395f51a1317cd1311cd13131a931",
    "3c31311149317149315c39317f31315249313249311f393112a9313fd931",
    "5fd93172a1315601317b79311b79313609313b993116e93176e9315b9131",
    "78993155e93135e9311891311509313871315871317501314301316e7931",
    "0e79312309312e993103e93163e9314e9131"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock053InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock053InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock053OutputMaskData : ℕ :=
  sixthHex% [
    "eb8636f9842cdf170cbc5516aab958c9fb42ef6862fd6a78b01a78a21862",
    "848b42e7c958f1251692670cb4f42ca6f636c82d1dab6f078dfc279ffe3d",
    "f85273ea5069ccc349af81538cedc9cc0ee99f339dae90bdafeee99e4dc9",
    "cd70bd8d939d93dee9a27dc9f140bdb1a39dc19dc9817ee9d2439de3e0bd",
    "9b7b96aad8b6f9e5c2b906e2c938b689db96dae6e2eb45c2f508b6b5eb96",
    "e6d6e2d775c2d60b96e7a8b6b495c2f476e2deacf3ef0fd3bc32a7fcd187",
    "8cefd3cc0cf39f3187ae92a7b0dfd3f03cf3a3018792a2a793dcf3a27fd3",
    "f142a7b1a187b87aacf8998caba4f89a07d89b798caadaacf9e7d8b904f8",
    "a7498c96eaacc5d7d88534f8f50aacb5e98ce6d4f8d777d8bda2aeead7d1",
    "b9eaa59fdfdadb7ee0fd4b9fae76ebf903949eacf1b8998eeba4fabcd185",
    "8930bfde45c08d78b4ab4dcbb9e5cb9fd0b4ccedc09b98bfae7985f90cfa",
    "aa318e8c04f1ebab94bcdeebefe39fc9d6e08d77daab42a5f87fd1af0aae",
    "b507d19332aec00fda977aa5a29b9ff5eee0a6d39480e6ebe7498eb03cf1",
    "e30185c534fa8195c0a7a0bff49dcba3e8b4c000b49775cbc448bfe27dc0",
    "a6dcfa80e985d3d4f184a18ee30eebc53b949606e0c1739ff492a5a3e7da",
    "f0daaed6efd1a398dfb192cec0dbffa391eeeeee808da491fceda0eee7b1",
    "93e68bf0ac9a81e5ab93efbaafd0d4bddac5cc93f4afd9e593e9e5f0a3f4",
    "81eac593e0d4afdfbabdd5abcc9c9aafd68bd2d7b1c0dda0b19491d2de80",
    "9fa1eefcebff8da2ce9fa8dfa33bffc071eeb138dfa332ce9f0da08d07b1",
    "fc4e809f0491e205abf00fba81468be20c9aaf73f4cc39e5bd70d4af7ac5",
    "e20ac5f000d48149e5e203f4af7c9acc368bbd7fbaaf75abd27491b13e80",
    "c077b1d27da0ee42cefc48df8d01eeee4bff3600000a31317b7800360931",
    "4ad13107a00076e9314ad80018980055e93124a000189131150931293800",
    "58713115000020e9316d98001cd13120e0002d78001149316000002d7131",
    "7f31314300003249317f380003e0004e91313fd80003e93124a80069d931",
    "18900024a131293931150800644131293000"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock053OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock053OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock053InputNumeratorData : ℕ :=
  sixthHex% [
    "7df85f85f8618617e17e17df85f8618617e185f8617df85f8617e185f861",
    "8617e185f8617e17df8617e18617e185f8617e17df8617e17e17df8617e1",
    "7df85f7e17df7e17df7df85f8617e17e17df8617e17e17df85f8618617e1",
    "7df85f85f8617e17df7df85f7e17df7df85f8617e17e17df85f7df86185f",
    "86185f7e18617df7e185f7df85f7df86185f7df7e185f7df85f7df86185f",
    "7e18617df7e17df7e185f7df86185f7e186185f7df86185f7e18617df7e1",
    "86185f7e18617e18617df7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock053InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock053InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock053OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617e185f8618617e185f8617e17df8617e185f8617df85f8617e185f861",
    "7df85f7e17df85f8617df85f7df85f7e17df85f8617df85f7e17df8617e1",
    "7df85f7e17df85f7df86185f7df7e185f7df86185f7e186185f7df86185f",
    "86185f7e186185f7df86185f7e18617df7e186185f7e18618617e17e17df",
    "85f8618617e17e17df7df85f8617e17e17df7e17df7df85f8617e17e17df",
    "7df85f85f8617e17df7df85f8617e17e17df7e17df7df85f85f8618617e1",
    "8617e17e17df85f8618617e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock053OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock053OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block053_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock053Input a) =
      generatedSixthXiShortBlock053InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock053Output a) =
      generatedSixthXiShortBlock053OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock053Input a) =
      generatedSixthXiShortBlock053InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock053Output a) =
      generatedSixthXiShortBlock053OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block053_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock053InputMask a) =
      generatedSixthXiShortBlock053OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock053InputMask a)) *
      generatedSixthXiShortBlock053InputNumerator a =
        generatedSixthXiShortBlock053OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block053_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock053Input a
    let y := generatedSixthXiShortBlock053Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block053_cache a
  have hs := generatedSixth_xi_short_block053_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block053_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock053Input a
    let y := generatedSixthXiShortBlock053Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block053_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block053_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock053Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block053_certificate a).1
    (generatedSixth_xi_short_block053_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
