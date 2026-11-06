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
def generatedSixthXiShortBlock059Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (68, 5)),
    Sum.inr (Sum.inl (68, 17)),
    Sum.inr (Sum.inl (137, 15)),
    Sum.inr (Sum.inl (137, 14)),
    Sum.inr (Sum.inl (227, 33)),
    Sum.inr (Sum.inl (227, 32)),
    Sum.inr (Sum.inl (159, 7)),
    Sum.inr (Sum.inl (159, 19)),
    Sum.inr (Sum.inl (79, 18)),
    Sum.inr (Sum.inl (79, 47)),
    Sum.inr (Sum.inl (181, 14)),
    Sum.inr (Sum.inl (181, 42)),
    Sum.inr (Sum.inl (51, 16)),
    Sum.inr (Sum.inl (51, 63)),
    Sum.inr (Sum.inl (109, 42)),
    Sum.inr (Sum.inl (109, 23)),
    Sum.inr (Sum.inl (159, 12)),
    Sum.inr (Sum.inl (159, 24)),
    Sum.inr (Sum.inl (227, 23)),
    Sum.inr (Sum.inl (227, 22)),
    Sum.inr (Sum.inl (137, 17)),
    Sum.inr (Sum.inl (137, 16)),
    Sum.inr (Sum.inl (68, 14)),
    Sum.inr (Sum.inl (68, 26)),
    Sum.inr (Sum.inl (181, 12)),
    Sum.inr (Sum.inl (181, 40)),
    Sum.inr (Sum.inl (79, 30)),
    Sum.inr (Sum.inl (79, 35)),
    Sum.inr (Sum.inl (109, 34)),
    Sum.inr (Sum.inl (109, 31)),
    Sum.inr (Sum.inl (51, 28)),
    Sum.inr (Sum.inl (51, 51)),
    Sum.inr (Sum.inl (227, 5)),
    Sum.inr (Sum.inl (227, 4)),
    Sum.inr (Sum.inl (159, 15)),
    Sum.inr (Sum.inl (159, 27)),
    Sum.inr (Sum.inl (68, 12)),
    Sum.inr (Sum.inl (68, 24)),
    Sum.inr (Sum.inl (137, 29)),
    Sum.inr (Sum.inl (137, 28)),
    Sum.inr (Sum.inl (94, 18)),
    Sum.inr (Sum.inl (160, 6)),
    Sum.inr (Sum.inl (122, 10)),
    Sum.inr (Sum.inl (180, 24)),
    Sum.inr (Sum.inl (50, 27)),
    Sum.inr (Sum.inl (96, 26)),
    Sum.inr (Sum.inl (69, 58)),
    Sum.inr (Sum.inl (228, 60)),
    Sum.inr (Sum.inl (94, 17)),
    Sum.inr (Sum.inl (160, 4)),
    Sum.inr (Sum.inl (122, 24)),
    Sum.inr (Sum.inl (180, 20)),
    Sum.inr (Sum.inl (50, 25)),
    Sum.inr (Sum.inl (96, 22)),
    Sum.inr (Sum.inl (69, 54)),
    Sum.inr (Sum.inl (228, 52)),
    Sum.inr (Sum.inl (160, 3)),
    Sum.inr (Sum.inl (94, 61)),
    Sum.inr (Sum.inl (180, 9)),
    Sum.inr (Sum.inl (122, 61)),
    Sum.inr (Sum.inl (96, 11)),
    Sum.inr (Sum.inl (50, 52)),
    Sum.inr (Sum.inl (228, 45)),
    Sum.inr (Sum.inl (69, 37)),
    Sum.inr (Sum.inl (160, 1)),
    Sum.inr (Sum.inl (94, 62)),
    Sum.inr (Sum.inl (180, 5)),
    Sum.inr (Sum.inl (122, 47)),
    Sum.inr (Sum.inl (96, 7)),
    Sum.inr (Sum.inl (50, 54)),
    Sum.inr (Sum.inl (228, 37)),
    Sum.inr (Sum.inl (69, 41)),
    Sum.inr (Sum.inl (50, 18)),
    Sum.inr (Sum.inl (96, 24)),
    Sum.inr (Sum.inl (69, 40)),
    Sum.inr (Sum.inl (228, 24)),
    Sum.inr (Sum.inl (94, 22)),
    Sum.inr (Sum.inl (160, 49)),
    Sum.inr (Sum.inl (122, 46)),
    Sum.inr (Sum.inl (180, 56)),
    Sum.inr (Sum.inl (50, 16)),
    Sum.inr (Sum.inl (96, 20)),
    Sum.inr (Sum.inl (69, 36)),
    Sum.inr (Sum.inl (228, 16)),
    Sum.inr (Sum.inl (94, 21)),
    Sum.inr (Sum.inl (160, 51)),
    Sum.inr (Sum.inl (122, 60)),
    Sum.inr (Sum.inl (180, 52)),
    Sum.inr (Sum.inl (96, 9)),
    Sum.inr (Sum.inl (50, 61)),
    Sum.inr (Sum.inl (228, 9)),
    Sum.inr (Sum.inl (69, 55)),
    Sum.inr (Sum.inl (160, 52)),
    Sum.inr (Sum.inl (94, 57)),
    Sum.inr (Sum.inl (180, 41)),
    Sum.inr (Sum.inl (122, 25)),
    Sum.inr (Sum.inl (96, 5)),
    Sum.inr (Sum.inl (50, 63)),
    Sum.inr (Sum.inl (228, 1)),
    Sum.inr (Sum.inl (69, 59)),
    Sum.inr (Sum.inl (160, 54)),
    Sum.inr (Sum.inl (94, 58)),
    Sum.inr (Sum.inl (180, 37)),
    Sum.inr (Sum.inl (122, 11)),
    Sum.inr (Sum.inl (93, 36)),
    Sum.inr (Sum.inl (65, 13)),
    Sum.inr (Sum.inl (65, 1)),
    Sum.inr (Sum.inl (93, 44)),
    Sum.inr (Sum.inl (136, 54)),
    Sum.inr (Sum.inl (49, 61)),
    Sum.inr (Sum.inl (49, 49)),
    Sum.inr (Sum.inl (136, 36)),
    Sum.inr (Sum.inl (189, 7)),
    Sum.inr (Sum.inl (95, 63)),
    Sum.inr (Sum.inl (95, 51)),
    Sum.inr (Sum.inl (189, 5)),
    Sum.inr (Sum.inl (198, 31)),
    Sum.inr (Sum.inl (229, 15)),
    Sum.inr (Sum.inl (229, 12)),
    Sum.inr (Sum.inl (198, 29)),
    Sum.inr (Sum.inl (189, 11)),
    Sum.inr (Sum.inl (95, 47)),
    Sum.inr (Sum.inl (95, 35)),
    Sum.inr (Sum.inl (189, 9)),
    Sum.inr (Sum.inl (198, 55)),
    Sum.inr (Sum.inl (229, 23)),
    Sum.inr (Sum.inl (229, 20)),
    Sum.inr (Sum.inl (198, 53)),
    Sum.inr (Sum.inl (93, 31)),
    Sum.inr (Sum.inl (65, 15)),
    Sum.inr (Sum.inl (65, 3)),
    Sum.inr (Sum.inl (93, 23)),
    Sum.inr (Sum.inl (136, 23)),
    Sum.inr (Sum.inl (49, 63)),
    Sum.inr (Sum.inl (49, 51)),
    Sum.inr (Sum.inl (136, 5)),
    Sum.inr (Sum.inl (93, 54)),
    Sum.inr (Sum.inl (65, 18)),
    Sum.inr (Sum.inl (65, 30)),
    Sum.inr (Sum.inl (93, 62)),
    Sum.inr (Sum.inl (136, 62)),
    Sum.inr (Sum.inl (49, 28)),
    Sum.inr (Sum.inl (49, 16)),
    Sum.inr (Sum.inl (136, 44)),
    Sum.inr (Sum.inl (189, 24)),
    Sum.inr (Sum.inl (95, 29)),
    Sum.inr (Sum.inl (95, 17)),
    Sum.inr (Sum.inl (189, 26)),
    Sum.inr (Sum.inl (198, 14)),
    Sum.inr (Sum.inl (229, 47)),
    Sum.inr (Sum.inl (229, 44)),
    Sum.inr (Sum.inl (198, 12)),
    Sum.inr (Sum.inl (189, 20)),
    Sum.inr (Sum.inl (95, 13)),
    Sum.inr (Sum.inl (95, 1)),
    Sum.inr (Sum.inl (189, 22)),
    Sum.inr (Sum.inl (198, 38)),
    Sum.inr (Sum.inl (229, 55)),
    Sum.inr (Sum.inl (229, 52)),
    Sum.inr (Sum.inl (198, 36)),
    Sum.inr (Sum.inl (93, 13)),
    Sum.inr (Sum.inl (65, 16)),
    Sum.inr (Sum.inl (65, 28)),
    Sum.inr (Sum.inl (93, 5)),
    Sum.inr (Sum.inl (136, 31)),
    Sum.inr (Sum.inl (49, 30)),
    Sum.inr (Sum.inl (49, 18)),
    Sum.inr (Sum.inl (136, 13)),
    Sum.inr (Sum.inl (92, 31)),
    Sum.inr (Sum.inl (107, 63)),
    Sum.inr (Sum.inl (176, 48)),
    Sum.inr (Sum.inl (156, 31)),
    Sum.inr (Sum.inl (73, 22)),
    Sum.inr (Sum.inl (54, 45)),
    Sum.inr (Sum.inl (111, 29)),
    Sum.inr (Sum.inl (230, 11)),
    Sum.inr (Sum.inl (92, 28)),
    Sum.inr (Sum.inl (107, 45)),
    Sum.inr (Sum.inl (176, 50)),
    Sum.inr (Sum.inl (156, 19)),
    Sum.inr (Sum.inl (73, 20)),
    Sum.inr (Sum.inl (54, 33)),
    Sum.inr (Sum.inl (111, 17)),
    Sum.inr (Sum.inl (230, 3)),
    Sum.inr (Sum.inl (73, 31)),
    Sum.inr (Sum.inl (54, 63)),
    Sum.inr (Sum.inl (111, 63)),
    Sum.inr (Sum.inl (230, 31)),
    Sum.inr (Sum.inl (92, 15)),
    Sum.inr (Sum.inl (107, 23)),
    Sum.inr (Sum.inl (176, 7)),
    Sum.inr (Sum.inl (156, 15)),
    Sum.inr (Sum.inl (73, 29)),
    Sum.inr (Sum.inl (54, 51)),
    Sum.inr (Sum.inl (111, 51)),
    Sum.inr (Sum.inl (230, 23)),
    Sum.inr (Sum.inl (92, 12)),
    Sum.inr (Sum.inl (107, 5)),
    Sum.inr (Sum.inl (176, 5)),
    Sum.inr (Sum.inl (156, 3)),
    Sum.inr (Sum.inl (176, 17)),
    Sum.inr (Sum.inl (156, 61)),
    Sum.inr (Sum.inl (92, 40)),
    Sum.inr (Sum.inl (107, 59)),
    Sum.inr (Sum.inl (111, 35)),
    Sum.inr (Sum.inl (230, 41)),
    Sum.inr (Sum.inl (73, 57)),
    Sum.inr (Sum.inl (54, 13)),
    Sum.inr (Sum.inl (176, 19)),
    Sum.inr (Sum.inl (156, 49)),
    Sum.inr (Sum.inl (92, 43)),
    Sum.inr (Sum.inl (107, 41)),
    Sum.inr (Sum.inl (111, 47)),
    Sum.inr (Sum.inl (230, 33)),
    Sum.inr (Sum.inl (73, 59)),
    Sum.inr (Sum.inl (54, 1)),
    Sum.inr (Sum.inl (111, 1)),
    Sum.inr (Sum.inl (230, 61)),
    Sum.inr (Sum.inl (73, 48)),
    Sum.inr (Sum.inl (54, 31)),
    Sum.inr (Sum.inl (176, 38)),
    Sum.inr (Sum.inl (156, 45)),
    Sum.inr (Sum.inl (92, 56)),
    Sum.inr (Sum.inl (107, 19)),
    Sum.inr (Sum.inl (111, 13)),
    Sum.inr (Sum.inl (230, 53)),
    Sum.inr (Sum.inl (73, 50)),
    Sum.inr (Sum.inl (54, 19)),
    Sum.inr (Sum.inl (176, 36)),
    Sum.inr (Sum.inl (156, 33)),
    Sum.inr (Sum.inl (92, 59)),
    Sum.inr (Sum.inl (107, 1)),
    Sum.inr (Sum.inr (225, 0)),
    Sum.inr (Sum.inr (160, 1)),
    Sum.inr (Sum.inr (96, 2)),
    Sum.inr (Sum.inr (42, 3)),
    Sum.inr (Sum.inr (511, 4)),
    Sum.inr (Sum.inr (500, 5)),
    Sum.inr (Sum.inr (511, 6)),
    Sum.inr (Sum.inr (511, 7)),
    Sum.inr (Sum.inr (225, 8)),
    Sum.inr (Sum.inr (96, 9)),
    Sum.inr (Sum.inr (42, 10)),
    Sum.inr (Sum.inr (160, 11)),
    Sum.inr (Sum.inr (42, 12)),
    Sum.inr (Sum.inr (225, 13)),
    Sum.inr (Sum.inr (96, 14)),
    Sum.inr (Sum.inr (160, 15)),
    Sum.inr (Sum.inr (500, 16)),
    Sum.inr (Sum.inr (500, 17)),
    Sum.inr (Sum.inr (511, 18)),
    Sum.inr (Sum.inr (500, 19)),
    Sum.inr (Sum.inr (42, 20)),
    Sum.inr (Sum.inr (96, 21)),
    Sum.inr (Sum.inr (160, 22)),
    Sum.inr (Sum.inr (225, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock059Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨15104 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock059InputMaskData : ℕ :=
  sixthHex% [
    "9b7000ad7000b67000c07000a7b000b9b0009eb000c0b000bfd00095d000",
    "aad000c0d00083e00081e00082e000c0e0008cf00084f00088f000c0f000",
    "f00000d00000e0000080000054c6e06d76e00d76e034cee01d76e024cee0",
    "44cee07d7ee06186e0583ee0383ee0018ee0283ee0118ee0718ee04836e0",
    "6c96e0552ee0352ee00c9ee0252ee01c9ee07c9ee04526e059dee0606ee0",
    "006ee039d6e0106ee029d6e049d6e07066e052a6e06b1ee00b1ee032aee0",
    "1b1ee022aee042aee07b16e067eee05e5ee03e5ee007e6e02e5ee017e6e0",
    "77e6e04e56e06afee0534ee0334ee00af6e0234ee01af6e07af6e04346e0",
    "5fbee06606e00606e03fb6e01606e02fb6e04fb6e0760ee0788863510863",
    "5908637080631518633c90633490631d10635418637d90637590635c1063",
    "3980631000631800633188631528633ca06334a0631d206378b063513063",
    "59306370b86339b06310306318306331b8635420637da86375a8635c2863",
    "6a286343a0634ba06362206307b0632e30632630630fb86346b0636f3063",
    "6730634eb8632b206302a8630aa8632328630780632e00632600630f8863",
    "6a10634398634b98636218632b10630298630a98632318634688636f0863",
    "6708634e806305f6833c46835c468365fe834c468375fe8315fe832c4e83",
    "38b683010e83610e8358be83710e8348be8328be831106837ca683451e83",
    "251e831cae83351e830cae836cae8355168341ee83785e83185e8321e683",
    "085e8331e68351e6836856837c9683452e83252e831c9e83352e830c9e83",
    "6c9e8355268341de83786e83186e8321d683086e8331d68351d683686683",
    "05ce833c7e835c7e8365c6834c7e8375c68315c6832c7683388e83013683",
    "613683588683713683488683288683113e83660ee8007ee85c8ee83af6e8",
    "519ee837e6e86b16e80d66e86faee809d6e85526e83356e85836e83e46e8",
    "62b6e804cee869cee80fb6e85346e83536e85e56e83826e864d6e802aee8",
    "6066e80616e85ae6e83c9ee857f6e8318ee86d7ee80b0ee8100ee87676e8",
    "2a86e84cf6e82796e841e6e81d16e87b6ee8"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock059InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock059InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock059OutputMaskData : ℕ :=
  sixthHex% [
    "dff391f8b2a0f52980a768bac9bfd4e2bfdff0bfd4aebfd4ea1aa0d68980",
    "ee5b91a7c8bad62aa0e6f8bac1b180846391d7f7dfdfffdfe6f7d49bffdf",
    "9710ba935980b5caa0c483916ba4fa4d98b43cd1856badcb1e0b9f4977d1",
    "383ee01e02ae5eecfa0990b478d9855ee5cb5a039f7c3fd10d76e05a0aae",
    "6fe39f389fd149d6e06feaae6b0cfa4d30b43c79856b05cb2beb9f0dd7d1",
    "7c9ee02be2ae5e44fa0938b47871855e4dcb630185347dcb4534fa6308b4",
    "67eee041d2ae309b9f67e7d12709850135cb707cfa2700b452a6e005daae",
    "74939f52afd11606e0303aae41739f160fd163a98534d5cb459cfa63a0b4",
    "234ee07432ae057b9f2347d127a185019dcb70d4fa27a8b4145706331a79",
    "3b12796d1f066886373e8b4836834811ce370a1d1c5c106354186373551c",
    "078c2d20c15228c9527ec42d4b2d1c1d206315286332651c46bc2d61f152",
    "69f9523ff42d242706036a790b62795d6f0658f6370efb4806f34821be37",
    "06ff0650f27958fa797fb7060b6e372c2348242b4872263769f51c4eb863",
    "46b06310bd1c15242d4329524b21526c6c2d28c51c0f8863078063518d1c",
    "54142d0219520a11522d5c2d368f06608279688a794fc7063b1e371c5348",
    "145b484256370a55a82c69e65d20d70a5c997ffacd28868359cfb27ff3fc",
    "3715a86069e61120d7371c9933facd15c683648fb233f3fc6c89e63bf5a8",
    "4abc996c80d76866834e5acd3f13fc686fb22089e606b5a877fc992080d7",
    "552683025acd7313fc552fb24f22cd185e836917b24f2bfc4bcda86df1e6",
    "1cb8d74bc4990322cd251e835457b2032bfc768da821f1e650b8d7768499",
    "58be837e82cd0fcbfc58b7b22d11e67a6da80b24992d18d765fe833282cd",
    "43cbfc65f7b26111e6472da83664996118d70ad18d6ca18d280fd23f3fd2",
    "1900b70e30b74a9ee82ceee815e2ad02d2ad467cf2200cf2777397110397",
    "55adc8429dc81d47d20a77d24ed98d28a98d7fd6e819a6e85d08b74a38b7",
    "7334f21544f251eaad46daad60e5c877d5c8337b97550b975890b74fa0b7",
    "0b0ee86d7ee83a018d5c718d18dfd20fefd2"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock059OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock059OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock059InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17e17df8617e18617e185f861",
    "7df85f7e17df7e17df8617e17df85f7e17df7e17df8617e185f8617df85f",
    "7df85f7e17df85f7df86185f86185f7e18617df7e185f7df85f7df86185f",
    "86185f7e18617e18617df7e185f7df86185f86185f7e18617e17df8617e1",
    "7df85f7e17df8617e185f8617e17df8617e17df85f7e17df85f8617df85f",
    "7e17df8617e17df85f7e17df7e18617df7e17df7e185f7df7df7e185f7df",
    "85f7df86185f7df7e185f7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock059InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock059InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock059OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7e185f7df7e18617df7e1",
    "85f7df86185f7df7e185f7df7e18617df7e186185f7e18617df7e185f7df",
    "7e18617df7e17e17df7df85f7df85f85f8618617e17e17df7e17df7df85f",
    "8617e17e17df7e17df7df85f85f8618617e18617e17e17df7df7e185f7df",
    "7e18617df7e17e18617df7e186185f7e186185f7df86185f7df7e185f7df",
    "7df7e185f7df7e18617df7e17e17df8617e18617e185f8617df85f7e17df",
    "7e17df8617e18617e185f861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock059OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock059OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block059_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock059Input a) =
      generatedSixthXiShortBlock059InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock059Output a) =
      generatedSixthXiShortBlock059OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock059Input a) =
      generatedSixthXiShortBlock059InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock059Output a) =
      generatedSixthXiShortBlock059OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block059_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock059InputMask a) =
      generatedSixthXiShortBlock059OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock059InputMask a)) *
      generatedSixthXiShortBlock059InputNumerator a =
        generatedSixthXiShortBlock059OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block059_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock059Input a
    let y := generatedSixthXiShortBlock059Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block059_cache a
  have hs := generatedSixth_xi_short_block059_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block059_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock059Input a
    let y := generatedSixthXiShortBlock059Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block059_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block059_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock059Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block059_certificate a).1
    (generatedSixth_xi_short_block059_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
