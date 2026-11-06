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
def generatedSixthXiShortBlock056Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (350, 8)),
    Sum.inr (Sum.inr (350, 23)),
    Sum.inr (Sum.inr (479, 0)),
    Sum.inr (Sum.inr (479, 13)),
    Sum.inr (Sum.inr (75, 0)),
    Sum.inr (Sum.inr (75, 13)),
    Sum.inr (Sum.inr (202, 8)),
    Sum.inr (Sum.inr (202, 23)),
    Sum.inr (Sum.inr (139, 13)),
    Sum.inr (Sum.inr (139, 0)),
    Sum.inr (Sum.inr (10, 23)),
    Sum.inr (Sum.inr (10, 8)),
    Sum.inr (Sum.inr (414, 23)),
    Sum.inr (Sum.inr (414, 8)),
    Sum.inr (Sum.inr (287, 13)),
    Sum.inr (Sum.inr (287, 0)),
    Sum.inr (Sum.inr (405, 23)),
    Sum.inr (Sum.inr (405, 8)),
    Sum.inr (Sum.inr (276, 13)),
    Sum.inr (Sum.inr (276, 0)),
    Sum.inr (Sum.inr (128, 13)),
    Sum.inr (Sum.inr (128, 0)),
    Sum.inr (Sum.inr (1, 23)),
    Sum.inr (Sum.inr (1, 8)),
    Sum.inr (Sum.inr (139, 8)),
    Sum.inr (Sum.inr (139, 23)),
    Sum.inr (Sum.inr (10, 0)),
    Sum.inr (Sum.inr (10, 13)),
    Sum.inr (Sum.inr (414, 0)),
    Sum.inr (Sum.inr (414, 13)),
    Sum.inr (Sum.inr (287, 8)),
    Sum.inr (Sum.inr (287, 23)),
    Sum.inr (Sum.inr (405, 0)),
    Sum.inr (Sum.inr (405, 13)),
    Sum.inr (Sum.inr (276, 8)),
    Sum.inr (Sum.inr (276, 23)),
    Sum.inr (Sum.inr (128, 8)),
    Sum.inr (Sum.inr (128, 23)),
    Sum.inr (Sum.inr (1, 0)),
    Sum.inr (Sum.inr (1, 13)),
    Sum.inr (Sum.inl (125, 24)),
    Sum.inr (Sum.inl (138, 24)),
    Sum.inr (Sum.inl (125, 20)),
    Sum.inr (Sum.inl (138, 16)),
    Sum.inr (Sum.inl (138, 9)),
    Sum.inr (Sum.inl (125, 55)),
    Sum.inr (Sum.inl (138, 1)),
    Sum.inr (Sum.inl (125, 59)),
    Sum.inr (Sum.inl (186, 30)),
    Sum.inr (Sum.inl (154, 56)),
    Sum.inr (Sum.inl (186, 28)),
    Sum.inr (Sum.inl (154, 52)),
    Sum.inr (Sum.inl (154, 41)),
    Sum.inr (Sum.inl (186, 41)),
    Sum.inr (Sum.inl (154, 37)),
    Sum.inr (Sum.inl (186, 43)),
    Sum.inr (Sum.inl (91, 10)),
    Sum.inr (Sum.inl (108, 24)),
    Sum.inr (Sum.inl (91, 24)),
    Sum.inr (Sum.inl (108, 20)),
    Sum.inr (Sum.inl (108, 9)),
    Sum.inr (Sum.inl (91, 61)),
    Sum.inr (Sum.inl (108, 5)),
    Sum.inr (Sum.inl (91, 47)),
    Sum.inr (Sum.inl (41, 54)),
    Sum.inr (Sum.inl (216, 46)),
    Sum.inr (Sum.inl (41, 53)),
    Sum.inr (Sum.inl (216, 44)),
    Sum.inr (Sum.inl (216, 43)),
    Sum.inr (Sum.inl (41, 25)),
    Sum.inr (Sum.inl (216, 41)),
    Sum.inr (Sum.inl (41, 26)),
    Sum.inr (Sum.inl (186, 10)),
    Sum.inr (Sum.inl (154, 24)),
    Sum.inr (Sum.inl (186, 8)),
    Sum.inr (Sum.inl (154, 20)),
    Sum.inr (Sum.inl (154, 9)),
    Sum.inr (Sum.inl (186, 61)),
    Sum.inr (Sum.inl (154, 5)),
    Sum.inr (Sum.inl (186, 63)),
    Sum.inr (Sum.inl (125, 26)),
    Sum.inr (Sum.inl (138, 35)),
    Sum.inr (Sum.inl (125, 22)),
    Sum.inr (Sum.inl (138, 43)),
    Sum.inr (Sum.inl (138, 50)),
    Sum.inr (Sum.inl (125, 53)),
    Sum.inr (Sum.inl (138, 58)),
    Sum.inr (Sum.inl (125, 57)),
    Sum.inr (Sum.inl (41, 18)),
    Sum.inr (Sum.inl (216, 6)),
    Sum.inr (Sum.inl (41, 17)),
    Sum.inr (Sum.inl (216, 4)),
    Sum.inr (Sum.inl (216, 3)),
    Sum.inr (Sum.inl (41, 61)),
    Sum.inr (Sum.inl (216, 1)),
    Sum.inr (Sum.inl (41, 62)),
    Sum.inr (Sum.inl (91, 43)),
    Sum.inr (Sum.inl (108, 26)),
    Sum.inr (Sum.inl (91, 57)),
    Sum.inr (Sum.inl (108, 22)),
    Sum.inr (Sum.inl (108, 11)),
    Sum.inr (Sum.inl (91, 28)),
    Sum.inr (Sum.inl (108, 7)),
    Sum.inr (Sum.inl (91, 14)),
    Sum.inr (Sum.inl (75, 21)),
    Sum.inr (Sum.inl (43, 21)),
    Sum.inr (Sum.inl (130, 49)),
    Sum.inr (Sum.inl (201, 43)),
    Sum.inr (Sum.inl (115, 50)),
    Sum.inr (Sum.inl (164, 39)),
    Sum.inr (Sum.inl (90, 23)),
    Sum.inr (Sum.inl (217, 7)),
    Sum.inr (Sum.inl (75, 52)),
    Sum.inr (Sum.inl (43, 53)),
    Sum.inr (Sum.inl (130, 46)),
    Sum.inr (Sum.inl (201, 57)),
    Sum.inr (Sum.inl (115, 45)),
    Sum.inr (Sum.inl (164, 53)),
    Sum.inr (Sum.inl (90, 30)),
    Sum.inr (Sum.inl (217, 15)),
    Sum.inr (Sum.inl (130, 51)),
    Sum.inr (Sum.inl (201, 35)),
    Sum.inr (Sum.inl (75, 25)),
    Sum.inr (Sum.inl (43, 25)),
    Sum.inr (Sum.inl (90, 21)),
    Sum.inr (Sum.inl (217, 21)),
    Sum.inr (Sum.inl (115, 49)),
    Sum.inr (Sum.inl (164, 43)),
    Sum.inr (Sum.inl (130, 44)),
    Sum.inr (Sum.inl (201, 49)),
    Sum.inr (Sum.inl (75, 56)),
    Sum.inr (Sum.inl (43, 57)),
    Sum.inr (Sum.inl (90, 28)),
    Sum.inr (Sum.inl (217, 29)),
    Sum.inr (Sum.inl (115, 46)),
    Sum.inr (Sum.inl (164, 57)),
    Sum.inr (Sum.inl (115, 58)),
    Sum.inr (Sum.inl (164, 7)),
    Sum.inr (Sum.inl (90, 56)),
    Sum.inr (Sum.inl (217, 35)),
    Sum.inr (Sum.inl (75, 23)),
    Sum.inr (Sum.inl (43, 7)),
    Sum.inr (Sum.inl (130, 56)),
    Sum.inr (Sum.inl (201, 15)),
    Sum.inr (Sum.inl (115, 37)),
    Sum.inr (Sum.inl (164, 21)),
    Sum.inr (Sum.inl (90, 49)),
    Sum.inr (Sum.inl (217, 43)),
    Sum.inr (Sum.inl (75, 54)),
    Sum.inr (Sum.inl (43, 39)),
    Sum.inr (Sum.inl (130, 39)),
    Sum.inr (Sum.inl (201, 29)),
    Sum.inr (Sum.inl (90, 58)),
    Sum.inr (Sum.inl (217, 49)),
    Sum.inr (Sum.inl (115, 57)),
    Sum.inr (Sum.inl (164, 11)),
    Sum.inr (Sum.inl (130, 58)),
    Sum.inr (Sum.inl (201, 7)),
    Sum.inr (Sum.inl (75, 27)),
    Sum.inr (Sum.inl (43, 11)),
    Sum.inr (Sum.inl (90, 51)),
    Sum.inr (Sum.inl (217, 57)),
    Sum.inr (Sum.inl (115, 38)),
    Sum.inr (Sum.inl (164, 25)),
    Sum.inr (Sum.inl (130, 37)),
    Sum.inr (Sum.inl (201, 21)),
    Sum.inr (Sum.inl (75, 58)),
    Sum.inr (Sum.inl (43, 43)),
    Sum.inr (Sum.inl (74, 15)),
    Sum.inr (Sum.inl (106, 30)),
    Sum.inr (Sum.inl (194, 54)),
    Sum.inr (Sum.inl (184, 60)),
    Sum.inr (Sum.inl (117, 46)),
    Sum.inr (Sum.inl (127, 58)),
    Sum.inr (Sum.inl (42, 58)),
    Sum.inr (Sum.inl (218, 7)),
    Sum.inr (Sum.inl (117, 45)),
    Sum.inr (Sum.inl (127, 54)),
    Sum.inr (Sum.inl (42, 54)),
    Sum.inr (Sum.inl (218, 11)),
    Sum.inr (Sum.inl (74, 29)),
    Sum.inr (Sum.inl (106, 28)),
    Sum.inr (Sum.inl (194, 52)),
    Sum.inr (Sum.inl (184, 52)),
    Sum.inr (Sum.inl (106, 27)),
    Sum.inr (Sum.inl (74, 56)),
    Sum.inr (Sum.inl (184, 45)),
    Sum.inr (Sum.inl (194, 25)),
    Sum.inr (Sum.inl (127, 43)),
    Sum.inr (Sum.inl (117, 49)),
    Sum.inr (Sum.inl (218, 22)),
    Sum.inr (Sum.inl (42, 21)),
    Sum.inr (Sum.inl (127, 39)),
    Sum.inr (Sum.inl (117, 50)),
    Sum.inr (Sum.inl (218, 26)),
    Sum.inr (Sum.inl (42, 25)),
    Sum.inr (Sum.inl (106, 25)),
    Sum.inr (Sum.inl (74, 42)),
    Sum.inr (Sum.inl (184, 37)),
    Sum.inr (Sum.inl (194, 27)),
    Sum.inr (Sum.inl (74, 46)),
    Sum.inr (Sum.inl (106, 46)),
    Sum.inr (Sum.inl (194, 58)),
    Sum.inr (Sum.inl (184, 7)),
    Sum.inr (Sum.inl (117, 54)),
    Sum.inr (Sum.inl (127, 56)),
    Sum.inr (Sum.inl (42, 56)),
    Sum.inr (Sum.inl (218, 39)),
    Sum.inr (Sum.inl (117, 53)),
    Sum.inr (Sum.inl (127, 52)),
    Sum.inr (Sum.inl (42, 52)),
    Sum.inr (Sum.inl (218, 43)),
    Sum.inr (Sum.inl (74, 60)),
    Sum.inr (Sum.inl (106, 44)),
    Sum.inr (Sum.inl (194, 56)),
    Sum.inr (Sum.inl (184, 15)),
    Sum.inr (Sum.inl (106, 43)),
    Sum.inr (Sum.inl (74, 25)),
    Sum.inr (Sum.inl (184, 22)),
    Sum.inr (Sum.inl (194, 21)),
    Sum.inr (Sum.inl (127, 41)),
    Sum.inr (Sum.inl (117, 41)),
    Sum.inr (Sum.inl (218, 54)),
    Sum.inr (Sum.inl (42, 23)),
    Sum.inr (Sum.inl (127, 37)),
    Sum.inr (Sum.inl (117, 42)),
    Sum.inr (Sum.inl (218, 58)),
    Sum.inr (Sum.inl (42, 27)),
    Sum.inr (Sum.inl (106, 41)),
    Sum.inr (Sum.inl (74, 11)),
    Sum.inr (Sum.inl (184, 30)),
    Sum.inr (Sum.inl (194, 23)),
    Sum.inr (Sum.inl (98, 6)),
    Sum.inr (Sum.inl (199, 6)),
    Sum.inr (Sum.inl (85, 18)),
    Sum.inr (Sum.inl (183, 40)),
    Sum.inr (Sum.inl (135, 15)),
    Sum.inr (Sum.inl (62, 58)),
    Sum.inr (Sum.inl (59, 26)),
    Sum.inr (Sum.inl (219, 60)),
    Sum.inr (Sum.inl (98, 5)),
    Sum.inr (Sum.inl (199, 20)),
    Sum.inr (Sum.inl (85, 16)),
    Sum.inr (Sum.inl (183, 36)),
    Sum.inr (Sum.inl (135, 13)),
    Sum.inr (Sum.inl (62, 54)),
    Sum.inr (Sum.inl (59, 22)),
    Sum.inr (Sum.inl (219, 52)),
    Sum.inr (Sum.inl (135, 6)),
    Sum.inr (Sum.inl (62, 24)),
    Sum.inr (Sum.inl (59, 8)),
    Sum.inr (Sum.inl (219, 40)),
    Sum.inr (Sum.inl (98, 22)),
    Sum.inr (Sum.inl (199, 46)),
    Sum.inr (Sum.inl (85, 37)),
    Sum.inr (Sum.inl (183, 56))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock056Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨14336 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock056InputMaskData : ℕ :=
  sixthHex% [
    "41142f18a42f28a42f711c2f08a42f511c2f611c2f38ac2f00042f59b42f",
    "69b42f300c2f49b42f100c2f200c2f79bc2f79442f20fc2f10fc2f494c2f",
    "30fc2f694c2f594c2f00f42f4002ac00d2ac50d2ac100aac4022ac00faac",
    "50faac102aac0422ac44faac14faac542aac040aac44daac14daac5402ac",
    "4032ac00eaac50eaac103aac401aac00caac50caac1012ac041aac44caac",
    "14caac5412ac043aac44e2ac14e2ac5432ac0132ac41eaac11eaac513aac",
    "011aac41caac11caac5112ac451aac05caac55caac1512ac453aac05e2ac",
    "55e2ac1532ac010aac41daac11daac5102ac012aac41f2ac11f2ac5122ac",
    "452aac05f2ac55f2ac1522ac4502ac05d2ac55d2ac150aac40f427768427",
    "367427000c27776427411c2701ec27379c27635427552c2715dc2723ac27",
    "54cc2762bc27224c271434274f3427794c2739bc270fcc2778ac274edc27",
    "0e2c273854276c9c275aec271a1c272c64275b0c276d74272d84271bf427",
    "36f427008c27407c27760c27016c27371c2777ec27419427155c27232c27",
    "63dc2755a42722cc2714b427544427623427393c270f4c274fbc2779c427",
    "0eac2738d4277824274e54271a9c272ce4276c14275a64272d04271b7427",
    "5b84276dfc2755342e6c842e2c742e15cc2e2c642e15dc2e552c2e6c9c2e",
    "6e642e57dc2e172c2e2e9c2e173c2e2e8c2e6e7c2e57c42e6f642e56dc2e",
    "162c2e2f9c2e163c2e2f8c2e6f7c2e56c42e543c2e6d8c2e2d7c2e14c42e",
    "2d6c2e14d42e54242e6d942e79542e40ec2e001c2e39ac2e000c2e39bc2e",
    "794c2e40f42e420c2e7bbc2e3b4c2e02f42e3b5c2e02e42e42142e7ba42e",
    "430c2e7abc2e3a4c2e03f42e3a5c2e03e42e43142e7aa42e785c2e41e42e",
    "01142e38a42e01042e38b42e78442e41fc2e5122a17bf2a12bf2a1012aa1",
    "7302a159daa109daa1230aa17702a15ddaa10ddaa1270aa1552aa17ffaa1",
    "2ffaa10522a13b12a111caa141caa16b1aa1193aa133eaa163eaa14932a1",
    "1d3aa137eaa167eaa14d32a13f1aa115c2a145c2a16f12a17a12a150caa1",
    "00caa12a1aa1583aa172eaa122eaa10832a1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock056InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock056InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock056OutputMaskData : ℕ :=
  sixthHex% [
    "20734a77063551951577a06a55dc2f73e950557a70020f0f5d742f0a0150",
    "2c92700aa70f28db4a0eee35287d157f086a24342f02015024927073e70f",
    "20db4a77ae35513d1577086a2ec6e24d8dc91a57d8085cf312f18700faac",
    "5720bd346b9656f18744faac1320bd706b961b86e278cdc92f17d83d1cf3",
    "0d6dc91f66e248bcf32bf7d8401aac235187748b966680bd041aac675187",
    "308b962280bd382dc92a26e27dfcf31eb7d86ff6e27dfdc92a27d8496cf3",
    "22818741caac1610bd041b9666818705caac5210bd401b965ab6e248bdc9",
    "1f67d87c2cf33d1dc95e56e2098cf31b87d8012aac13218744fb9627b0bd",
    "452aac57218700fb9663b0bd085dc96b16e23cccf32ec7d80dab423c0153",
    "637d1d23970c1e7a785e906901ec273046362e0b426ee153319d1d00370c",
    "4c9a787d3069224c2762a6361a3d1d5ad70c05ab4234015378ac27490636",
    "167a7856906948dd1d79770c260b4266e1535b0c271be636449a78753069",
    "5fea781f0069407c2771d6363d7b420cd15353ad1d13470c0d0a783ca069",
    "63dc272336361edb425e3153014d1d30e70c393c2708963657ea78170069",
    "2aed1d6a070c357b4204d1531a9c275a7636050a7834a069780d1d49a70c",
    "16db425631530c363f2a0a7175763f220a716aea713d963f62ea7144d63f",
    "2f386078442e27386001042e38a42e1e986041e42e16986038a3406fdf0e",
    "30a340169f0e2f3f0e090340567f0e0103406aed1f4cd15113ad1f44d151",
    "0c31515b4d1f043151220d1f3800606f7c2e300060163c2e2f9c2e09a060",
    "56dc2e01a0606a4e3f4c7271130e3f4472710c92715bee3f04927122ae3f",
    "7dd51f5be95104951f53e9511b09514c751f13095135351f5edb4009a70e",
    "56db4070e70e49470e6f7b4030070e677b40aa380180e001d73a108ca210",
    "a29444f90c44aed655840e5593944fc80c4f9fd65eb50e5eea780ac0a00a",
    "977a1bcce21bc000019b9801cc4210e69a10b9ec44933444c4ee559f7655",
    "88ec4fa2344ff5ee5eae765e80400adbd80a8c021ba6da1ba29b2af9032a",
    "aed93b84013bdb776ff1af6fa6757efded7e"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock056OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock056OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock056InputNumeratorData : ℕ :=
  sixthHex% [
    "86185f7e18617df7e185f7df85f7df86185f7e18617df7e17df7e185f7df",
    "86185f7e18617e18617df7e186185f7e18617e18617df7e185f7df86185f",
    "86185f7e18617df85f7e17df85f8617df85f7e17df8617e17df85f7e17df",
    "7e17df8617e17df85f7e17df8617e185f8617e17df8617e17df85f7e17df",
    "85f8617df85f7e17df8617e17df85f7e17df85f8617df85f8617e185f861",
    "7df85f7e17df85f8617df85f7e186186185f86185f85f7df7df7e17e1861",
    "7e186186185f7df7e17e1861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock056InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock056InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock056OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df85f85f8617df85f85f86185f8618617e186185f85f7df85f7df7df7e1",
    "85f7df7df7e17df7e17e18617e186186185f86185f85f7df86185f85f7df",
    "85f7df7df7e186185f85f7df7e186186185f7e186186185f7df7e17e1861",
    "85f7df7df7e186185f85f7df86185f85f7df7e186186185f7df85f7e17df",
    "7e17df8617e17e17df8617e18617e185f86185f8617df85f7df85f7e17df",
    "7df85f7e17df7e17df8617e17e18617df7e186185f7e18617df7e185f7df",
    "7e18617df7e186185f7e1861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock056OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock056OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block056_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock056Input a) =
      generatedSixthXiShortBlock056InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock056Output a) =
      generatedSixthXiShortBlock056OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock056Input a) =
      generatedSixthXiShortBlock056InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock056Output a) =
      generatedSixthXiShortBlock056OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block056_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock056InputMask a) =
      generatedSixthXiShortBlock056OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock056InputMask a)) *
      generatedSixthXiShortBlock056InputNumerator a =
        generatedSixthXiShortBlock056OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block056_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock056Input a
    let y := generatedSixthXiShortBlock056Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block056_cache a
  have hs := generatedSixth_xi_short_block056_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block056_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock056Input a
    let y := generatedSixthXiShortBlock056Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block056_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block056_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock056Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block056_certificate a).1
    (generatedSixth_xi_short_block056_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
