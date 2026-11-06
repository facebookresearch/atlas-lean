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
def generatedSixthXiShortBlock049Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (313, 15)),
    Sum.inr (Sum.inr (102, 1)),
    Sum.inr (Sum.inr (306, 15)),
    Sum.inr (Sum.inr (109, 1)),
    Sum.inr (Sum.inr (102, 11)),
    Sum.inr (Sum.inr (313, 22)),
    Sum.inr (Sum.inr (109, 11)),
    Sum.inr (Sum.inr (306, 22)),
    Sum.inr (Sum.inr (109, 15)),
    Sum.inr (Sum.inr (306, 1)),
    Sum.inr (Sum.inr (102, 15)),
    Sum.inr (Sum.inr (313, 1)),
    Sum.inr (Sum.inr (306, 11)),
    Sum.inr (Sum.inr (109, 22)),
    Sum.inr (Sum.inr (313, 11)),
    Sum.inr (Sum.inr (102, 22)),
    Sum.inr (Sum.inr (440, 15)),
    Sum.inr (Sum.inr (231, 1)),
    Sum.inr (Sum.inr (435, 15)),
    Sum.inr (Sum.inr (236, 1)),
    Sum.inr (Sum.inr (231, 11)),
    Sum.inr (Sum.inr (440, 22)),
    Sum.inr (Sum.inr (236, 11)),
    Sum.inr (Sum.inr (435, 22)),
    Sum.inr (Sum.inr (371, 15)),
    Sum.inr (Sum.inr (44, 1)),
    Sum.inr (Sum.inr (376, 15)),
    Sum.inr (Sum.inr (39, 1)),
    Sum.inr (Sum.inr (44, 11)),
    Sum.inr (Sum.inr (371, 22)),
    Sum.inr (Sum.inr (39, 11)),
    Sum.inr (Sum.inr (376, 22)),
    Sum.inr (Sum.inr (166, 15)),
    Sum.inr (Sum.inr (505, 1)),
    Sum.inr (Sum.inr (173, 15)),
    Sum.inr (Sum.inr (498, 1)),
    Sum.inr (Sum.inr (505, 11)),
    Sum.inr (Sum.inr (166, 22)),
    Sum.inr (Sum.inr (498, 11)),
    Sum.inr (Sum.inr (173, 22)),
    Sum.inr (Sum.inr (498, 13)),
    Sum.inr (Sum.inr (236, 0)),
    Sum.inr (Sum.inr (505, 13)),
    Sum.inr (Sum.inr (231, 0)),
    Sum.inr (Sum.inr (236, 8)),
    Sum.inr (Sum.inr (498, 23)),
    Sum.inr (Sum.inr (231, 8)),
    Sum.inr (Sum.inr (505, 23)),
    Sum.inr (Sum.inr (39, 13)),
    Sum.inr (Sum.inr (313, 0)),
    Sum.inr (Sum.inr (44, 13)),
    Sum.inr (Sum.inr (306, 0)),
    Sum.inr (Sum.inr (313, 8)),
    Sum.inr (Sum.inr (39, 23)),
    Sum.inr (Sum.inr (306, 8)),
    Sum.inr (Sum.inr (44, 23)),
    Sum.inr (Sum.inr (109, 13)),
    Sum.inr (Sum.inr (371, 0)),
    Sum.inr (Sum.inr (102, 13)),
    Sum.inr (Sum.inr (376, 0)),
    Sum.inr (Sum.inr (371, 8)),
    Sum.inr (Sum.inr (109, 23)),
    Sum.inr (Sum.inr (376, 8)),
    Sum.inr (Sum.inr (102, 23)),
    Sum.inr (Sum.inr (440, 13)),
    Sum.inr (Sum.inr (166, 0)),
    Sum.inr (Sum.inr (435, 13)),
    Sum.inr (Sum.inr (173, 0)),
    Sum.inr (Sum.inr (166, 8)),
    Sum.inr (Sum.inr (440, 23)),
    Sum.inr (Sum.inr (173, 8)),
    Sum.inr (Sum.inr (435, 23)),
    Sum.inr (Sum.inr (173, 13)),
    Sum.inr (Sum.inr (435, 0)),
    Sum.inr (Sum.inr (166, 13)),
    Sum.inr (Sum.inr (440, 0)),
    Sum.inr (Sum.inr (435, 8)),
    Sum.inr (Sum.inr (173, 23)),
    Sum.inr (Sum.inr (440, 8)),
    Sum.inr (Sum.inr (166, 23)),
    Sum.inr (Sum.inr (376, 13)),
    Sum.inr (Sum.inr (102, 0)),
    Sum.inr (Sum.inr (371, 13)),
    Sum.inr (Sum.inr (109, 0)),
    Sum.inr (Sum.inr (102, 8)),
    Sum.inr (Sum.inr (376, 23)),
    Sum.inr (Sum.inr (109, 8)),
    Sum.inr (Sum.inr (371, 23)),
    Sum.inr (Sum.inr (306, 13)),
    Sum.inr (Sum.inr (44, 0)),
    Sum.inr (Sum.inr (313, 13)),
    Sum.inr (Sum.inr (39, 0)),
    Sum.inr (Sum.inr (44, 8)),
    Sum.inr (Sum.inr (306, 23)),
    Sum.inr (Sum.inr (39, 8)),
    Sum.inr (Sum.inr (313, 23)),
    Sum.inr (Sum.inr (231, 13)),
    Sum.inr (Sum.inr (505, 0)),
    Sum.inr (Sum.inr (236, 13)),
    Sum.inr (Sum.inr (498, 0)),
    Sum.inr (Sum.inr (505, 8)),
    Sum.inr (Sum.inr (231, 23)),
    Sum.inr (Sum.inr (498, 8)),
    Sum.inr (Sum.inr (236, 23)),
    Sum.inr (Sum.inl (49, 10)),
    Sum.inr (Sum.inl (93, 12)),
    Sum.inr (Sum.inl (49, 6)),
    Sum.inr (Sum.inl (93, 4)),
    Sum.inr (Sum.inl (198, 34)),
    Sum.inr (Sum.inl (95, 8)),
    Sum.inr (Sum.inl (198, 32)),
    Sum.inr (Sum.inl (95, 4)),
    Sum.inr (Sum.inl (198, 10)),
    Sum.inr (Sum.inl (95, 24)),
    Sum.inr (Sum.inl (198, 8)),
    Sum.inr (Sum.inl (95, 20)),
    Sum.inr (Sum.inl (49, 8)),
    Sum.inr (Sum.inl (93, 55)),
    Sum.inr (Sum.inl (49, 4)),
    Sum.inr (Sum.inl (93, 63)),
    Sum.inr (Sum.inl (93, 45)),
    Sum.inr (Sum.inl (49, 37)),
    Sum.inr (Sum.inl (93, 37)),
    Sum.inr (Sum.inl (49, 41)),
    Sum.inr (Sum.inl (95, 54)),
    Sum.inr (Sum.inl (198, 25)),
    Sum.inr (Sum.inl (95, 58)),
    Sum.inr (Sum.inl (198, 27)),
    Sum.inr (Sum.inl (95, 38)),
    Sum.inr (Sum.inl (198, 49)),
    Sum.inr (Sum.inl (95, 42)),
    Sum.inr (Sum.inl (198, 51)),
    Sum.inr (Sum.inl (93, 22)),
    Sum.inr (Sum.inl (49, 39)),
    Sum.inr (Sum.inl (93, 30)),
    Sum.inr (Sum.inl (49, 43)),
    Sum.inr (Sum.inl (136, 3)),
    Sum.inr (Sum.inl (65, 10)),
    Sum.inr (Sum.inl (136, 17)),
    Sum.inr (Sum.inl (65, 6)),
    Sum.inr (Sum.inl (229, 18)),
    Sum.inr (Sum.inl (189, 10)),
    Sum.inr (Sum.inl (229, 17)),
    Sum.inr (Sum.inl (189, 8)),
    Sum.inr (Sum.inl (229, 10)),
    Sum.inr (Sum.inl (189, 6)),
    Sum.inr (Sum.inl (229, 9)),
    Sum.inr (Sum.inl (189, 4)),
    Sum.inr (Sum.inl (136, 34)),
    Sum.inr (Sum.inl (65, 8)),
    Sum.inr (Sum.inl (136, 48)),
    Sum.inr (Sum.inl (65, 4)),
    Sum.inr (Sum.inl (65, 27)),
    Sum.inr (Sum.inl (136, 56)),
    Sum.inr (Sum.inl (65, 23)),
    Sum.inr (Sum.inl (136, 42)),
    Sum.inr (Sum.inl (189, 27)),
    Sum.inr (Sum.inl (229, 41)),
    Sum.inr (Sum.inl (189, 25)),
    Sum.inr (Sum.inl (229, 42)),
    Sum.inr (Sum.inl (189, 23)),
    Sum.inr (Sum.inl (229, 49)),
    Sum.inr (Sum.inl (189, 21)),
    Sum.inr (Sum.inl (229, 50)),
    Sum.inr (Sum.inl (65, 25)),
    Sum.inr (Sum.inl (136, 25)),
    Sum.inr (Sum.inl (65, 21)),
    Sum.inr (Sum.inl (136, 11)),
    Sum.inr (Sum.inl (226, 8)),
    Sum.inr (Sum.inl (67, 61)),
    Sum.inr (Sum.inl (226, 44)),
    Sum.inr (Sum.inl (67, 21)),
    Sum.inr (Sum.inl (197, 16)),
    Sum.inr (Sum.inl (123, 47)),
    Sum.inr (Sum.inl (197, 52)),
    Sum.inr (Sum.inl (123, 45)),
    Sum.inr (Sum.inl (47, 34)),
    Sum.inr (Sum.inl (80, 34)),
    Sum.inr (Sum.inl (47, 54)),
    Sum.inr (Sum.inl (80, 28)),
    Sum.inr (Sum.inl (110, 48)),
    Sum.inr (Sum.inl (190, 47)),
    Sum.inr (Sum.inl (110, 50)),
    Sum.inr (Sum.inl (190, 45)),
    Sum.inr (Sum.inl (197, 8)),
    Sum.inr (Sum.inl (123, 55)),
    Sum.inr (Sum.inl (197, 44)),
    Sum.inr (Sum.inl (123, 53)),
    Sum.inr (Sum.inl (226, 16)),
    Sum.inr (Sum.inl (67, 63)),
    Sum.inr (Sum.inl (226, 52)),
    Sum.inr (Sum.inl (67, 23)),
    Sum.inr (Sum.inl (110, 36)),
    Sum.inr (Sum.inl (190, 59)),
    Sum.inr (Sum.inl (110, 38)),
    Sum.inr (Sum.inl (190, 57)),
    Sum.inr (Sum.inl (47, 32)),
    Sum.inr (Sum.inl (80, 32)),
    Sum.inr (Sum.inl (47, 52)),
    Sum.inr (Sum.inl (80, 30)),
    Sum.inr (Sum.inl (67, 41)),
    Sum.inr (Sum.inl (226, 54)),
    Sum.inr (Sum.inl (67, 1)),
    Sum.inr (Sum.inl (226, 18)),
    Sum.inr (Sum.inl (123, 11)),
    Sum.inr (Sum.inl (197, 46)),
    Sum.inr (Sum.inl (123, 9)),
    Sum.inr (Sum.inl (197, 10)),
    Sum.inr (Sum.inl (80, 54)),
    Sum.inr (Sum.inl (47, 28)),
    Sum.inr (Sum.inl (80, 8)),
    Sum.inr (Sum.inl (47, 8)),
    Sum.inr (Sum.inl (190, 14)),
    Sum.inr (Sum.inl (110, 14)),
    Sum.inr (Sum.inl (190, 12)),
    Sum.inr (Sum.inl (110, 12)),
    Sum.inr (Sum.inl (123, 19)),
    Sum.inr (Sum.inl (197, 54)),
    Sum.inr (Sum.inl (123, 17)),
    Sum.inr (Sum.inl (197, 18)),
    Sum.inr (Sum.inl (67, 43)),
    Sum.inr (Sum.inl (226, 46)),
    Sum.inr (Sum.inl (67, 3)),
    Sum.inr (Sum.inl (226, 10)),
    Sum.inr (Sum.inl (190, 26)),
    Sum.inr (Sum.inl (110, 26)),
    Sum.inr (Sum.inl (190, 24)),
    Sum.inr (Sum.inl (110, 24)),
    Sum.inr (Sum.inl (80, 52)),
    Sum.inr (Sum.inl (47, 30)),
    Sum.inr (Sum.inl (80, 10)),
    Sum.inr (Sum.inl (47, 10)),
    Sum.inr (Sum.inl (223, 40)),
    Sum.inr (Sum.inl (162, 23)),
    Sum.inr (Sum.inl (77, 9)),
    Sum.inr (Sum.inl (86, 27)),
    Sum.inr (Sum.inl (134, 29)),
    Sum.inr (Sum.inl (100, 63)),
    Sum.inr (Sum.inl (44, 45)),
    Sum.inr (Sum.inl (191, 5)),
    Sum.inr (Sum.inl (223, 21)),
    Sum.inr (Sum.inl (162, 8)),
    Sum.inr (Sum.inl (77, 41)),
    Sum.inr (Sum.inl (86, 18)),
    Sum.inr (Sum.inl (134, 2)),
    Sum.inr (Sum.inl (100, 53)),
    Sum.inr (Sum.inl (44, 36)),
    Sum.inr (Sum.inl (191, 13)),
    Sum.inr (Sum.inl (162, 7)),
    Sum.inr (Sum.inl (223, 32)),
    Sum.inr (Sum.inl (86, 11)),
    Sum.inr (Sum.inl (77, 3)),
    Sum.inr (Sum.inl (100, 47)),
    Sum.inr (Sum.inl (134, 23)),
    Sum.inr (Sum.inl (191, 20)),
    Sum.inr (Sum.inl (44, 43))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock049Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨12544 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock049InputMaskData : ℕ :=
  sixthHex% [
    "7f000a12a00a78a00a15080a47a00a2a080a40080a2da80a00a00a6d000a",
    "07000a6aa80a38000a55a80a3fa80a52080a12000a7fa80a15a80a78080a",
    "2aa80a47080a2d080a40a00a6a38033f08037d08032830037e08032b3003",
    "6930033c00037c08032930036b30033e00036830033d00037f00032a3803",
    "3f38036a00032800037d30032b00037e30033c30036908032900037c3003",
    "3e30036b08033d30036808032a08037f3803553803000003420003173003",
    "410003143003563003030803430003163003543003010803573003020803",
    "400803153803003003550003170003423803140003413803033803560803",
    "16000343380301380354080302380357080315080340300341342d78842d",
    "38742d01cc2d79642d40dc2d002c2d399c2d38542d01ec2d411c2d78ac2d",
    "000c2d39bc2d794c2d40f42d52542d6bec2d2b1c2d12ac2d6a0c2d53bc2d",
    "134c2d2af42d2b3c2d128c2d527c2d6bc42d136c2d2ad42d6a242d53942d",
    "47542d7eec2d3e1c2d07ac2d7f0c2d46bc2d064c2d3ff42d3e3c2d078c2d",
    "477c2d7ec42d066c2d3fd42d7f242d46942d543c2d6d8c2d2d7c2d14c42d",
    "6c6c2d55d42d15242d2c942d2d5c2d14e42d54142d6da42d15042d2cb42d",
    "6c442d55fc2d48244371944379644340dc4331744308cc43003c43398c43",
    "31444308fc43000c4339bc43481c4371ac43795c4340e4436444435dfc43",
    "550c436cbc431d1c4324ac432c5c4315e4431d2c43249c432c6c4315d443",
    "647c435dc4435534436c84434e444377fc437f0c4346bc43371c430eac43",
    "065c433fe443372c430e9c43066c433fd4434e7c4377c4437f3443468443",
    "622c435b9c43536c436ad4431b7c4322c4432a34431384431b4c4322f443",
    "2a044313b4436214435ba4435354436aec437dcd72247d724c8d72153572",
    "479d721e257276d5722f657204ad725d157235e5726c55723ef572674572",
    "0fb572560d726ead723715725fe57206557254f5720d457265b5723c0d72",
    "17c5724e75722685727f3d722d9572742d721cdd72456d7251ad72081572",
    "60e5723955726bf5723245725ab572030d72"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock049InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock049InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock049OutputMaskData : ℕ :=
  sixthHex% [
    "4a721015080a5c9b2172a13b6449304a732a03e0015c9a1b07000a587a10",
    "11e93b3fd321293b2a0701304e921b11e80115a80a3b921072013b2d7b21",
    "4ad32a15a9305c3a1b72000110d32842393907eb2824413920a212030803",
    "46da1214300310700833da1976080824e21951413203ab2346793265d323",
    "61921242380307ea1255000320a328724939379b28143139107132429b23",
    "07493224e32320000803aa194678081492192801390bab284e79391c9328",
    "6930033bda127e08035da21259e2190b08084eda196d70086993234a3932",
    "0feb235d01322800037aea123f38031c92121871393bdb287e09392ce328",
    "28a3230b09324edb231c31326992193b78087eaa195d0008144706327b48",
    "6d07063a7b48100063477c2d1800633e3c2d513063064c2d5930637f0c2d",
    "243706020b485d77060a0b4818a3484fdf0610a348369f066da42d4b9863",
    "14e42d4398632c942d0aa86355d42d02a86328d3487faf0620d34806ef06",
    "1ce2794b9e3714e27932de3769e51c4fd95210a51c47d95228d51c0ee952",
    "51951c06e9522c92797bee3724927902ae37614637477a791806374f7a79",
    "650152327d1c6d01524b3d1c243152734d1c2c31520a0d1c513637770a79",
    "2876377f0a799bdb9cbde7d29f9397c8efd9fd07d2aa7b9c880fd9ae3397",
    "deacf989d0b7aba4f28d98bcc930b7ef0cf9cd78bc9a04f2afedc3f8918d",
    "dae5c8fcd986b8718d9e4dc3bc3986eb45c89bdaa6bde6e89f92adc8eee3",
    "fd06e8aa7aa6880ee3ae32ad937ee3c402ade676e8c04aa684e2ada2dee3",
    "80aaa6d7d6e8a749868175c8a3018df47dc3c195c896e986b49dc392a18d",
    "d608bcf034f2d240b7853cf9b0d4f2e7a8bcc5dcf9e3e0b7937fd9c40397",
    "e677d2c04b9c84e397a2dfd980ab9cd7d7d2a992adfee7d2addaa68befd9",
    "9d07d2bb32ade80fd9bf7aa6ece5c8cad0b799edc3ce98bca930b7fe45c8",
    "ad78bc8b4dc3a576e383439cd07ee8870b97e0a39cb7d6e3e4eb97c2dee8",
    "914186c634f995098db33cf2a5d4f983e186d0dcf287a98d9da4f2bb918d",
    "e8acf9bfd986d8718d8f04f2dc3986fa0cf9"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock049OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock049OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock049InputNumeratorData : ℕ :=
  sixthHex% [
    "8617e17e17df8617e17e17df85f8618617e185f8618617e17df85f85f861",
    "7df85f85f8617e17df7df85f8617e17e17df85f8618617e185f8618617e1",
    "7df85f85f8617df85f7e17df85f8617df85f7e17df8617e17df85f7e17df",
    "85f8617df85f8617e185f8617df85f7e17df85f8617df85f7df7e185f7df",
    "85f7df86185f7e18617df7e17df7e185f7df85f7df86185f86185f7e1861",
    "7df7e185f7df85f7df86185f7e17df8617e18617e185f8617df85f7e17df",
    "7e17df8617e17df85f7e17df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock049InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock049InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock049OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e17df8617e17e17df8617e18617e185f86185f7df7df7e186185f85f7df",
    "86185f85f7df7e186186185f7df7e17e186185f7df7df7e185f7df7df7e1",
    "86185f85f7df7df85f85f8617e17df7df85f85f8618617e17df85f85f861",
    "85f8618617e17df85f85f8618617e17e17df85f8618617e17e18617df7e1",
    "86185f7e186186185f7e186185f7df86185f7df7e185f7df7e18617df7e1",
    "7e18617df7e186185f7e18617e186186185f86185f85f7df7df7e17e1861",
    "7e186186185f86185f85f7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock049OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock049OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block049_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock049Input a) =
      generatedSixthXiShortBlock049InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock049Output a) =
      generatedSixthXiShortBlock049OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock049Input a) =
      generatedSixthXiShortBlock049InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock049Output a) =
      generatedSixthXiShortBlock049OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block049_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock049InputMask a) =
      generatedSixthXiShortBlock049OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock049InputMask a)) *
      generatedSixthXiShortBlock049InputNumerator a =
        generatedSixthXiShortBlock049OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block049_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock049Input a
    let y := generatedSixthXiShortBlock049Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block049_cache a
  have hs := generatedSixth_xi_short_block049_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block049_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock049Input a
    let y := generatedSixthXiShortBlock049Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block049_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block049_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock049Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block049_certificate a).1
    (generatedSixth_xi_short_block049_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
