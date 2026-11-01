/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMasks

/-! Exact full extraspecial action by finite bit masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Literal full binary images of all corrected source coordinate generators. -/
def generatedNinthLowerSpinShortPackedColumns : Fin 11 → Fin 24 → ℕ :=
  ![
    ![780855, 6543924, 4829188, 4813444, 7010241, 2699299, 64, 6543336, 256, 731108, 650091, 2048,
      4397056, 4331520, 2158592, 4718592, 12288, 6959104, 7143424, 2719744, 7929856, 6926336,
      2686976, 12595203],
    ![3778346, 1218345, 7996043, 1586115, 2759920, 3239040, 64, 1168416, 7011215, 5464036,
      3163136, 2048, 1107968, 1103872, 3145728, 1079296, 65536, 2699264, 2459648, 3393536,
      3192832, 3209216, 7024640, 11731915],
    ![3268609, 3201026, 4829188, 3176456, 3821584, 65568, 64, 3229824, 4831488, 4831744, 3163136,
      2048, 6144, 10240, 16384, 34816, 65536, 133120, 264192, 524288, 1050624, 2099200, 4196352,
      12101483],
    ![3754858, 2769922, 4436410, 19464, 3821584, 90304, 64, 1128544, 6885566, 5322805, 3163136,
      2048, 2099200, 1079296, 3145728, 1103872, 3227648, 3690496, 921600, 1198080, 22528, 6144,
      4237312, 11048843],
    ![10160952, 15863397, 4786618, 16254929, 3821584, 8991020, 64, 11784242, 4831488, 4827908,
      3206144, 700416, 41406, 542421, 2237323, 155349, 644971, 686033, 303290, 50799, 3330613,
      2142654, 4235450, 7368712],
    ![11731841, 16384170, 9961896, 7995627, 11671736, 2211204, 64, 4252867, 12713504, 12828395,
      3711851, 3241984, 6856332, 6860428, 132043, 6416871, 65536, 7464840, 7114380, 2883183,
      4348460, 7346663, 3801315, 11731915],
    ![9095444, 557121, 6495712, 2832626, 9486989, 3724273, 64, 9614878, 11207855, 1230283, 18432,
      1644395, 11740708, 12092036, 1643371, 12127844, 693408, 9618077, 10937612, 3393330,
      10639044, 9110959, 12078041, 4248584],
    ![14683369, 5393258, 1191633, 10487011, 7340833, 14705014, 64, 128, 8479687, 4431304, 2307883,
      1220459, 13751574, 13805277, 1180523, 14693718, 148427, 12828356, 11992638, 3727154,
      15934109, 13722102, 14733547, 10514656],
    ![8610367, 3839786, 14259445, 1138930, 12114406, 3686321, 64, 8610494, 256561, 8596542, 18432,
      2709355, 9592516, 11123300, 2708331, 11024004, 3855520, 12317974, 8768135, 772185, 8597028,
      10108239, 10642233, 7537603],
    ![8864216, 1426514, 3748977, 5546403, 6095172, 8723085, 4311695, 2636831, 5049287, 8982890,
      10672541, 10177181, 13454550, 1971787, 7453440, 16774077, 10739794, 11106214, 6523664,
      6592148, 9926290, 13951737, 13195039, 1359380],
    ![13865918, 14917595, 16361469, 5824116, 549489, 10189828, 7005743, 3867335, 12938000,
      12141665, 7275135, 10660826, 4998022, 846163, 15477023, 4466701, 1305489, 12708297,
      11446991, 788996, 775794, 15494029, 7471959, 10030481]
  ]

/-- Exact upper triangular cocycle correction rows in the original Q extension. -/
def generatedNinthLowerSpinShortPackedRows : Fin 11 → Fin 24 → ℕ :=
  ![
    ![8390294, 8388628, 1176, 528, 1696, 1024, 0, 8388608, 0, 8388608, 8388608, 0, 8388608,
      8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![8389410, 8389008, 8390424, 48, 8389536, 8389120, 0, 8388608, 8390144, 1024, 0, 0, 8388608,
      8388608, 0, 8388608, 0, 0, 8388608, 8388608, 8388608, 8388608, 0, 0],
    ![798, 780, 1176, 768, 928, 0, 0, 768, 1024, 1024, 0, 0, 8388608, 8388608, 0, 8388608, 0,
      8388608, 8388608, 0, 8388608, 8388608, 8388608, 0],
    ![8388916, 416, 1680, 768, 928, 8388864, 0, 8388608, 1024, 1024, 0, 0, 8388608, 8388608, 0,
      8388608, 0, 0, 0, 8388608, 8388608, 8388608, 8388608, 0],
    ![5145628, 5145228, 1827992, 5595680, 928, 6715136, 0, 16618496, 8389632, 10216448, 8388608,
      8388608, 8388608, 6176768, 753664, 6160384, 14548992, 5505024, 8912896, 13631488, 8388608,
      8388608, 8388608, 0],
    ![7900954, 9457172, 7900584, 11334944, 9456000, 256, 0, 4469504, 9457152, 13924352, 11333632,
      0, 0, 0, 7897088, 14286848, 0, 7864320, 0, 10485760, 10485760, 12582912, 8388608, 0],
    ![13272092, 9791660, 15135104, 688, 16528416, 16195712, 0, 11099136, 689664, 9791488, 3584000,
      3612672, 4038656, 14893056, 3604480, 5177344, 14548992, 13893632, 9961472, 8388608, 6291456,
      4194304, 0, 0],
    ![2087196, 16620580, 11030048, 1140496, 3673120, 4502784, 0, 0, 6936064, 14303232, 15933440,
      12685312, 2580480, 16613376, 12943360, 2293760, 14286848, 12058624, 6815744, 15728640,
      8388608, 4194304, 0, 0],
    ![12035884, 6703412, 10909072, 3715984, 4040480, 16327296, 0, 12035840, 14932480, 8459264,
      3584000, 12685312, 5627904, 327680, 12681216, 2555904, 5242880, 8388608, 8388608, 12582912,
      8388608, 4194304, 0, 0],
    ![11595148, 3169176, 5026224, 9329056, 8045920, 3694464, 9281280, 16247296, 3932672, 2355200,
      9611264, 15564800, 7520256, 2048000, 13402112, 12255232, 6029312, 4456448, 9961472, 0,
      12582912, 12582912, 0, 0],
    ![14472080, 4372296, 10832512, 7970192, 10465440, 16100608, 4482304, 16258816, 8388608,
      2829312, 14499840, 11550720, 909312, 15679488, 15171584, 9568256, 3932160, 15728640,
      4194304, 15728640, 12582912, 8388608, 0, 0]
  ]

/-- Original central coefficients of all twenty-four corrected source unit images. -/
def generatedNinthLowerSpinShortPackedCoefficients : Fin 11 → ℕ :=
  ![8388917, 929, 7778707, 16167052, 7541295, 553780, 9360937, 7004197, 270519, 3327949, 855109]

/-- Complete original generator images, retaining the central Pauli correction. -/
def generatedNinthLowerSpinShortPackedImages (i : Fin 11) (j : Fin 24) : Q :=
  generatedNinthLowerSpinCorrection i * generatedNinthLowerSpinQImage i j *
    (generatedNinthLowerSpinCorrection i)⁻¹

/-- Exact decoded full-Q metadata for one corrected source generator. -/
def generatedNinthLowerSpinShortPackedMetadata (i : Fin 11) : Prop :=
  (∀ j, toAdd (generatedNinthLowerSpinShortPackedImages i j).base =
    monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinShortPackedColumns i j)) ∧
  (∀ j k, monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinShortPackedRows i j) k =
    if j < k then
      qBeta (monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinShortPackedColumns i j))
        (monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinShortPackedColumns i k)) +
        qBeta (Pi.single j 1) (Pi.single k 1) else 0) ∧
  (∀ j, monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinShortPackedCoefficients i) j =
    toAdd (generatedNinthLowerSpinShortPackedImages i j).coeff)

/-- Finite whole-mask and exact central-bit certificates, with the original signed coefficient. -/
def generatedNinthLowerSpinShortPackedCondition (i : Fin 11) (a : Fin 98280) : Prop :=
  let r := generatedNinthLowerSpinShortIndex a
  generatedAxisGlobalQMaskVector (generatedNinthLowerSpinShortPackedColumns i)
      (generatedAxisGlobalShortMask r) =
    generatedAxisGlobalShortMask (generatedNinthLowerSpinShortDestination i r) ∧
  (if (generatedAxisGlobalQMaskCentral (generatedNinthLowerSpinShortPackedRows i)
    (generatedNinthLowerSpinShortPackedCoefficients i) (generatedAxisGlobalShortMask r)).testBit 0
    then (1 : ZMod 2) else 0) = generatedNinthLowerSpinShortPhase i r ∧
  nortonUIntegerSign (generatedNinthLowerSpinShortPhase i r) *
    generatedNinthLowerSpinShortInputInteger r =
      generatedNinthLowerSpinShortInputInteger (generatedNinthLowerSpinShortDestination i r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
