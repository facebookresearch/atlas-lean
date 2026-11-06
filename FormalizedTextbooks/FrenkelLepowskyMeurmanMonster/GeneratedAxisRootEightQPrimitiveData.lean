/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceQImage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Original full extraspecial actions of the primitive root-eight source factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Original Golay signs in the root-eight generators and canonical transport. -/
def generatedRootEightQPrimitiveSignLabels : Fin 6 → Fin 4096 := ![1, 2048, 2816, 1536, 3220, 165]

/-- Full original Q images, with every central and inverse-source phase retained. -/
def generatedRootEightQPrimitiveImage (k : Fin 11) (q : Q) : Q :=
  if h : k.val < 4 then
    if h2 : k.val < 2 then monsterSourcePermutationImage ⟨k.val, h2⟩ q
    else generatedAxisGlobalMonomialInverseQImage ⟨k.val - 2, by omega⟩ q
  else if k.val = 4 then xiSpinGImage (xiSpinGammaImage q)
  else generatedAxisGlobalSignFullImage
    (generatedRootEightQPrimitiveSignLabels ⟨k.val - 5, by omega⟩) q

/-- Complete original binary columns for the eleven primitive actions. -/
def generatedRootEightQPrimitiveColumns : Fin 11 → Fin 24 → ℕ :=
![![4259837, 3150606, 7325964, 6277644, 4129584, 2550305, 4129728, 1505615, 49164, 4241412, 51198,
    2048, 987136, 4403200, 1454080, 2699264, 4259840, 196608, 4718592, 786432, 3190784, 49152,
    5181440, 12570624],
  ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024, 2048,
    3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192, 12288, 4243456,
    8388608],
  ![2637071, 2756878, 5954048, 8051456, 379963, 1035303, 1035397, 380105, 895236, 485640, 2151506,
    2048, 659456, 4726784, 7925760, 5828608, 4263936, 4395008, 4984832, 4460544, 5074944, 4698112,
    4198400, 11194368],
  ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024, 2048,
    3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192, 12288, 4243456,
    8388608],
  ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205, 16395,
    32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
  ![1, 4196354, 4196356, 4196360, 131088, 65568, 64, 128, 2097408, 1049088, 58368, 2048, 6144,
    8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8445953],
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 8388608],
  ![3147777, 983042, 589828, 393224, 286736, 565280, 106560, 155776, 4198656, 4198912, 3148800,
    2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1050624, 2099200, 4194304,
    12587776],
  ![1107969, 380930, 962564, 749576, 827408, 311328, 221248, 114816, 6297856, 1049088, 1051648,
    2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2099200, 4196352,
    13639168],
  ![4384769, 8378370, 3782660, 4222984, 3041296, 2699296, 1646656, 1534080, 2908416, 1270272,
    46080, 2048, 4096, 8192, 18432, 32768, 67584, 131072, 262144, 526336, 1048576, 2097152,
    4196352, 9010324],
  ![4259841, 2, 6160388, 1771528, 2922512, 2672672, 608320, 3655808, 2670848, 1769984, 23552, 2048,
    6144, 8192, 18432, 32768, 65536, 133120, 262144, 526336, 1048576, 2097152, 4194304, 13598885]]

/-- Original central signs at all twenty-four positive binary generators. -/
def generatedRootEightQPrimitiveCoefficients : Fin 11 → ℕ := ![0, 0, 250, 515, 4255744, 816,
    8388608, 8389633, 1537, 8389484, 1853]

/-- Each recorded basis image is an actual element of the original Q extension. -/
def generatedRootEightQPrimitiveBasisImage (k : Fin 11) (i : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedRootEightQPrimitiveColumns k i)),
    ofAdd (if (generatedRootEightQPrimitiveCoefficients k).testBit i.val then 1 else 0)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
