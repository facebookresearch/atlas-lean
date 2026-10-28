/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer mask encodings of the complete actual Conway operator matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportMatrices

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- All fifteen complete actual operator matrices have these exact integer row masks. -/
def monsterCo1GeometryBinaryOperatorMasks : Fin 15 → Fin 24 → ℕ :=
    ![![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
    16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
    ![8388609, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 6158, 4096, 8397824, 8406016, 8422400,
    65568, 131088, 262144, 524288, 1049088, 2097408, 4194318, 8388608],
    ![1, 8388610, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10253, 8393728, 8192, 8406016,
    8422400, 66208, 131408, 262816, 524624, 1048736, 2097232, 4194317, 8388608],
    ![1, 2, 8388612, 8, 16, 32, 64, 128, 256, 512, 1024, 18443, 8393728, 8397824, 16384,
    8422400, 66016, 131984, 263056, 524912, 1048688, 2097376, 4194315, 8388608],
    ![1, 2, 4, 8388616, 16, 32, 64, 128, 256, 512, 1024, 34823, 8393728, 8397824, 8406016,
    32768, 66400, 131792, 262576, 525152, 1048784, 2097328, 4194311, 8388608],
    ![1, 2, 4, 8, 8388624, 32, 64, 128, 256, 512, 1024, 67599, 8392736, 8397472, 8405472,
    8422240, 65536, 131087, 262668, 525062, 1048716, 2097354, 4194304, 8388608],
    ![1, 2, 4, 8, 16, 8388640, 64, 128, 256, 512, 1024, 133135, 8392720, 8397136, 8405904,
    8422096, 65551, 131072, 262922, 524556, 1048774, 2097228, 4194304, 8388608],
    ![1, 2, 4, 8, 16, 32, 8388672, 128, 256, 512, 1024, 264206, 4096, 8397472, 8405904,
    8421808, 66060, 131850, 262144, 524302, 1048620, 2097206, 4194304, 8388608],
    ![1, 2, 4, 8, 16, 32, 64, 8388736, 256, 512, 1024, 526350, 4096, 8397136, 8405616, 8422240,
    66310, 131340, 262158, 524288, 1048634, 2097180, 4194304, 8388608],
    ![1, 2, 4, 8, 16, 32, 64, 128, 8388864, 512, 1024, 1051649, 8393216, 8352, 16496, 32976,
    65676, 131270, 262188, 524346, 1048576, 2098177, 12583424, 8388608],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 8389120, 1024, 2100225, 8392960, 8272, 16608, 32944,
    65738, 131148, 262198, 524316, 1049601, 2097152, 12583168, 8388608],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 4110, 8205, 16395, 32775, 65536,
    131072, 262144, 524288, 1049088, 2097408, 4194304, 8388608],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
    131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608],
    ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733, 13693571, 1106593,
    10487213, 11536301, 12824668, 12742908, 13127932, 13406300, 9453786, 9470070, 4530701,
    8388608],
    ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048, 2801756, 4178172, 4210699,
    4227079, 66051, 262658, 131331, 524546, 209088, 839728, 4194304, 8388608]]

set_option maxHeartbeats 24000000 in
-- Decode every coordinate of every matrix, retaining the already proved actual operators.
/-- The mask catalogue decodes to the original complete actual operator matrices. -/
theorem monsterCo1GeometryBinaryOperatorMasks_decode (k : Fin 15) :
    monsterCo1GeometryTransportOperatorMatrix k =
      monsterCo1GeometryBinaryMaskMatrix (monsterCo1GeometryBinaryOperatorMasks k) := by
  have hc : ∀ k : Fin 15, monsterCo1GeometryTransportOperatorMatrix k =
      monsterCo1GeometryBinaryMaskMatrix (monsterCo1GeometryBinaryOperatorMasks k) := by
    decide +kernel
  exact hc k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
