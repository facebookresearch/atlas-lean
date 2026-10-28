/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Complete phase-preserving coordinate data for the four actual comparison words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false

/-- Original source-derived QCacheBinary data, checked separately against the complete actual source. -/
def generatedAxisGlobalOddFourthQCacheBinary : Fin 4 → Fin 24 → ℕ :=
  ![![6851630, 2265395, 7159993, 5469585, 4532341, 10477530, 5960113, 11864017, 316403, 1198889, 15460239, 2652160, 2634779, 6696473, 1122427, 7245139, 5495835, 6973440, 5084187, 3780608, 1198387, 1101824, 5492736, 3051774],
    ![7660083, 3291136, 3443945, 3564777, 559111, 9893610, 6688488, 9596205, 2041508, 6757557, 14625247, 5767168, 7029325, 6701643, 7665679, 6980215, 6148685, 4720640, 5907021, 419840, 4673589, 5597184, 1468416, 15604775],
    ![7563264, 6514688, 1081344, 5478400, 3145893, 2896083, 2983444, 1351409, 6767797, 2649120, 10192912, 528384, 1690378, 2228492, 5367368, 1830470, 7774208, 2670592, 7845888, 7329792, 3782656, 2805760, 530432, 12148263],
    ![6818050, 5489412, 2106432, 6958158, 3145893, 2896083, 2983444, 1351409, 6767797, 2649120, 12148263, 530432, 3783434, 1208588, 1211976, 1797702, 7774208, 2670592, 7845888, 7329792, 3782656, 2805760, 2048, 2283063]]

/-- Original source-derived QCachePhase data, checked separately against the complete actual source. -/
def generatedAxisGlobalOddFourthQCachePhase : Fin 4 → Fin 24 → ZMod 2 :=
  ![![0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0],
    ![1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1]]

/-- Original source-derived MaskRows data, checked separately against the complete actual source. -/
def generatedAxisGlobalOddFourthMaskRows : Fin 4 → Fin 24 → ℕ :=
  ![![57536, 58636, 1090232, 1091328, 8737216, 1498816, 8398080, 1456640, 9454592, 49152, 206848, 8388608, 0, 8437760, 1081344, 1048576, 0, 0, 0, 0, 0, 0, 0, 0],
    ![9454892, 8397984, 357728, 8761792, 357248, 16434176, 1082624, 7336448, 349696, 9827328, 7278592, 8388608, 9461760, 8732672, 360448, 1048576, 9437184, 8388608, 9437184, 8388608, 0, 8388608, 8388608, 0],
    ![8393728, 8397824, 16384, 8422400, 8446144, 8421440, 8414208, 8421632, 29696, 8445952, 6082560, 8388608, 8445952, 49152, 8421376, 8388608, 0, 0, 8388608, 8388608, 8388608, 0, 8388608, 0],
    ![4798, 9452, 16616, 33024, 8447168, 8422464, 25600, 8422656, 8417280, 8446976, 6068224, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Full original linear central-cochain correction bits. -/
def generatedAxisGlobalOddFourthMaskCoefficients : Fin 4 → ℕ :=
  ![10803892, 4384380, 11443487, 11419499]

/-- The complete cached Q extension element retains its original central phase. -/
def generatedAxisGlobalOddFourthQCache (k : Fin 4) (i : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthQCacheBinary k i)),
    ofAdd (generatedAxisGlobalOddFourthQCachePhase k i)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
