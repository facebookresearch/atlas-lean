/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Source-derived candidate coordinate and central-cochain data for three actual local words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Complete candidate binary images of all original hyperbolic coordinate generators. -/
def generatedAxisGlobalOddComparisonQCacheBinary : Fin 3 → Fin 24 → ℕ :=
  ![![2048, 3891968, 877312, 7344896, 3873893, 370433, 40960, 4298752, 5760884, 1654000,
    6534587, 7366814, 15761552, 8197488, 7111300, 7397364, 4460544, 4325376, 7347096, 396046,
    4128768, 3432448, 7760030, 2362811],
    ![2048, 3713792, 959232, 7590656, 3169381, 4568833, 43008, 4296704, 3577716, 2698480,
    4220347, 7092382, 13695138, 7736688, 3359364, 2363380, 4460544, 4327424, 3640216, 445198,
    4128768, 3434496, 6959262, 513467],
    ![12105385, 12828660, 16544775, 1820672, 1037091, 6153754, 5166393, 4186915, 2627835,
    2369739, 4222976, 8128512, 786432, 7663616, 7927808, 7848904, 1180669, 6817795, 5507075,
    590846, 378880, 2279424, 8126476, 4670684]]

/-- Complete original central signs of the same source-derived coordinate images. -/
def generatedAxisGlobalOddComparisonQCachePhase : Fin 3 → Fin 24 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0]]

/-- Full candidate coordinate images, retaining the original central component. -/
def generatedAxisGlobalOddComparisonQCache (k : Fin 3) (i : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonQCacheBinary k i)),
    ofAdd (generatedAxisGlobalOddComparisonQCachePhase k i)⟩

/-- Original triangular cocycle-difference rows, checked separately against the actual cocycle. -/
def generatedAxisGlobalOddComparisonMaskRows : Fin 3 → Fin 24 → ℕ :=
  ![![0, 8414976, 8390400, 8439552, 8431136, 12590080, 262144, 528384, 290816, 12897280,
    5011456, 8388608, 16384, 8388608, 8650752, 262144, 0, 0, 8388608, 8388608, 0, 0, 0, 0],
    ![0, 4237824, 4250112, 4200960, 4761888, 12631808, 266240, 524288, 5011456, 12889088, 28672,
    0, 15622144, 8437760, 9207808, 786432, 0, 0, 524288, 0, 0, 0, 8388608, 0],
    ![8342376, 16173276, 7752552, 32768, 8880128, 917760, 9339136, 9338880, 8847360, 9306112,
    4194304, 8388608, 0, 0, 0, 8978432, 0, 0, 0, 0, 0, 0, 8388608, 0]]

/-- Original linear central cochain coefficients. -/
def generatedAxisGlobalOddComparisonMaskCoefficients : Fin 3 → ℕ :=
  ![14841922, 2797821, 3777885]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
