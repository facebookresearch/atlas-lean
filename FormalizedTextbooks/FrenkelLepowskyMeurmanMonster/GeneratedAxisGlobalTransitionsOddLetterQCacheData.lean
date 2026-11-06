/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Candidate complete coordinate images of original signed odd-family source letters. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The original source binary image masks of all ten signed letters. -/
def generatedAxisGlobalOddLetterQCacheBinary : Fin 10 → Fin 24 → ℕ :=
  ![![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
    16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
  ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 14, 13, 11, 7,
    65536, 131072, 262144, 524288, 1048576, 2097152, 2048, 1024],
  ![133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024, 2048,
    4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8450064],
  ![133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024, 2048,
    4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8450064],
  ![67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4194304,
    8450080],
  ![67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4194304,
    8450080],
  ![4259837, 3150606, 7325964, 6277644, 4129584, 2550305, 4129728, 1505615, 49164, 4241412,
    51198, 2048, 987136, 4403200, 1454080, 2699264, 4259840, 196608, 4718592, 786432, 3190784,
    49152, 5181440, 12570624],
  ![2637071, 2756878, 5954048, 8051456, 379963, 1035303, 1035397, 380105, 895236, 485640,
    2151506, 2048, 659456, 4726784, 7925760, 5828608, 4263936, 4395008, 4984832, 4460544,
    5074944, 4698112, 4198400, 11194368],
  ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
    2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192, 12288,
    4243456, 8388608],
  ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
    2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192, 12288,
    4243456, 8388608]]

/-- Full source-derived central coefficients, checked before use as actual actions. -/
def generatedAxisGlobalOddLetterQCachePhase : Fin 10 → Fin 24 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- A candidate full coordinate image, including its original central sign. -/
def generatedAxisGlobalOddLetterQCache (l : Fin 10) (i : Fin 24) : Q :=
  ⟨ofAdd (fun j => golayBooleanCast ((generatedAxisGlobalOddLetterQCacheBinary l i).testBit j.val)),
    ofAdd (generatedAxisGlobalOddLetterQCachePhase l i)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
