/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskRows
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddRootsData

/-! Candidate short words in five original source operators,
      checked against their genuine actions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Original positive and inverse binary columns,
      alternating for each of the five source letters. -/
def generatedAxisGlobalOddSourceColumns : Fin 10 → Fin 24 → ℕ :=
  ![![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
      16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 14, 13, 11, 7,
      65536, 131072, 262144, 524288, 1048576, 2097152, 2048, 1024],
    ![133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024,
      2048, 4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8450064],
    ![133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024,
      2048, 4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8450064],
    ![67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024,
      2048, 4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4194304,
      8450080],
    ![67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024,
      2048, 4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4194304,
      8450080],
    ![4259837, 3150606, 7325964, 6277644, 4129584, 2550305, 4129728, 1505615, 49164, 4241412,
      51198, 2048, 987136, 4403200, 1454080, 2699264, 4259840, 196608, 4718592, 786432,
      3190784, 49152, 5181440, 12570624],
    ![2637071, 2756878, 5954048, 8051456, 379963, 1035303, 1035397, 380105, 895236, 485640,
      2151506, 2048, 659456, 4726784, 7925760, 5828608, 4263936, 4395008, 4984832, 4460544,
      5074944, 4698112, 4198400, 11194368],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
      2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192,
      12288, 4243456, 8388608],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
      2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192,
      12288, 4243456, 8388608]]

/-- The same original columns retain their explicit coordinate indices. -/
def generatedAxisGlobalOddSourceRows : Fin 10 → List (ℕ × ℕ) :=
  ![[(0, 57344), (1, 53248), (2, 45056), (3, 28672), (4, 16), (5, 32), (6, 64), (7, 128), (8,
      256), (9, 512), (10, 8388608), (11, 4194304), (12, 4110), (13, 8205), (14, 16395), (15,
      32775), (16, 65536), (17, 131072), (18, 262144), (19, 524288), (20, 1048576), (21,
      2097152), (22, 4196352), (23, 8389632)],
    [(0, 57345), (1, 53250), (2, 45060), (3, 28680), (4, 16), (5, 32), (6, 64), (7, 128), (8,
      256), (9, 512), (10, 8389632), (11, 4196352), (12, 14), (13, 13), (14, 11), (15, 7), (16,
      65536), (17, 131072), (18, 262144), (19, 524288), (20, 1048576), (21, 2097152), (22,
      2048), (23, 1024)],
    [(0, 133121), (1, 2754562), (2, 1968132), (3, 3541000), (4, 16), (5, 61472), (6, 2146368),
      (7, 3170432), (8, 573696), (9, 827904), (10, 1024), (11, 2048), (12, 4096), (13, 8192),
      (14, 16384), (15, 32768), (16, 67584), (17, 131072), (18, 262144), (19, 524288), (20,
      1048576), (21, 2097152), (22, 4194304), (23, 8450064)],
    [(0, 133121), (1, 2754562), (2, 1968132), (3, 3541000), (4, 16), (5, 61472), (6, 2146368),
      (7, 3170432), (8, 573696), (9, 827904), (10, 1024), (11, 2048), (12, 4096), (13, 8192),
      (14, 16384), (15, 32768), (16, 67584), (17, 131072), (18, 262144), (19, 524288), (20,
      1048576), (21, 2097152), (22, 4194304), (23, 8450064)],
    [(0, 67585), (1, 1378306), (2, 3737604), (3, 2951176), (4, 61456), (5, 32), (6, 3186752),
      (7, 1097856), (8, 811264), (9, 311808), (10, 1024), (11, 2048), (12, 4096), (13, 8192),
      (14, 16384), (15, 32768), (16, 65536), (17, 133120), (18, 262144), (19, 524288), (20,
      1048576), (21, 2097152), (22, 4194304), (23, 8450080)],
    [(0, 67585), (1, 1378306), (2, 3737604), (3, 2951176), (4, 61456), (5, 32), (6, 3186752),
      (7, 1097856), (8, 811264), (9, 311808), (10, 1024), (11, 2048), (12, 4096), (13, 8192),
      (14, 16384), (15, 32768), (16, 65536), (17, 133120), (18, 262144), (19, 524288), (20,
      1048576), (21, 2097152), (22, 4194304), (23, 8450080)],
    [(0, 4259837), (1, 3150606), (2, 7325964), (3, 6277644), (4, 4129584), (5, 2550305), (6,
      4129728), (7, 1505615), (8, 49164), (9, 4241412), (10, 51198), (11, 2048), (12, 987136),
      (13, 4403200), (14, 1454080), (15, 2699264), (16, 4259840), (17, 196608), (18, 4718592),
      (19, 786432), (20, 3190784), (21, 49152), (22, 5181440), (23, 12570624)],
    [(0, 2637071), (1, 2756878), (2, 5954048), (3, 8051456), (4, 379963), (5, 1035303), (6,
      1035397), (7, 380105), (8, 895236), (9, 485640), (10, 2151506), (11, 2048), (12, 659456),
      (13, 4726784), (14, 7925760), (15, 5828608), (16, 4263936), (17, 4395008), (18, 4984832),
      (19, 4460544), (20, 5074944), (21, 4698112), (22, 4198400), (23, 11194368)],
    [(0, 377516), (1, 1033212), (2, 46084), (3, 29704), (4, 2109456), (5, 2105408), (6,
      1060896), (7, 1056896), (8, 786483), (9, 196813), (10, 1024), (11, 2048), (12, 3145728),
      (13, 1048576), (14, 2125824), (15, 2142208), (16, 1122304), (17, 1323008), (18, 2236416),
      (19, 2633728), (20, 8192), (21, 12288), (22, 4243456), (23, 8388608)],
    [(0, 377516), (1, 1033212), (2, 46084), (3, 29704), (4, 2109456), (5, 2105408), (6,
      1060896), (7, 1056896), (8, 786483), (9, 196813), (10, 1024), (11, 2048), (12, 3145728),
      (13, 1048576), (14, 2125824), (15, 2142208), (16, 1122304), (17, 1323008), (18, 2236416),
      (19, 2633728), (20, 8192), (21, 12288), (22, 4243456), (23, 8388608)]]

/-- Literal source words, in product order, normalizing the nine genuine roots. -/
def generatedAxisGlobalOddSourceRootWords : Fin 9 → List (Fin 10) :=
  ![[1, 6, 6, 0, 5, 9, 7, 7, 7, 9, 0],
    [0, 9, 6, 1, 6, 1, 6, 6, 9, 7, 0],
    [1, 7, 9, 1, 7, 9, 6, 0, 9, 6, 9],
    [0, 6, 9, 0, 7, 1, 6, 6, 1],
    [1, 9, 0, 3, 6, 9, 7, 3, 7],
    [],
    [1, 9, 1, 7, 7, 0],
    [1, 9, 7, 9, 6, 9, 0, 3, 5, 6, 1],
    [0, 6, 9, 1, 7, 0, 9, 6, 9, 1, 6]]

set_option maxHeartbeats 12000000 in
-- Check every forward and inverse source column against the genuine lattice-induced operators.
/-- Positive columns are actual operators; inverse columns pass the genuine right-inverse test. -/
theorem generatedAxisGlobalOddSourceColumns_certificate : ∀ k : Fin 5,
    omegaOrbitBinaryMatrices k =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalOddSourceColumns
        ⟨2 * k.val, by omega⟩) ∧
    (∀ j : Fin 24, omegaOrbitBinaryMatrices k *ᵥ
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalOddSourceColumns ⟨2 * k.val + 1, by omega⟩ j) = Pi.single j 1) := by
  decide +kernel

/-- Every literal indexed list retains the complete source column data. -/
theorem generatedAxisGlobalOddSourceRows_certificate : ∀ k : Fin 10,
    generatedAxisGlobalOddSourceRows k = List.ofFn
      (fun j : Fin 24 => (j.val, generatedAxisGlobalOddSourceColumns k j)) := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Check each complete source product on its exact original binary root mask.
/-- All nine source products send the actual root masks to the genuine frame mask. -/
theorem generatedAxisGlobalOddSourceRootWords_certificate : ∀ k : Fin 9,
    (generatedAxisGlobalOddSourceRootWords k).foldr
      (fun l x => generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      (generatedAxisGlobalOddRootMask k) = 2048 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
