/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSectionBinaryActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineKernelOrbit

/-! Eleven literal original section words and their full binary columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Full inverse columns of every original section source letter. -/
def generatedNinthAffineSectionInverseColumns : Fin 18 → Fin 24 → ℕ :=
  ![![1, 4196354, 4196356, 4196360, 131088, 65568, 64, 128, 2097408, 1049088, 58368, 2048,
      6144, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8445953],
    ![4196353, 2, 4196356, 4196360, 2752528, 1376288, 2752576, 1376384, 655616, 328192,
      54272, 2048, 4096, 10240, 16384, 32768, 65536, 131072, 262144, 524288, 1048576,
      2097152, 4194304, 8441858],
    ![4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016,
      46080, 2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576,
      2097152, 4194304, 8433668],
    ![4196353, 4196354, 4196356, 8, 3538960, 2949152, 1769536, 3539072, 852224, 721408,
      29696, 2048, 4096, 8192, 16384, 34816, 65536, 131072, 262144, 524288, 1048576,
      2097152, 4194304, 8417288],
    ![133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024,
      2048, 4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152,
      4194304, 8450064],
    ![67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024,
      2048, 4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152,
      4194304, 8450080],
    ![1, 2754562, 3737604, 1771528, 2146320, 3186720, 64, 57472, 180480, 221696, 1024,
      2048, 4096, 8192, 16384, 32768, 65536, 131072, 264192, 524288, 1048576, 2097152,
      4194304, 8446016],
    ![1, 1378306, 2557956, 3541000, 3170320, 1097760, 57408, 128, 237824, 115200, 1024,
      2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 526336, 1048576, 2097152,
      4194304, 8446080],
    ![2099201, 655362, 458756, 851976, 573456, 811040, 180288, 237696, 256, 4198912,
      2100224, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1050624,
      2097152, 4194304, 12587264],
    ![1050625, 327682, 917508, 720904, 827408, 311328, 221248, 114816, 4198656, 512,
      1051648, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576,
      2099200, 4194304, 12587520],
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 2097408, 1049088, 1024, 2048, 4096,
      8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
      131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608],
    ![7203536, 7985674, 7843844, 4749824, 4880920, 6375016, 2643462, 4570135, 4221704,
      423944, 1831494, 2048, 524288, 4988928, 4997120, 3350528, 593920, 131072, 4329472,
      4096, 1048576, 5746688, 917504, 12169216],
    ![7733256, 6946818, 6160388, 4325377, 16, 61503, 3166437, 24726, 283189, 274723, 62495,
      2048, 7766016, 6955008, 6176768, 4329472, 5963776, 3538944, 262144, 786432, 2097152,
      1048576, 4194304, 8388608],
    ![5242881, 3801090, 5242884, 2490376, 1835024, 6594602, 229447, 73869, 4290824, 172554,
      1203909, 2048, 4984832, 2498560, 4997120, 3833856, 65536, 131072, 4456448, 4718592,
      1048576, 6291456, 4194304, 13631488],
    ![7948046, 4245354, 1552388, 4351920, 8148904, 4505691, 2310236, 71460, 6377756,
      1381072, 1291027, 2048, 4325376, 4337664, 1855488, 1519616, 7766016, 630784, 2498560,
      2195456, 5877760, 6926336, 634880, 8388608],
    ![524840, 7479887, 5156868, 590402, 6853982, 7774922, 2622144, 8259399, 5829062,
      2959812, 4348639, 2048, 131072, 4263936, 2510848, 856064, 7733248, 4362240, 7180288,
      3538944, 3780608, 6926336, 7798784, 10399744],
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 14, 13, 11,
      7, 65536, 131072, 262144, 524288, 1048576, 2097152, 2048, 1024]]

/-- Signed original letters, with true denoting the genuine inverse. -/
def generatedNinthAffineSectionLetter (l : Fin 18 × Bool) : leechIsomSubgroup :=
  if l.2 then (generatedFifthSectionGenerator l.1)⁻¹ else generatedFifthSectionGenerator l.1

/-- Full packed binary columns of each original signed section letter. -/
def generatedNinthAffineSectionLetterColumns (l : Fin 18 × Bool) : Fin 24 → ℕ :=
  if l.2 then generatedNinthAffineSectionInverseColumns l.1
    else generatedNinthAffineSectionColumns l.1

/-- Exact full packed evaluation of a literal signed original section word. -/
def generatedNinthAffineSectionMaskWord (w : List (Fin 18 × Bool)) (v : ℕ) : ℕ :=
  w.foldr (fun l z => sixthFrameOrbitMaskApply
    (generatedNinthAffineSectionLetterColumns l) z) v

/-- Nine whole binary kernel source words followed by two alternating image source words. -/
def generatedNinthAffineLowerSourceWord : Fin 11 → List (Fin 18 × Bool) :=
  ![[(16, false), (15, false), (5, false), (0, false), (0, true), (1, false), (0, true), (5,
      true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (2, false), (0, true), (5, true), (15,
      true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (0, true), (3, false), (0, true), (5,
      true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (5, true), (6, false), (0, true), (5,
      true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (7, true), (5, false), (4, false), (0,
      true), (5, true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (4, true), (13, true), (15, true), (13,
      false), (15, false), (4, false), (0, true), (5, true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (12, true), (17, true), (5, true), (6,
      false), (17, false), (12, false), (0, true), (5, true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (12, true), (14, true), (13, true), (14,
      false), (12, false), (15, false), (0, true), (5, true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (15, true), (17, true), (5, true), (6,
      false), (17, false), (15, false), (0, true), (5, true), (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (12, true), (7, true), (17, true), (16,
      true), (8, false), (13, false), (14, false), (15, false), (0, false), (0, true), (5, true),
      (15, true), (16, true)],
    [(16, false), (15, false), (5, false), (0, false), (12, true), (7, true), (16, true), (17,
      true), (7, false), (15, false), (17, false), (15, false), (0, true), (5, true), (15, true),
      (16, true)]]

/-- Entire binary columns of the eleven complete original source words. -/
def generatedNinthAffineLowerSourceColumns : Fin 11 → Fin 24 → ℕ :=
  ![![67585, 8323074, 4, 3541000, 669712, 2467872, 1222720, 73856, 2400512, 1221120, 11264,
      2048, 6144, 8192, 18432, 34816, 65536, 133120, 264192, 524288, 1048576, 2097152,
      4194304, 13078637],
    ![4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016,
      46080, 2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576,
      2097152, 4194304, 8433668],
    ![4325377, 5570562, 4, 1771528, 3713040, 3446816, 665664, 2457728, 2334976, 1769984,
      15360, 2048, 6144, 10240, 16384, 32768, 67584, 131072, 264192, 526336, 1048576,
      2097152, 4194304, 13074643],
    ![67585, 8323074, 4, 7733256, 3946512, 565280, 106560, 3352704, 633088, 633344, 44032,
      2048, 4096, 10240, 16384, 34816, 65536, 133120, 264192, 524288, 1048576, 2097152,
      4194304, 16322666],
    ![4390913, 6946818, 4, 7143432, 3051536, 2699296, 2719808, 499840, 256, 502272, 46080,
      2048, 4096, 8192, 18432, 32768, 67584, 133120, 262144, 526336, 1048576, 2097152,
      4194304, 10485940],
    ![4196353, 4196354, 4, 4196360, 917530, 1638441, 1638477, 1507463, 5114122, 512,
      1094868, 2048, 921600, 1646592, 4997120, 1540096, 4261888, 131072, 4458496, 4720640,
      1048576, 2097152, 4194304, 9482448],
    ![4196367, 4196360, 4, 4196354, 1966272, 3735616, 3735584, 2555952, 459008, 918016,
      46080, 2048, 4096, 36864, 22528, 12288, 524288, 786432, 196608, 65536, 1048576,
      2097152, 4194304, 8433668],
    ![8323074, 4259841, 4, 526351, 3682419, 4460702, 7999742, 5607513, 2953662, 1381086,
      932964, 2048, 632832, 3643392, 7784448, 4096000, 4128768, 5570560, 7143424, 3538944,
      1048576, 2097152, 4194304, 12615687],
    ![67585, 8323074, 4, 7733256, 6434835, 3252266, 3711050, 5513357, 5153034, 4694538,
      3779684, 2048, 593920, 3614720, 4737024, 4098048, 65536, 4325376, 4456448, 524288,
      1048576, 2097152, 4194304, 12587022],
    ![9065543, 11519134, 1638400, 11031626, 10584850, 12526385, 16036837, 1060899, 1973344,
      4449972, 5952692, 634880, 960512, 1128544, 7212980, 2041952, 2631902, 2525370,
      921700, 2498782, 5832708, 3780608, 3192836, 1199520],
    ![13546164, 13677156, 962560, 11078158, 9148436, 4072952, 4689298, 8994108, 13673372,
      9674312, 10285352, 2603012, 4860122, 2498573, 10313966, 1226963, 958644, 6002871,
      2457607, 594100, 6928384, 1093632, 2689024, 9588518]]

set_option maxHeartbeats 8000000 in
-- Check both inverse source products on every original binary basis column.
/-- Every displayed inverse acts as a whole two-sided inverse on all original binary columns. -/
theorem generatedNinth_affine_section_inverse_columns : ∀ g : Fin 18,
    (∀ j : Fin 24, sixthFrameOrbitMaskApply (generatedNinthAffineSectionColumns g)
      (generatedNinthAffineSectionInverseColumns g j) = 2 ^ j.val) ∧
    (∀ j : Fin 24, sixthFrameOrbitMaskApply (generatedNinthAffineSectionInverseColumns g)
      (generatedNinthAffineSectionColumns g j) = 2 ^ j.val) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Evaluate all eleven complete source words on all twenty-four original columns.
/-- All complete original source words have the displayed action on every binary basis vector. -/
theorem generatedNinth_affine_lower_source_columns : ∀ (k : Fin 11) (j : Fin 24),
    generatedNinthAffineSectionMaskWord (generatedNinthAffineLowerSourceWord k) (2 ^ j.val) =
      generatedNinthAffineLowerSourceColumns k j := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Compare every full column of the nine kernel source words.
/-- The nine previously proved kernel orbit columns are the complete original word columns. -/
theorem generatedNinth_affine_lower_kernel_columns : ∀ k : Fin 9,
    generatedNinthAffineLowerSourceColumns ⟨k.val, by omega⟩ =
      generatedNinthAffineKernelColumns k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
