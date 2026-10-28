/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSpatialWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMasks

/-! Full original binary columns for the eighteen genuine selected-section letters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Full binary columns of the original two Golay permutation generators and their inverses. -/
def generatedNinthAffinePermutationColumns : Fin 4 → Fin 24 → ℕ :=
  ![![4259837, 3150606, 7325964, 6277644, 4129584, 2550305, 4129728, 1505615, 49164,
      4241412, 51198, 2048, 987136, 4403200, 1454080, 2699264, 4259840, 196608, 4718592,
      786432, 3190784, 49152, 5181440, 12570624],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813,
      1024, 2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728,
      8192, 12288, 4243456, 8388608],
    ![2637071, 2756878, 5954048, 8051456, 379963, 1035303, 1035397, 380105, 895236, 485640,
      2151506, 2048, 659456, 4726784, 7925760, 5828608, 4263936, 4395008, 4984832, 4460544,
      5074944, 4698112, 4198400, 11194368],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813,
      1024, 2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728,
      8192, 12288, 4243456, 8388608]]

/-- Full binary columns of all eighteen original signs, selected permutations and Xi. -/
def generatedNinthAffineSectionColumns : Fin 18 → Fin 24 → ℕ :=
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
    ![5327726, 3304192, 5242884, 1264480, 2131786, 4877493, 2772188, 4053832, 1715600,
      3090388, 5990002, 2048, 4726784, 6004736, 7954432, 4403200, 4259840, 4096, 8364032,
      7733248, 3735552, 5156864, 589824, 14680064],
    ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
      16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632]]

/-- Literal original permutation letters with both genuine inverse actions. -/
def generatedNinthAffinePermutationLetter (l : Fin 2 × Bool) : leechIsomSubgroup :=
  if l.2 then (omegaOrbitPermutationIsometry l.1)⁻¹ else omegaOrbitPermutationIsometry l.1

/-- The full original binary columns of a signed permutation source letter. -/
def generatedNinthAffinePermutationLetterColumns (l : Fin 2 × Bool) : Fin 24 → ℕ :=
  generatedNinthAffinePermutationColumns ⟨l.1.val + if l.2 then 2 else 0, by
    split_ifs <;> omega⟩

/-- Original source words for the five selected-octad permutation letters. -/
def generatedNinthAffineSelectedSourceWord (k : Fin 5) : List (Fin 2 × Bool) :=
  if h : k.val < 4 then generatedFourthMonomialWord ⟨k.val, h⟩ else [(0, false)]

/-- Complete original source transport, selected letter and inverse transport. -/
def generatedNinthAffineSelectedWord (k : Fin 5) : List (Fin 2 × Bool) :=
  generatedFifthMonomialTransportWord ++ generatedNinthAffineSelectedSourceWord k ++
    generatedFifthMonomialTransportWord.reverse.map (fun l => (l.1, !l.2))

/-- Exact full binary evaluation of any original signed permutation word. -/
def generatedNinthAffinePermutationMaskWord (w : List (Fin 2 × Bool)) (v : ℕ) : ℕ :=
  w.foldr (fun l z => sixthFrameOrbitMaskApply
    (generatedNinthAffinePermutationLetterColumns l) z) v

set_option maxHeartbeats 8000000 in
-- Bind all original signs to their previously certified whole binary matrices.
/-- The twelve original sign columns are the full genuine lattice quotient actions. -/
theorem generatedNinth_affine_section_sign_columns : ∀ k : Fin 12,
    sixthFrameOrbitColumnMatrix (generatedNinthAffineSectionColumns ⟨k.val, by omega⟩) =
      monsterCo1GeometrySignBinary k := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Bind both original permutation matrices and the original Xi matrix.
/-- The original permutation and Xi columns equal the already certified actual matrices. -/
theorem generatedNinth_affine_original_columns :
    (∀ k : Fin 2,
      sixthFrameOrbitColumnMatrix (generatedNinthAffinePermutationColumns ⟨k.val, by omega⟩) =
        omegaOrbitBinaryMatrices (Fin.natAdd 3 k)) ∧
      sixthFrameOrbitColumnMatrix (generatedNinthAffineSectionColumns 17) =
        omegaOrbitBinaryMatrices 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check both complete inverse products of the original source matrices.
/-- The proposed original inverse permutation columns are genuine two-sided inverses. -/
theorem generatedNinth_affine_permutation_column_inverse : ∀ k : Fin 2,
    sixthFrameOrbitColumnMatrix (generatedNinthAffinePermutationColumns ⟨k.val, by omega⟩) *
        sixthFrameOrbitColumnMatrix (generatedNinthAffinePermutationColumns
          ⟨k.val + 2, by omega⟩) = 1 ∧
      sixthFrameOrbitColumnMatrix (generatedNinthAffinePermutationColumns
        ⟨k.val + 2, by omega⟩) *
          sixthFrameOrbitColumnMatrix (generatedNinthAffinePermutationColumns
            ⟨k.val, by omega⟩) = 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bind each selected source word on all twenty-four original basis columns.
/-- Each selected original permutation word has its complete proposed binary columns. -/
theorem generatedNinth_affine_selected_word_columns : ∀ (k : Fin 5) (j : Fin 24),
    generatedNinthAffinePermutationMaskWord (generatedNinthAffineSelectedWord k) (2 ^ j.val) =
      generatedNinthAffineSectionColumns ⟨k.val + 12, by omega⟩ j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
