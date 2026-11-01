/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSourceMasks

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact original positive/inverse letter index. -/
def generatedNinthLowerSpinPrimitivePackedIndex (l : GeneratedNinthLowerSpinLetter) : Fin 30 :=
  ⟨2 * l.1.val + if l.2 then 1 else 0, by split_ifs <;> omega⟩

/-- The signed original source letter represented by each metadata row. -/
def generatedNinthLowerSpinPrimitivePackedLetter (n : Fin 30) : GeneratedNinthLowerSpinLetter :=
  (⟨n.val / 2, by omega⟩, n.val % 2 == 1)

/-- All actual signed source letters occur in their exact metadata position. -/
theorem generatedNinth_lower_spin_primitive_packed_letter_index :
    ∀ l : GeneratedNinthLowerSpinLetter,
      generatedNinthLowerSpinPrimitivePackedLetter (generatedNinthLowerSpinPrimitivePackedIndex l) =
        l := by
  decide +kernel

/-- Complete binary images of every positive and inverse source primitive. -/
def generatedNinthLowerSpinPrimitivePackedColumns : Fin 30 → Fin 24 → ℕ :=
  ![
    ![1, 4196354, 4196356, 4196360, 131088, 65568, 64, 128, 2097408, 1049088, 58368, 2048, 6144,
      8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8445953],
    ![1, 4196354, 4196356, 4196360, 131088, 65568, 64, 128, 2097408, 1049088, 58368, 2048, 6144,
      8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8445953],
    ![4196353, 2, 4196356, 4196360, 2752528, 1376288, 2752576, 1376384, 655616, 328192, 54272,
      2048, 4096, 10240, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8441858],
    ![4196353, 2, 4196356, 4196360, 2752528, 1376288, 2752576, 1376384, 655616, 328192, 54272,
      2048, 4096, 10240, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8441858],
    ![4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016, 46080,
      2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8433668],
    ![4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016, 46080,
      2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8433668],
    ![4196353, 4196354, 4196356, 8, 3538960, 2949152, 1769536, 3539072, 852224, 721408, 29696,
      2048, 4096, 8192, 16384, 34816, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8417288],
    ![4196353, 4196354, 4196356, 8, 3538960, 2949152, 1769536, 3539072, 852224, 721408, 29696,
      2048, 4096, 8192, 16384, 34816, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
      8417288],
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
    ![1, 2754562, 3737604, 1771528, 2146320, 3186720, 64, 57472, 180480, 221696, 1024, 2048, 4096,
      8192, 16384, 32768, 65536, 131072, 264192, 524288, 1048576, 2097152, 4194304, 8446016],
    ![1, 2754562, 3737604, 1771528, 2146320, 3186720, 64, 57472, 180480, 221696, 1024, 2048, 4096,
      8192, 16384, 32768, 65536, 131072, 264192, 524288, 1048576, 2097152, 4194304, 8446016],
    ![1, 1378306, 2557956, 3541000, 3170320, 1097760, 57408, 128, 237824, 115200, 1024, 2048,
      4096, 8192, 16384, 32768, 65536, 131072, 262144, 526336, 1048576, 2097152, 4194304,
      8446080],
    ![1, 1378306, 2557956, 3541000, 3170320, 1097760, 57408, 128, 237824, 115200, 1024, 2048,
      4096, 8192, 16384, 32768, 65536, 131072, 262144, 526336, 1048576, 2097152, 4194304,
      8446080],
    ![2099201, 655362, 458756, 851976, 573456, 811040, 180288, 237696, 256, 4198912, 2100224,
      2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1050624, 2097152, 4194304,
      12587264],
    ![2099201, 655362, 458756, 851976, 573456, 811040, 180288, 237696, 256, 4198912, 2100224,
      2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1050624, 2097152, 4194304,
      12587264],
    ![1050625, 327682, 917508, 720904, 827408, 311328, 221248, 114816, 4198656, 512, 1051648,
      2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2099200, 4194304,
      12587520],
    ![1050625, 327682, 917508, 720904, 827408, 311328, 221248, 114816, 4198656, 512, 1051648,
      2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2099200, 4194304,
      12587520],
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 2097408, 1049088, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 2097408, 1049088, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
      262144, 524288, 1048576, 2097152, 4194304, 8388608],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
      262144, 524288, 1048576, 2097152, 4194304, 8388608],
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
      4243456, 8388608],
    ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205, 16395,
      32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632],
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 14, 13, 11, 7,
      65536, 131072, 262144, 524288, 1048576, 2097152, 2048, 1024]
  ]

/-- Original upper triangular cocycle correction for each signed primitive. -/
def generatedNinthLowerSpinPrimitivePackedRows : Fin 30 → Fin 24 → ℕ :=
  ![
    ![0, 1024, 1024, 1024, 32, 0, 0, 0, 512, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1024, 1024, 1024, 32, 0, 0, 0, 512, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1024, 0, 1024, 1024, 672, 320, 640, 256, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![1024, 0, 1024, 1024, 672, 320, 640, 256, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![1024, 1024, 0, 1024, 480, 896, 896, 512, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![1024, 1024, 0, 1024, 480, 896, 896, 512, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![1024, 1024, 1024, 0, 864, 704, 384, 768, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![1024, 1024, 1024, 0, 864, 704, 384, 768, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![32, 672, 480, 864, 0, 0, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0],
    ![32, 672, 480, 864, 0, 0, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0],
    ![16, 336, 912, 720, 0, 0, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0],
    ![16, 336, 912, 720, 0, 0, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0],
    ![0, 672, 912, 432, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0],
    ![0, 672, 912, 432, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0],
    ![0, 336, 624, 864, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0],
    ![0, 336, 624, 864, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0],
    ![512, 160, 112, 208, 128, 192, 0, 0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0],
    ![512, 160, 112, 208, 128, 192, 0, 0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0],
    ![256, 80, 224, 176, 192, 64, 0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0],
    ![256, 80, 224, 176, 192, 64, 0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0],
    ![14, 12, 8, 0, 0, 0, 0, 0, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0],
    ![14, 12, 8, 0, 0, 0, 0, 0, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1038, 12, 1032, 1024, 864, 896, 896, 768, 1536, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4096, 8192, 16384, 32768, 0, 0, 0, 0, 0, 0, 4194304, 8388608, 57344, 49152, 32768, 0, 0, 0,
      0, 0, 0, 0, 8388608, 0],
    ![4110, 8204, 16392, 32768, 0, 0, 0, 0, 0, 0, 4196352, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0]
  ]

/-- Full central coefficients of all signed primitive coordinate images. -/
def generatedNinthLowerSpinPrimitivePackedCoefficients : Fin 30 → ℕ :=
  ![4926, 4926, 8445, 8445, 16635, 16635, 33015, 33015, 65536, 65536, 131072, 131072, 262144,
      262144, 524288, 524288, 1048576, 1048576, 2097152, 2097152, 4195072, 4195072, 0, 0, 0, 250,
      0, 515, 4255744, 2048]

/-- Exact decoded binary columns, all576 cochain entries, and full actual unit central bits. -/
def generatedNinthLowerSpinPrimitivePackedMetadata (n : Fin 30) : Prop :=
  (∀ j, toAdd (generatedNinthLowerSpinPrimitiveQGenerator
      (generatedNinthLowerSpinPrimitivePackedLetter n) j).base =
    monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinPrimitivePackedColumns n j)) ∧
  (∀ j k, monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinPrimitivePackedRows n j) k =
    if j < k then
      qBeta (monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinPrimitivePackedColumns n j))
        (monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinPrimitivePackedColumns n k)) +
        qBeta (Pi.single j 1) (Pi.single k 1) else 0) ∧
  (∀ j, monsterCo1GeometryBinaryMaskDecode
      (generatedNinthLowerSpinPrimitivePackedCoefficients n) j =
    toAdd (generatedNinthLowerSpinPrimitiveQGenerator
      (generatedNinthLowerSpinPrimitivePackedLetter n) j).coeff)

/-- Both complete binary halves of a25bit actual Q label. -/
def generatedNinthLowerSpinPrimitivePackedBinary (w : ℕ) : ℕ :=
  generatedAxisGlobalSourceMaskJoin (w % 4096) ((w / 4096) % 4096)

/-- The genuine central coefficient of a25bit actual Q label. -/
def generatedNinthLowerSpinPrimitivePackedCentral (w : ℕ) : ZMod 2 :=
  ((w / 16777216 : ℕ) : ZMod 2)

/-- Full original Q decoding of both binary halves and the original central coefficient. -/
def generatedNinthLowerSpinPrimitivePackedQ (w : ℕ) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients ⟨w % 4096, Nat.mod_lt _ (by decide)⟩)
    (golayLabelCoefficients ⟨(w / 4096) % 4096, Nat.mod_lt _ (by decide)⟩)),
    ofAdd (generatedNinthLowerSpinPrimitivePackedCentral w)⟩

/-- Complete output vector and actual central coefficient of one original primitive step. -/
def generatedNinthLowerSpinPrimitivePackedCondition (l : GeneratedNinthLowerSpinLetter)
    (input output : ℕ) : Prop :=
  let n := generatedNinthLowerSpinPrimitivePackedIndex l
  generatedAxisGlobalQMaskVector (generatedNinthLowerSpinPrimitivePackedColumns n)
      (generatedNinthLowerSpinPrimitivePackedBinary input) =
    generatedNinthLowerSpinPrimitivePackedBinary output ∧
  generatedNinthLowerSpinPrimitivePackedCentral input +
    (if (generatedAxisGlobalQMaskCentral (generatedNinthLowerSpinPrimitivePackedRows n)
      (generatedNinthLowerSpinPrimitivePackedCoefficients n)
      (generatedNinthLowerSpinPrimitivePackedBinary input)).testBit 0
      then (1 : ZMod 2) else 0) = generatedNinthLowerSpinPrimitivePackedCentral output

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
