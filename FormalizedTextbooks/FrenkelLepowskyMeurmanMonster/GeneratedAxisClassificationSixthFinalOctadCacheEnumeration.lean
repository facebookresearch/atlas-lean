/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheData

/-! Genuine occurring catalogue labels and complete original-row coverage of the finite cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The family containing each genuine original middle row. -/
def generatedSixthFinalOctadCacheOwner : Fin 273 → Fin 231 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 0, 31, 32, 33, 0,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 1, 50, 51, 52, 1, 53, 54, 55,
    56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
    2, 68, 69, 70, 2, 71, 72, 73, 74, 75, 76, 77,
    78, 79, 80, 81, 82, 83, 84, 3, 85, 86, 87, 3,
    88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
    100, 4, 101, 102, 103, 4, 104, 105, 106, 107, 108, 109,
    110, 111, 112, 113, 114, 115, 5, 116, 117, 118, 5, 119,
    120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 6, 130,
    131, 132, 6, 133, 134, 135, 136, 137, 138, 139, 140, 141,
    142, 7, 143, 144, 145, 7, 146, 147, 148, 149, 150, 151,
    152, 153, 154, 8, 155, 156, 157, 8, 158, 159, 160, 161,
    162, 163, 164, 165, 9, 166, 167, 168, 9, 169, 170, 171,
    172, 173, 174, 175, 10, 176, 177, 178, 10, 179, 180, 181,
    182, 183, 184, 185, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 186, 187, 11, 188, 189, 190, 191, 192, 193, 194,
    195, 12, 196, 197, 198, 199, 200, 201, 202, 13, 203, 204,
    205, 206, 207, 208, 209, 14, 15, 16, 17, 18, 19, 20,
    210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221,
    222, 223, 224, 225, 226, 227, 228, 229, 230]

/-- One actual original middle row supplies the genuine catalogue index of each family. -/
def generatedSixthFinalOctadCacheRepresentative : Fin 231 → Fin 273 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 36, 37,
    38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 53, 54, 55, 57, 58, 59, 60, 61, 62, 63,
    64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 77,
    78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
    90, 92, 93, 94, 96, 97, 98, 99, 100, 101, 102, 103,
    104, 105, 106, 107, 108, 110, 111, 112, 114, 115, 116, 117,
    118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 131,
    132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 143, 144,
    145, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 158,
    159, 160, 162, 163, 164, 165, 166, 167, 168, 169, 170, 172,
    173, 174, 176, 177, 178, 179, 180, 181, 182, 183, 185, 186,
    187, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 201,
    202, 203, 204, 205, 206, 207, 218, 219, 221, 222, 223, 224,
    225, 226, 227, 228, 230, 231, 232, 233, 234, 235, 236, 238,
    239, 240, 241, 242, 243, 244, 252, 253, 254, 255, 256, 257,
    258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269,
    270, 271, 272]

/-- The family lookup retains the exact original code label on every row. -/
theorem generatedSixth_final_octad_cache_owner : ∀ j : Fin 273,
    generatedSixthMiddleOctadCode j =
      generatedSixthFinalOctadCacheCode (generatedSixthFinalOctadCacheOwner j) := by
  decide +kernel

/-- Each selected genuine middle row has its displayed family code. -/
theorem generatedSixth_final_octad_cache_representative : ∀ f : Fin 231,
    generatedSixthMiddleOctadCode (generatedSixthFinalOctadCacheRepresentative f) =
      generatedSixthFinalOctadCacheCode f := by
  decide +kernel

/-- The actual inverse catalogue, rather than a numerical discovery index, supplies the family. -/
def generatedSixthFinalOctadCacheOctad (f : Fin 231) : Fin 759 :=
  generatedSixthMiddleOctad (generatedSixthFinalOctadCacheRepresentative f)

/-- The genuine occurring octad carries exactly the displayed original code label. -/
theorem generatedSixth_final_octad_cache_label (f : Fin 231) :
    golayOctadLabel (generatedSixthFinalOctadCacheOctad f) =
      generatedSixthFinalOctadCacheCode f := by
  rw [generatedSixthFinalOctadCacheOctad, generatedSixthMiddleOctad_label,
    generatedSixth_final_octad_cache_representative]

/-- All original octad rows occur in the genuine finite cache. -/
theorem generatedSixth_final_octad_cache_coverage (j : Fin 273) :
    generatedSixthMiddleOctad j =
      generatedSixthFinalOctadCacheOctad (generatedSixthFinalOctadCacheOwner j) := by
  apply golayOctadLabel_injective
  rw [generatedSixthMiddleOctad_label, generatedSixth_final_octad_cache_label,
    generatedSixth_final_octad_cache_owner]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
