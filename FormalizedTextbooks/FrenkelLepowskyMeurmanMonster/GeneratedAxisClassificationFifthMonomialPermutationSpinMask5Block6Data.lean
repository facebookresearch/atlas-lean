/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Blocks

/-! Exact integer row certificates retain every original phase in this bounded word block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original signed input model of this bounded block. -/
def generatedFifthPermutationMask5Input6 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        270, 768, 269, 1310, 2034, 818,
        564, 1660, 122, 458, 819, 2094
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        14, 68, 604, 664, 1408, 1696,
        384, 1536, 1280, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block6 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((1, true),
      ⟨fun i => ((![
        432, 122, 713, 1754, 1160, 64,
        504, 1464, 768, 526, 1824, 2094
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1822, 798, 1688, 1048, 704, 736,
        384, 384, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1028, 3897, 2253, 2957, 1528, 3568,
        912, 528, 1599, 1266, 152, 2048
      ],
      ![
        1296, 151, 1937, 1695, 1408, 1696,
        48, 1994, 1110, 1691, 432, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1096, 738, 1615, 1089, 536, 600,
        720, 1896, 1259, 1280, 1680, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        888, 1866, 736, 1248, 1040, 896,
        1152, 640, 1536, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4, 2570, 2560, 2782, 203, 3267,
        110, 221, 1473, 1804, 1176, 2048
      ],
      ![
        770, 1811, 440, 1543, 471, 1737,
        1215, 664, 564, 12, 1328, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input6 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input6 =
      generatedFifthPermutationPlan5Input6 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block6 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block6 =
      generatedFifthPermutationPlan5Block6 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
