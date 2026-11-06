/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPropagationData

/-! Compressed binary certificates for the 56 ordered root decompositions.
The bit set is computed from the checked local integer roots, and its complete
binding to their eight binary coordinates is checked by the Lean kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The ordinary eight-bit label of each actual local root pattern. -/
def generatedOctadPatternMask : Fin 120 → Fin 256 :=
  ![1, 2, 4, 8, 16, 32, 63, 3, 5, 9, 17, 33, 62, 6, 10, 18,
    34, 61, 12, 20, 36, 59, 24, 40, 55, 48, 47, 31, 64, 67, 69, 73,
    81, 97, 126, 66, 68, 72, 80, 96, 127, 71, 75, 83, 99, 124, 77, 85,
    101, 122, 89, 105, 118, 113, 110, 94, 128, 225, 224, 192, 227, 195, 194, 163,
    229, 197, 196, 165, 199, 166, 167, 135, 233, 201, 200, 169, 203, 170, 171, 139,
    205, 172, 173, 141, 174, 142, 143, 238, 241, 209, 208, 177, 211, 178, 179, 147,
    213, 180, 181, 149, 182, 150, 151, 246, 217, 184, 185, 153, 186, 154, 155, 250,
    188, 156, 157, 252, 158, 255, 254, 222]

/-- Decode an eight-bit label into the corresponding binary coordinate vector. -/
def generatedOctadMaskBits (m : Fin 256) (j : Fin 8) : ZMod 2 :=
  if m.val.testBit j.val then 1 else 0

/-- Exact physical-pattern binding of the compressed binary labels. -/
theorem generatedOctadPatternMask_bits : ∀ p : Fin 120,
    generatedOctadMaskBits (generatedOctadPatternMask p) = generatedOctadPatternBits p := by
  decide +kernel

/-- The compressed root labels are distinct. -/
theorem generatedOctadPatternMask_injective : Function.Injective generatedOctadPatternMask := by
  decide +kernel

/-- The bit set of precisely the 120 root labels. -/
def generatedOctadRootMaskSet : ℕ :=
  96007392487432813274984884115030220198974927479942110629818158251892649957246

/-- The bit set contains exactly the labels of the actual 120 patterns. -/
theorem generatedOctadRootMaskSet_exact : ∀ m : Fin 256,
    generatedOctadRootMaskSet.testBit m.val = true ↔
      ∃ p : Fin 120, generatedOctadPatternMask p = m := by decide +kernel

/-- For each root label exactly 56 binary labels decompose it into two roots. -/
theorem generatedOctadRootMaskSet_pair_count : ∀ p : Fin 120,
    (Finset.univ.filter (fun m : Fin 256 =>
      generatedOctadRootMaskSet.testBit m.val = true ∧
      generatedOctadRootMaskSet.testBit (Nat.xor m.val (generatedOctadPatternMask p).val) =
        true)).card = 56 := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
