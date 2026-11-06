/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpanData

/-! A finite short-root addition certificate for the actual coordinate E8 section.
The 120 patterns and propagation DAG were calculated directly from the eight
integer roots in this repository. Lean checks every addition and every bound. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All increasing local coordinate pairs in the eight-coordinate section. -/
def generatedOctadPatternPair : Fin 28 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
  (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3),
  (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6),
  (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]

/-- Every listed pair uses distinct increasing coordinates. -/
theorem generatedOctadPatternPair_lt : ∀ p : Fin 28,
    (generatedOctadPatternPair p).1 < (generatedOctadPatternPair p).2 := by decide +kernel

/-- The 56 pair patterns and 64 even-sign octad patterns. -/
def generatedOctadPatternVector (p : Fin 120) : Fin 8 → ℤ :=
  if h : p.val < 56 then
    generatedOctadIntegerPair ⟨p.val / 28, by omega⟩
      (generatedOctadPatternPair ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩).1
      (generatedOctadPatternPair ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩).2
  else generatedOctadIntegerSigns ⟨p.val - 56, by omega⟩

/-- Binary coordinates in the actual checked eight-root basis. -/
def generatedOctadPatternBits (p : Fin 120) : Fin 8 → ZMod 2 :=
  fun j => (generatedOctadIntegerRootCoordinates (generatedOctadPatternVector p) j : ZMod 2)

/-- Every one of the 120 local roots has its checked integer spanning expression. -/
theorem generatedOctadPatternVector_span : ∀ p : Fin 120,
    generatedOctadIntegerRootMatrix *ᵥ
      generatedOctadIntegerRootCoordinates (generatedOctadPatternVector p) =
        generatedOctadPatternVector p := by decide +kernel

/-- The 120 actual patterns have distinct eight-bit coordinates. -/
theorem generatedOctadPatternBits_injective : Function.Injective generatedOctadPatternBits := by
  decide +kernel

/-- The first eight nodes are the chosen basis; subsequent nodes are short-root sums. -/
def generatedOctadPropagationOrder : Fin 120 → Fin 120 :=
  ![0, 1, 2, 3, 4, 5, 28, 56, 7, 8, 9, 10, 11, 13, 14, 15,
  16, 18, 19, 20, 22, 23, 25, 29, 30, 31, 32, 33, 35, 36, 37, 38,
  39, 41, 42, 43, 44, 46, 47, 48, 50, 51, 53, 57, 58, 59, 60, 61,
  62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 54, 6, 12, 17, 21,
  24, 26, 27, 34, 40, 45, 49, 52, 55, 73, 74, 75, 76, 77, 78, 79,
  80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
  96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
  112, 113, 114, 115, 116, 117, 118, 119]

/-- First earlier parent of each of the 112 propagation nodes. -/
def generatedOctadPropagationLeft : Fin 112 → Fin 120 :=
  ![1, 2, 3, 4, 5, 2, 3, 4, 5, 3, 4, 5, 4, 5, 5, 8,
  9, 10, 11, 12, 6, 6, 6, 6, 6, 23, 23, 23, 23, 24, 24, 24,
  25, 25, 26, 27, 32, 7, 36, 23, 28, 43, 39, 24, 29, 43, 33, 43,
  44, 45, 41, 58, 59, 59, 59, 59, 59, 60, 59, 59, 59, 59, 59, 59,
  59, 25, 30, 43, 34, 43, 44, 45, 37, 43, 44, 45, 46, 47, 48, 49,
  42, 26, 31, 43, 35, 43, 44, 45, 38, 43, 44, 45, 46, 47, 48, 49,
  40, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]

/-- Second earlier parent of each of the 112 propagation nodes. -/
def generatedOctadPropagationRight : Fin 112 → Fin 120 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 6,
  6, 6, 6, 6, 1, 2, 3, 4, 5, 2, 3, 4, 5, 3, 4, 5,
  4, 5, 5, 7, 7, 6, 7, 7, 7, 28, 7, 7, 7, 29, 7, 33,
  33, 33, 7, 57, 26, 31, 35, 38, 40, 4, 42, 4, 11, 15, 18, 20,
  22, 7, 7, 30, 7, 34, 34, 34, 7, 37, 37, 37, 37, 37, 37, 37,
  7, 7, 7, 31, 7, 35, 35, 35, 7, 38, 38, 38, 38, 38, 38, 38,
  7, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40]

/-- The order lists every actual local root exactly once. -/
theorem generatedOctadPropagationOrder_bijective :
    Function.Bijective generatedOctadPropagationOrder := by
  decide +kernel

/-- The first eight ordered patterns are exactly the eight binary basis vectors. -/
theorem generatedOctadPropagation_basis : ∀ j : Fin 8,
    generatedOctadPatternBits (generatedOctadPropagationOrder ⟨j.val, by omega⟩) =
      Pi.single j 1 := by decide +kernel

/-- Every later node is the sum of its two earlier short-root parents. -/
theorem generatedOctadPropagation_step : ∀ j : Fin 112,
    (generatedOctadPropagationLeft j).val < 8 + j.val ∧
    (generatedOctadPropagationRight j).val < 8 + j.val ∧
    generatedOctadPatternBits (generatedOctadPropagationOrder ⟨8 + j.val, by omega⟩) =
      generatedOctadPatternBits (generatedOctadPropagationOrder (generatedOctadPropagationLeft j)) +
        generatedOctadPatternBits
          (generatedOctadPropagationOrder (generatedOctadPropagationRight j)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
