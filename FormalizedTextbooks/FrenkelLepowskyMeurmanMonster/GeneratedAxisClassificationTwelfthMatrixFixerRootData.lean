/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerFrame

/-! Whole root permutations and prefix-orbit witnesses of three actual whole matrix fixers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original 120-root images of the three entire original matrix fixing words. -/
def generatedTwelfthMatrixFixerRootForward : Fin 3 → Fin 120 → Fin 120 :=
  ![![9, 18, 24, 50, 31, 23, 14, 8, 12, 38, 28, 11, 7, 21, 47, 30, 20, 13, 54, 34, 27, 17, 4,
    53, 43, 33, 29, 16, 37, 46, 52, 22, 3, 51, 42, 36, 40, 10, 0, 39, 35, 49, 19, 2, 48, 41,
    26, 6, 55, 45, 32, 25, 15, 5, 1, 44, 89, 105, 91, 107, 97, 113, 99, 115, 86, 70, 84, 68,
    78, 62, 76, 60, 57, 73, 59, 75, 65, 81, 67, 83, 118, 102, 116, 100, 110, 94, 108, 92, 88,
    104, 90, 106, 96, 112, 98, 114, 87, 71, 85, 69, 79, 63, 77, 61, 56, 72, 58, 74, 64, 80, 66,
    82, 119, 103, 117, 101, 111, 95, 109, 93], ![0, 69, 61, 37, 3, 65, 57, 70, 62, 31, 9, 66,
    58, 48, 87, 84, 44, 41, 79, 76, 13, 16, 28, 83, 75, 80, 72, 20, 50, 118, 110, 4, 38, 114,
    106, 117, 109, 10, 32, 113, 105, 17, 100, 103, 21, 27, 92, 95, 55, 49, 22, 96, 88, 99, 91,
    45, 26, 93, 94, 52, 19, 89, 90, 46, 53, 97, 98, 23, 15, 86, 85, 42, 111, 6, 12, 63, 107, 2,
    8, 59, 115, 33, 39, 67, 68, 1, 7, 116, 108, 40, 34, 60, 104, 36, 30, 56, 112, 11, 5, 64,
    71, 35, 29, 119, 24, 77, 78, 54, 18, 73, 74, 47, 51, 81, 82, 25, 14, 102, 101, 43], ![90,
    31, 56, 88, 30, 34, 92, 107, 38, 11, 99, 84, 7, 73, 105, 18, 24, 109, 53, 65, 118, 43, 97,
    86, 16, 21, 101, 82, 60, 49, 94, 62, 52, 46, 58, 77, 44, 15, 69, 114, 25, 111, 79, 6, 2,
    75, 35, 103, 80, 39, 71, 112, 10, 3, 67, 116, 63, 87, 12, 28, 70, 104, 9, 36, 54, 4, 59,
    83, 50, 19, 66, 108, 27, 33, 91, 115, 23, 48, 98, 76, 57, 81, 45, 1, 64, 110, 42, 13, 78,
    96, 8, 37, 113, 89, 0, 40, 47, 22, 74, 100, 32, 26, 117, 93, 20, 51, 106, 68, 5, 55, 85,
    61, 72, 102, 41, 14, 119, 95, 29, 17]]

/-- Each original whole word yields precisely this entire original root permutation. -/
theorem generatedTwelfth_matrix_fixer_root_source : ∀ (g : Fin 3) (r : Fin 120),
    (generatedTwelfthMatrixFixerWord g).foldr generatedTwelfthRootFiniteLetter r =
      generatedTwelfthMatrixFixerRootForward g r := by
  decide +kernel

/-- Every genuine inverse uses the exact original inverse of its complete root permutation. -/
def generatedTwelfthMatrixFixerRootBackward : Fin 3 → Fin 120 → Fin 120 :=
  ![![38, 54, 43, 32, 22, 53, 47, 12, 7, 0, 37, 11, 8, 17, 6, 52, 27, 21, 1, 42, 16, 13, 31, 5,
    2, 51, 46, 20, 10, 26, 15, 4, 50, 25, 19, 40, 35, 28, 9, 39, 36, 45, 34, 24, 55, 49, 29,
    14, 44, 41, 3, 33, 30, 23, 18, 48, 104, 72, 106, 74, 71, 103, 69, 101, 108, 76, 110, 78,
    67, 99, 65, 97, 105, 73, 107, 75, 70, 102, 68, 100, 109, 77, 111, 79, 66, 98, 64, 96, 88,
    56, 90, 58, 87, 119, 85, 117, 92, 60, 94, 62, 83, 115, 81, 113, 89, 57, 91, 59, 86, 118,
    84, 116, 93, 61, 95, 63, 82, 114, 80, 112], ![0, 85, 77, 4, 31, 98, 73, 86, 78, 10, 37, 97,
    74, 20, 116, 68, 21, 41, 108, 60, 27, 44, 50, 67, 104, 115, 56, 45, 22, 102, 94, 9, 38, 81,
    90, 101, 93, 3, 32, 82, 89, 17, 71, 119, 16, 55, 63, 111, 13, 49, 28, 112, 59, 64, 107, 48,
    95, 6, 12, 79, 91, 2, 8, 75, 99, 5, 11, 83, 84, 1, 7, 100, 26, 109, 110, 24, 19, 105, 106,
    18, 25, 113, 114, 23, 15, 70, 69, 14, 52, 61, 62, 54, 46, 57, 58, 47, 51, 65, 66, 53, 42,
    118, 117, 43, 92, 40, 34, 76, 88, 36, 30, 72, 96, 39, 33, 80, 87, 35, 29, 103], ![94, 83,
    44, 53, 65, 108, 43, 12, 90, 62, 52, 9, 58, 87, 115, 37, 24, 119, 15, 69, 104, 25, 97, 76,
    16, 40, 101, 72, 59, 118, 4, 1, 100, 73, 5, 46, 63, 91, 8, 49, 95, 114, 86, 21, 36, 82, 33,
    96, 77, 29, 68, 105, 32, 18, 64, 109, 2, 80, 34, 66, 28, 111, 31, 56, 84, 19, 70, 54, 107,
    38, 60, 50, 112, 13, 98, 45, 79, 35, 88, 42, 48, 81, 27, 67, 11, 110, 23, 57, 3, 93, 0, 74,
    6, 103, 30, 117, 89, 22, 78, 10, 99, 26, 113, 47, 61, 14, 106, 7, 71, 17, 85, 41, 51, 92,
    39, 75, 55, 102, 20, 116]]

/-- The finite original inverse dictionary really inverts all 120 original root addresses. -/
theorem generatedTwelfth_matrix_fixer_root_inverse : ∀ (g : Fin 3) (r : Fin 120),
    generatedTwelfthMatrixFixerRootForward g (generatedTwelfthMatrixFixerRootBackward g r) = r := by
  decide +kernel

/-- Original positive and inverse letters in the three entire true matrix fixers. -/
def generatedTwelfthMatrixFixerRootFiniteLetter (l : Fin 3 × Bool) (r : Fin 120) : Fin 120 :=
  if l.2 then generatedTwelfthMatrixFixerRootBackward l.1 r
  else generatedTwelfthMatrixFixerRootForward l.1 r

/-- Distinct prefix-orbit witnesses, each a word in the three original entire matrix fixers. -/
def generatedTwelfthMatrixFixerRootWitnessWord : Fin 86 → List (Fin 3 × Bool) :=
  ![
    [],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (0, false), (0,
    false), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false),
    (1, true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(0, false), (1, false), (0, false), (0, false)],
    [(1, false), (1, false), (0, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false), (1, false), (0, false), (0, false), (1, false), (1, false),
    (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1, true), (2, true),
    (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1,
    true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1,
    false)],
    [(0, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2,
    true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2,
    false), (2, false), (1, false), (1, false), (2, false), (1, false), (1, true), (2, true),
    (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1,
    true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1,
    false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false),
    (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false),
    (2, false), (2, false), (1, false), (1, false)],
    [(2, false), (2, false)],
    [(0, false)],
    [(2, true), (0, false), (2, false), (1, false), (0, false), (2, true), (0, false), (2,
    false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false),
    (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false),
    (2, false), (2, false), (1, false), (1, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false),
    (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true),
    (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(2, false), (0, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false), (2, false), (1, false), (1, true), (2, true), (0, false),
    (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true),
    (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1,
    false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true),
    (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false),
    (2, false), (1, false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (0, false), (1,
    false), (2, false), (2, true), (0, false), (2, false), (1, true), (2, true), (0, false),
    (2, false), (1, false), (1, false)],
    [(0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (0,
    false), (0, false), (1, false), (1, false), (1, false), (1, true), (2, true), (0, false),
    (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true),
    (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(2, false), (2, false), (0, false), (0, false)],
    [(0, false), (1, false), (0, false)],
    [(2, true), (0, false), (2, false), (2, false), (2, false), (0, false), (1, false), (2,
    true), (0, false), (2, false), (1, true), (2, true), (0, false), (2, false), (1, false),
    (1, false)],
    [(1, false), (0, false), (1, false), (0, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1, false), (2,
    false), (2, true), (0, false), (2, false)],
    [(1, false), (0, false)],
    [(1, false), (0, false), (0, false)],
    [(1, false), (2, false)],
    [(2, true), (0, false), (2, false), (1, false), (0, false), (0, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false), (1, false)],
    [(0, true)],
    [(0, false), (1, false), (2, false)],
    [(2, true), (0, false), (2, false), (0, false), (1, false), (0, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(2, false), (1, false), (0, false), (0, false)],
    [(2, false), (0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (0, false), (0, false), (1, false), (1, true), (2, true), (0, false), (2, false),
    (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true),
    (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2,
    false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    false), (1, false)],
    [(0, false), (0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (0, false), (0, false), (1, false), (0, true), (1, true), (2, true), (1, false),
    (2, false), (2, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1,
    false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1,
    false), (2, false), (2, false), (1, false), (1, false)],
    [(2, true), (0, false), (2, false), (2, false), (0, true), (1, true), (2, true), (1,
    false), (2, false), (2, false), (2, true), (0, false), (2, false), (1, false), (1, true),
    (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2,
    false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(2, false), (1, false), (2, false), (0, false)],
    [(1, false), (0, false), (2, true), (0, false), (2, false), (2, false), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1, true),
    (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(2, false), (1, false), (0, false)],
    [(2, false), (2, false), (2, false), (0, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (0, false), (1, true), (2, true), (0,
    false), (2, false), (1, false), (1, false), (0, true), (1, true), (2, true), (1, false),
    (2, false), (2, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1,
    false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1,
    false), (2, false), (2, false), (1, false), (1, false)],
    [(1, false), (2, false), (0, false)],
    [(2, true), (0, false), (2, false), (0, false), (1, false), (2, false)],
    [(1, false), (2, false), (2, false), (0, false)],
    [(2, false), (0, false), (0, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (0, false), (1,
    false), (2, true), (0, false), (2, false), (1, true), (2, true), (0, false), (2, false),
    (1, false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, true),
    (2, true), (0, false), (2, false), (1, false), (1, false), (1, false), (1, true), (2,
    true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false),
    (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false),
    (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2,
    false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    false), (1, false)],
    [(2, true), (0, false), (2, false), (1, false), (2, false), (1, false), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1, true),
    (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (0,
    false), (1, false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false),
    (1, false), (1, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (2, false), (2,
    false), (2, true), (0, false), (2, false), (1, true), (2, true), (0, false), (2, false),
    (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true),
    (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1, true), (2,
    true), (0, false), (2, false), (1, false), (1, false), (1, true), (2, true), (0, false),
    (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true),
    (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(2, false), (0, false), (1, false), (2, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (0, false), (1, false), (0, false),
    (1, false), (2, true), (0, false), (2, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(2, false), (2, false), (0, false)],
    [(2, true), (0, false), (2, false), (2, false), (0, false), (1, false), (1, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (2, false), (0,
    false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true),
    (0, false), (2, false), (2, true), (0, false), (2, false), (1, true), (2, true), (0,
    false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true),
    (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(2, false), (0, false), (1, false), (0, false), (0, false)],
    [(2, false)],
    [(0, false), (2, true), (0, false), (2, false), (2, false), (0, true), (1, true), (2,
    true), (1, false), (2, false), (2, false), (2, true), (0, false), (2, false), (1, false),
    (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true),
    (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false),
    (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(2, true), (0, false), (2, false), (2, false), (2, false), (0, true), (1, true), (2,
    true), (1, false), (2, false), (2, false), (1, false)],
    [(2, true), (0, false), (2, false), (0, true), (1, true), (2, true), (1, false), (2,
    false), (2, false), (0, false), (0, false), (1, true), (2, true), (0, false), (2, false),
    (1, false), (1, false), (2, true), (0, false), (2, false), (2, true), (0, false), (2,
    false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true),
    (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false),
    (2, false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1,
    false), (1, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (0,
    false), (2, true), (0, false), (2, false), (1, true), (2, true), (0, false), (2, false),
    (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true),
    (2, true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(0, false), (2, false), (1, false), (0, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (0, false), (1,
    false), (0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false),
    (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(1, false), (1, false), (2, false)],
    [(1, false), (0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (0, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false),
    (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, true), (2, true),
    (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1,
    true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1,
    false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1, true),
    (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2,
    false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    false), (1, false)],
    [(0, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (2,
    false), (0, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false),
    (2, true), (0, false), (2, false), (2, true), (0, false), (2, false), (1, true), (2, true),
    (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1,
    true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1,
    false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, false), (1,
    false), (0, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false),
    (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2,
    true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2,
    false), (2, false), (1, false), (1, false)],
    [],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false), (1, false), (1, false), (1, true), (2, true), (0, false),
    (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true),
    (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false), (1, true), (2, true), (0,
    false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true),
    (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(2, true), (0, false), (2, false), (1, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false),
    (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true),
    (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(1, false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1,
    false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2,
    true), (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1,
    true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1, true),
    (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2,
    true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2,
    false), (2, false), (1, false), (1, false), (1, false), (1, true), (2, true), (0, false),
    (2, false), (1, false), (1, false), (2, true), (0, true), (2, false), (1, true), (0, true),
    (1, true), (2, true), (1, false), (2, false), (2, false), (1, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(1, false), (2, true), (0, false), (2, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false)],
    [(2, true), (0, false), (2, false), (0, true), (1, true), (2, true), (1, false), (2,
    false), (2, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false),
    (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false),
    (2, false), (2, false), (1, false), (1, false), (1, true), (2, true), (0, false), (2,
    false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false),
    (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true),
    (1, false), (2, false), (2, false), (1, false), (1, false)],
    [(1, false), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false), (1, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false)],
    [(2, true), (0, false), (2, false), (2, true), (0, false), (2, false), (1, true), (2,
    true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2, false),
    (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1, false),
    (1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2,
    false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1, false), (1,
    true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0, true), (2,
    false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (1,
    false), (1, false)],
    [(1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    false), (2, false), (2, true), (0, false), (2, false)],
    [(0, true), (1, true), (2, true), (1, false), (2, false), (2, false), (2, true), (0,
    false), (2, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false),
    (1, false), (2, true), (0, true), (2, false), (1, true), (0, true), (1, true), (2, true),
    (1, false), (2, false), (2, false), (1, false), (1, false), (1, true), (2, true), (0,
    false), (2, false), (1, false), (1, false)],
    [(1, false), (1, false)],
    [(2, true), (0, false), (2, false)],
    [(1, false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (1,
    false), (1, true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false)],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false), (1, true), (2, true), (0, false), (2, false), (1, false),
    (1, false)],
    [],
    [],
    [(1, true), (2, true), (0, false), (2, false), (1, false), (1, false), (2, true), (0,
    true), (2, false), (1, true), (0, true), (1, true), (2, true), (1, false), (2, false), (2,
    false), (1, false), (1, false)]]

/-- Exact distinct target addresses of the original prefix-orbit witnesses. -/
def generatedTwelfthMatrixFixerRootWitnessTarget : Fin 86 → Fin 120 :=
  ![0, 1, 3, 4, 5, 7, 8, 9, 10, 11, 12, 15, 18, 19, 22, 23, 28, 30, 31, 32, 34, 37, 38, 42, 50,
    52, 53, 54, 58, 59, 60, 62, 64, 65, 66, 67, 68, 69, 70, 71, 74, 76, 78, 79, 83, 84, 85, 86,
    88, 90, 91, 94, 97, 98, 99, 100, 106, 107, 108, 110, 1, 3, 4, 5, 7, 9, 10, 11, 31, 32, 37,
    38, 65, 66, 69, 70, 85, 86, 97, 98, 2, 6, 89, 3, 4, 86]

/-- The five certified actual prefix-orbit lower bounds. -/
def generatedTwelfthMatrixFixerRootOrbitBound : Fin 5 → ℕ := ![60, 20, 3, 1, 2]

/-- Every prefix-orbit witness has its original complete source-word address. -/
def generatedTwelfthMatrixFixerRootWitnessNumber (k : Fin 5) :
    Fin (generatedTwelfthMatrixFixerRootOrbitBound k) → Fin 86 :=
  match k with
  | 0 => ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
  | 1 => ![60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
  | 2 => ![80, 81, 82]
  | 3 => ![83]
  | 4 => ![84, 85]


/-- Finite whole word evaluation on the actual original root addresses. -/
def generatedTwelfthMatrixFixerRootFiniteWord (n : Fin 86) (r : Fin 120) : Fin 120 :=
  (generatedTwelfthMatrixFixerRootWitnessWord n).foldr generatedTwelfthMatrixFixerRootFiniteLetter r

/-- Every original prefix witness fixes every preceding original root. -/
theorem generatedTwelfth_matrix_fixer_root_witness_prefix :
    ∀ (k : Fin 5) (j : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)) (r : Fin 120),
      r.val < k.val → generatedTwelfthMatrixFixerRootFiniteWord
        (generatedTwelfthMatrixFixerRootWitnessNumber k j) r = r := by
  decide +kernel

/-- Every full prefix witness reaches precisely its original displayed root target. -/
theorem generatedTwelfth_matrix_fixer_root_witness_target :
    ∀ (k : Fin 5) (j : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)),
      generatedTwelfthMatrixFixerRootFiniteWord (generatedTwelfthMatrixFixerRootWitnessNumber k j)
          (Fin.castLE (by decide : 5 ≤ 120) k) =
        generatedTwelfthMatrixFixerRootWitnessTarget
          (generatedTwelfthMatrixFixerRootWitnessNumber k j) := by
  decide +kernel

/-- Every prefix witness target is distinct within its entire displayed original orbit. -/
theorem generatedTwelfth_matrix_fixer_root_targets_distinct :
    ∀ (k : Fin 5) (j l : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)),
      generatedTwelfthMatrixFixerRootWitnessTarget
          (generatedTwelfthMatrixFixerRootWitnessNumber k j) =
        generatedTwelfthMatrixFixerRootWitnessTarget
          (generatedTwelfthMatrixFixerRootWitnessNumber k l) → j = l := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
