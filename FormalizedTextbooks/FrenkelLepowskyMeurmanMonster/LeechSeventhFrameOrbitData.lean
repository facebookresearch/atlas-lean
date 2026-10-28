/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2FrameComplement
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Orbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction

/-! Bounded actual section words fixing the original triangle and reaching 27 frame classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Explicit inverse root addresses of the eighteen actual section generators. -/
def leechSeventhFrameRootInverse : Fin 18 → Fin 120 → Fin 120 :=
  ![![0, 1, 2, 31, 32, 33, 34, 7, 8, 37, 38, 39, 40, 13, 42,
      43, 44, 45, 46, 47, 48, 49, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 3, 4, 5, 6, 35, 36, 9, 10, 11, 12, 41, 14, 15, 16,
      17, 18, 19, 20, 21, 50, 51, 52, 53, 54, 55, 71, 70, 69, 68,
      67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 87, 86, 85,
      84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 103, 102,
      101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 119,
      118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104],
    ![0, 1, 2, 31, 32, 33, 34, 7, 8, 37, 38, 39, 40, 13, 42,
      43, 44, 45, 46, 47, 48, 49, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 3, 4, 5, 6, 35, 36, 9, 10, 11, 12, 41, 14, 15, 16,
      17, 18, 19, 20, 21, 50, 51, 52, 53, 54, 55, 71, 70, 69, 68,
      67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 87, 86, 85,
      84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 103, 102,
      101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 119,
      118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
      15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
      45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
      60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
      75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
      90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
      105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119],
    ![0, 1, 2, 31, 32, 33, 34, 7, 8, 37, 38, 39, 40, 13, 42,
      43, 44, 45, 46, 47, 48, 49, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 3, 4, 5, 6, 35, 36, 9, 10, 11, 12, 41, 14, 15, 16,
      17, 18, 19, 20, 21, 50, 51, 52, 53, 54, 55, 71, 70, 69, 68,
      67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 87, 86, 85,
      84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 103, 102,
      101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 119,
      118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104],
    ![0, 1, 2, 3, 4, 33, 34, 7, 8, 9, 10, 39, 40, 13, 14,
      15, 44, 45, 18, 19, 48, 49, 22, 51, 52, 53, 54, 27, 28, 29,
      30, 31, 32, 5, 6, 35, 36, 37, 38, 11, 12, 41, 42, 43, 16,
      17, 46, 47, 20, 21, 50, 23, 24, 25, 26, 55, 119, 118, 117, 116,
      115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101,
      100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86,
      85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71,
      70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56],
    ![0, 1, 2, 3, 32, 5, 34, 7, 8, 9, 38, 11, 40, 13, 14,
      43, 16, 45, 18, 47, 20, 49, 50, 23, 52, 53, 26, 55, 28, 29,
      30, 31, 4, 33, 6, 35, 36, 37, 10, 39, 12, 41, 42, 15, 44,
      17, 46, 19, 48, 21, 22, 51, 24, 25, 54, 27, 87, 86, 85, 84,
      83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69,
      68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 119, 118,
      117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103,
      102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88],
    ![0, 1, 2, 3, 32, 5, 34, 7, 8, 9, 38, 11, 40, 13, 14,
      43, 16, 45, 18, 47, 20, 49, 50, 23, 52, 53, 26, 55, 28, 29,
      30, 31, 4, 33, 6, 35, 36, 37, 10, 39, 12, 41, 42, 15, 44,
      17, 46, 19, 48, 21, 22, 51, 24, 25, 54, 27, 87, 86, 85, 84,
      83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69,
      68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 119, 118,
      117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103,
      102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88],
    ![0, 1, 2, 3, 32, 33, 6, 7, 8, 9, 38, 39, 12, 13, 14,
      43, 44, 17, 18, 47, 48, 21, 50, 51, 24, 25, 54, 55, 28, 29,
      30, 31, 4, 5, 34, 35, 36, 37, 10, 11, 40, 41, 42, 15, 16,
      45, 46, 19, 20, 49, 22, 23, 52, 53, 26, 27, 88, 89, 90, 91,
      92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
      107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 56, 57,
      58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72,
      73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87],
    ![0, 29, 30, 3, 32, 33, 6, 35, 36, 9, 38, 39, 12, 13, 42,
      15, 16, 45, 46, 19, 20, 49, 50, 51, 24, 25, 54, 55, 28, 1,
      2, 31, 4, 5, 34, 7, 8, 37, 10, 11, 40, 41, 14, 43, 44,
      17, 18, 47, 48, 21, 22, 23, 52, 53, 26, 27, 100, 101, 102, 103,
      96, 97, 98, 99, 92, 93, 94, 95, 88, 89, 90, 91, 116, 117, 118,
      119, 112, 113, 114, 115, 108, 109, 110, 111, 104, 105, 106, 107, 68, 69,
      70, 71, 64, 65, 66, 67, 60, 61, 62, 63, 56, 57, 58, 59, 84,
      85, 86, 87, 80, 81, 82, 83, 76, 77, 78, 79, 72, 73, 74, 75],
    ![28, 1, 30, 3, 4, 33, 34, 35, 8, 37, 38, 11, 12, 41, 14,
      15, 44, 45, 46, 47, 20, 21, 22, 51, 52, 53, 54, 27, 0, 29,
      2, 31, 32, 5, 6, 7, 36, 9, 10, 39, 40, 13, 42, 43, 16,
      17, 18, 19, 48, 49, 50, 23, 24, 25, 26, 55, 109, 108, 111, 110,
      105, 104, 107, 106, 117, 116, 119, 118, 113, 112, 115, 114, 93, 92, 95,
      94, 89, 88, 91, 90, 101, 100, 103, 102, 97, 96, 99, 98, 77, 76,
      79, 78, 73, 72, 75, 74, 85, 84, 87, 86, 81, 80, 83, 82, 61,
      60, 63, 62, 57, 56, 59, 58, 69, 68, 71, 70, 65, 64, 67, 66],
    ![28, 29, 30, 31, 4, 5, 6, 7, 8, 9, 38, 39, 40, 13, 14,
      43, 44, 45, 18, 47, 48, 49, 50, 51, 52, 25, 26, 27, 0, 1,
      2, 3, 32, 33, 34, 35, 36, 37, 10, 11, 12, 41, 42, 15, 16,
      17, 46, 19, 20, 21, 22, 23, 24, 53, 54, 55, 86, 87, 84, 85,
      82, 83, 80, 81, 78, 79, 76, 77, 74, 75, 72, 73, 70, 71, 68,
      69, 66, 67, 64, 65, 62, 63, 60, 61, 58, 59, 56, 57, 118, 119,
      116, 117, 114, 115, 112, 113, 110, 111, 108, 109, 106, 107, 104, 105, 102,
      103, 100, 101, 98, 99, 96, 97, 94, 95, 92, 93, 90, 91, 88, 89],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
      15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
      45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
      60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
      75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
      90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
      105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119],
    ![11, 27, 20, 23, 25, 5, 16, 12, 8, 9, 10, 0, 7, 21, 24,
      26, 6, 17, 18, 19, 2, 13, 22, 3, 14, 4, 15, 1, 39, 55,
      48, 51, 53, 33, 44, 40, 36, 37, 38, 28, 35, 49, 52, 54, 34,
      45, 46, 47, 30, 41, 50, 31, 42, 32, 43, 29, 56, 57, 59, 58,
      118, 119, 117, 116, 65, 64, 66, 67, 111, 110, 108, 109, 73, 72, 74,
      75, 103, 102, 100, 101, 80, 81, 83, 82, 94, 95, 93, 92, 89, 88,
      90, 91, 87, 86, 84, 85, 96, 97, 99, 98, 78, 79, 77, 76, 104,
      105, 107, 106, 70, 71, 69, 68, 113, 112, 114, 115, 63, 62, 60, 61],
    ![1, 0, 2, 4, 3, 5, 6, 7, 13, 15, 14, 16, 17, 8, 10,
      9, 11, 12, 19, 18, 20, 21, 22, 25, 26, 23, 24, 27, 29, 28,
      30, 32, 31, 33, 34, 35, 41, 43, 42, 44, 45, 36, 38, 37, 39,
      40, 47, 46, 48, 49, 50, 53, 54, 51, 52, 55, 56, 57, 60, 61,
      58, 59, 62, 63, 64, 65, 68, 69, 66, 67, 70, 71, 88, 89, 92,
      93, 90, 91, 94, 95, 96, 97, 100, 101, 98, 99, 102, 103, 72, 73,
      76, 77, 74, 75, 78, 79, 80, 81, 84, 85, 82, 83, 86, 87, 104,
      105, 108, 109, 106, 107, 110, 111, 112, 113, 116, 117, 114, 115, 118, 119],
    ![13, 1, 7, 14, 15, 16, 17, 2, 8, 18, 19, 20, 21, 0, 3,
      4, 5, 6, 9, 10, 11, 12, 22, 23, 24, 25, 26, 27, 41, 29,
      35, 42, 43, 44, 45, 30, 36, 46, 47, 48, 49, 28, 31, 32, 33,
      34, 37, 38, 39, 40, 50, 51, 52, 53, 54, 55, 56, 60, 64, 68,
      57, 61, 65, 69, 58, 62, 66, 70, 59, 63, 67, 71, 72, 76, 80,
      84, 73, 77, 81, 85, 74, 78, 82, 86, 75, 79, 83, 87, 88, 92,
      96, 100, 89, 93, 97, 101, 90, 94, 98, 102, 91, 95, 99, 103, 104,
      108, 112, 116, 105, 109, 113, 117, 106, 110, 114, 118, 107, 111, 115, 119],
    ![0, 1, 5, 4, 3, 2, 6, 7, 11, 10, 9, 8, 12, 16, 15,
      14, 13, 17, 25, 23, 20, 27, 22, 19, 26, 18, 24, 21, 28, 29,
      33, 32, 31, 30, 34, 35, 39, 38, 37, 36, 40, 44, 43, 42, 41,
      45, 53, 51, 48, 55, 50, 47, 54, 46, 52, 49, 56, 65, 66, 59,
      68, 61, 62, 71, 64, 57, 58, 67, 60, 69, 70, 63, 96, 89, 90,
      99, 92, 101, 102, 95, 88, 97, 98, 91, 100, 93, 94, 103, 80, 73,
      74, 83, 76, 85, 86, 79, 72, 81, 82, 75, 84, 77, 78, 87, 104,
      113, 114, 107, 116, 109, 110, 119, 112, 105, 106, 115, 108, 117, 118, 111],
    ![4, 15, 25, 26, 19, 22, 10, 1, 5, 6, 2, 3, 0, 16, 17,
      13, 14, 7, 27, 20, 23, 11, 21, 24, 12, 18, 8, 9, 32, 43,
      53, 54, 47, 50, 38, 29, 33, 34, 30, 31, 28, 44, 45, 41, 42,
      35, 55, 48, 51, 39, 49, 52, 40, 46, 36, 37, 56, 104, 73, 89,
      76, 92, 61, 109, 72, 88, 57, 105, 60, 108, 77, 93, 103, 87, 118,
      70, 115, 67, 98, 82, 119, 71, 102, 86, 99, 83, 114, 66, 80, 96,
      65, 113, 68, 116, 85, 101, 64, 112, 81, 97, 84, 100, 69, 117, 111,
      63, 94, 78, 91, 75, 106, 58, 95, 79, 110, 62, 107, 59, 90, 74],
    ![41, 36, 35, 86, 89, 57, 118, 7, 8, 74, 101, 69, 106, 13, 76,
      99, 67, 108, 80, 95, 63, 112, 55, 54, 53, 25, 26, 27, 0, 1,
      2, 73, 102, 70, 105, 30, 29, 85, 90, 58, 117, 28, 83, 92, 60,
      115, 79, 96, 64, 111, 22, 23, 24, 52, 51, 50, 31, 87, 75, 37,
      77, 42, 18, 78, 81, 46, 14, 82, 9, 84, 72, 3, 33, 56, 68,
      39, 66, 44, 20, 65, 62, 48, 16, 61, 11, 59, 71, 5, 6, 119,
      107, 12, 109, 17, 49, 110, 113, 21, 45, 114, 40, 116, 104, 34, 32,
      103, 91, 38, 93, 43, 19, 94, 97, 47, 15, 98, 10, 100, 88, 4]]

/-- Bit masks for the actual inverse eight-coordinate generator matrices. -/
def leechSeventhFrameInverseRows : Fin 18 → Fin 8 → ℕ :=
  ![![185, 130, 132, 8, 16, 32, 120, 128],
    ![185, 130, 132, 8, 16, 32, 120, 128],
    ![1, 2, 4, 8, 16, 32, 64, 128],
    ![185, 130, 132, 8, 16, 32, 120, 128],
    ![33, 130, 132, 136, 144, 32, 224, 128],
    ![17, 130, 132, 136, 16, 160, 208, 128],
    ![17, 130, 132, 136, 16, 160, 208, 128],
    ![177, 2, 4, 8, 144, 160, 240, 128],
    ![55, 130, 132, 8, 144, 160, 118, 128],
    ![100, 130, 4, 136, 144, 32, 37, 128],
    ![206, 130, 132, 136, 16, 32, 15, 128],
    ![1, 2, 4, 8, 16, 32, 64, 128],
    ![3, 2, 6, 10, 18, 125, 64, 128],
    ![66, 65, 4, 16, 8, 32, 64, 128],
    ![68, 127, 65, 8, 16, 32, 64, 128],
    ![1, 2, 32, 16, 8, 4, 64, 128],
    ![72, 10, 24, 40, 119, 12, 64, 128],
    ![249, 13, 11, 136, 16, 32, 183, 56]]

/-- The inverse binary matrix in original intrinsic root coordinates. -/
def leechSeventhFrameInverseMatrix (g : Fin 18) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => if (leechSeventhFrameInverseRows g i).testBit j.val then 1 else 0

/-- Every inverse root address is checked against the original forward root action. -/
theorem leechSeventhFrameRootInverse_certificate : ∀ g : Fin 18, ∀ r : Fin 120,
    leechSeventhE8RootImage g (leechSeventhFrameRootInverse g r) = r := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Only eighteen eight-dimensional inverse matrix products are checked.
/-- The literal inverse binary matrices are actual right inverses of the original matrices. -/
theorem leechSeventhFrameInverseMatrix_certificate : ∀ g : Fin 18,
    generatedFifthSectionGeneratorBinary g * leechSeventhFrameInverseMatrix g = 1 := by
  decide +kernel

/-- Root-address action of a signed original section letter. -/
def leechSeventhFrameLetterRoot (l : Fin 18 × Bool) (r : Fin 120) : Fin 120 :=
  if l.2 then leechSeventhFrameRootInverse l.1 r else leechSeventhE8RootImage l.1 r

/-- Binary intrinsic-coordinate action of a signed original section letter. -/
def leechSeventhFrameLetterMatrix (l : Fin 18 × Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  if l.2 then leechSeventhFrameInverseMatrix l.1 else generatedFifthSectionGeneratorBinary l.1

/-- Root addresses under an original signed section word, in actual left-action order. -/
def leechSeventhFrameWordRoot (w : List (Fin 18 × Bool)) (r : Fin 120) : Fin 120 :=
  w.foldr leechSeventhFrameLetterRoot r

/-- Binary root coordinates under the same actual signed word. -/
def leechSeventhFrameWordBinary (w : List (Fin 18 × Bool)) (a : Fin 8 → ZMod 2) :=
  w.foldr (fun l b => leechSeventhFrameLetterMatrix l *ᵥ b) a

/-- Twenty-seven original words fixing the triangle, with all inverse letters retained. -/
def leechSeventhFrameOrbitWord : Fin 27 → List (Fin 18 × Bool) :=
  ![[(4, true), (12, true), (16, true), (15, true), (14, true), (17, false), (14, false),
    (15, false), (16, false), (12, false)],
    [(12, true), (17, true), (8, true), (16, true), (17, true), (16, false), (17, false),
      (12, false), (15, false), (17, false), (5, false)],
    [(4, true), (12, true), (16, true), (17, true), (15, true), (0, true), (16, false),
      (16, false), (4, false), (17, false), (16, false), (4, false)],
    [(12, true), (17, true), (16, true), (17, true), (16, true), (12, false), (17, false),
      (12, false), (15, false), (17, false), (5, false)],
    [(7, true), (16, true), (13, true), (16, true), (17, false), (17, false), (15, false),
      (16, false), (12, false), (5, false)],
    [],
    [(5, true), (12, true), (16, true), (15, true), (17, true), (8, false), (14, false),
      (15, false), (16, false), (12, false)],
    [(4, true), (12, true), (13, true), (16, true), (14, true), (15, true), (14, false),
      (12, false), (14, false), (16, false), (17, false), (4, false)],
    [(12, true), (16, true), (17, true), (13, true), (17, false), (12, false), (14, false),
      (16, false), (17, false), (4, false)],
    [(4, true), (16, true), (13, true), (16, true), (17, false), (16, false), (13, false),
      (16, false)],
    [(16, true), (15, true), (16, true), (17, true), (9, false), (17, false), (12, false),
      (15, false), (17, false), (5, false)],
    [(16, true), (14, true), (17, true), (10, true), (16, true), (12, false), (15, false),
      (7, false), (16, false), (17, false), (12, false)],
    [(4, true), (17, true), (12, true), (16, true), (17, true), (17, true), (15, false),
      (17, false), (17, false), (16, false), (12, false), (17, false), (4, false)],
    [(16, true), (13, true), (17, true), (12, true), (16, true), (0, false), (17, false),
      (12, false), (15, false), (17, false), (5, false)],
    [(12, true), (17, true), (15, true), (17, true), (16, false), (15, false), (16, false),
      (15, false), (16, false), (5, false)],
    [(5, true), (12, true), (17, true), (15, true), (0, true), (14, true), (16, false),
      (10, false), (17, false), (16, false), (14, false), (12, false)],
    [(5, true), (16, true), (14, true), (16, true), (17, true), (5, false), (16, false),
      (12, false), (17, false), (13, false), (16, false)],
    [(5, true), (17, true), (12, true), (16, true), (13, false), (17, false), (15, false),
      (16, false), (12, false), (5, false)],
    [(4, true), (17, true), (15, true), (17, true), (12, true), (10, false), (17, false),
      (16, false), (16, false), (7, false)],
    [(4, true), (17, true), (4, true), (16, true), (14, true), (16, false), (12, false),
      (7, false), (17, false), (7, false)],
    [(16, true), (15, true), (16, true), (17, true), (15, true), (9, false), (10, false),
      (17, false), (16, false), (14, false), (12, false)],
    [(16, true), (13, true), (17, true), (8, true), (17, true), (12, false), (13, false),
      (12, false), (7, false), (17, false), (16, false)],
    [(5, true), (17, true), (15, true), (12, true), (17, true), (15, false), (10, false),
      (17, false), (16, false), (14, false), (12, false)],
    [(4, true), (17, true), (16, true), (14, true), (12, true), (15, false), (12, false),
      (14, false), (16, false), (17, false), (4, false)],
    [(5, true), (12, true), (17, true), (15, true), (17, true), (7, true), (16, false),
      (16, false), (12, false), (17, false), (13, false), (16, false)],
    [(5, true), (17, true), (12, true), (16, true), (10, false), (17, false), (15, false),
      (16, false), (12, false), (5, false)],
    [(16, true), (13, true), (17, true), (12, true), (16, true), (15, false), (16, false),
      (12, false), (17, false), (13, false), (16, false)]]

/-- Actual finite target labels of the twenty-seven intrinsic frame images. -/
def leechSeventhFrameOrbitLabel : Fin 27 → Fin 256 :=
  ![7, 35, 37, 38, 39, 65, 70, 98, 100, 102, 103, 129, 130, 131, 132,
      133, 134, 160, 161, 162, 164, 193, 198, 226, 228, 230, 231]

/-- The literal frame targets are distinct. -/
theorem leechSeventhFrameOrbitLabel_injective : Function.Injective leechSeventhFrameOrbitLabel := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Only 27 signed words on the original three triangle root addresses are evaluated.
/-- Each original signed word permutes the original triangle root lines. -/
theorem leechSeventhFrameOrbitWord_triangle : ∀ k : Fin 27,
    Finset.univ.image (fun j : Fin 3 =>
      leechSeventhFrameWordRoot (leechSeventhFrameOrbitWord k) (leechSeventhE8A2Indices 537 j)) =
        Finset.univ.image (leechSeventhE8A2Indices 537) := by decide +kernel

/-- Explicit intermediate eight-bit states for each original signed word. -/
def leechSeventhFrameOrbitStateTail : Fin 27 → List (Fin 256) :=
  ![[7, 26, 35, 7, 7, 65, 65, 65, 65, 65],
    [30, 95, 30, 50, 115, 95, 30, 35, 7, 65, 65],
    [100, 100, 107, 45, 53, 53, 44, 7, 7, 65, 65, 65],
    [27, 90, 92, 91, 98, 95, 30, 35, 7, 65, 65],
    [102, 104, 115, 70, 7, 65, 65, 65, 65, 65],
    [],
    [70, 91, 98, 70, 65, 65, 65, 65, 65, 65],
    [35, 30, 29, 15, 13, 49, 54, 43, 44, 7, 65, 65],
    [100, 107, 45, 54, 54, 43, 44, 7, 65, 65],
    [39, 41, 50, 7, 65, 65, 65, 65],
    [86, 106, 88, 30, 95, 30, 35, 7, 65, 65],
    [190, 187, 125, 125, 117, 117, 109, 44, 7, 65, 65],
    [220, 146, 175, 136, 78, 198, 226, 237, 35, 26, 7, 65, 65],
    [189, 190, 120, 88, 95, 95, 30, 35, 7, 65, 65],
    [164, 98, 70, 65, 65, 65, 65, 65, 65, 65],
    [235, 214, 86, 106, 106, 109, 70, 7, 65, 65, 65, 65],
    [232, 219, 219, 226, 35, 35, 26, 7, 65, 65, 65],
    [206, 15, 50, 7, 7, 65, 65, 65, 65, 65],
    [190, 120, 92, 91, 70, 7, 65, 65, 65, 65],
    [189, 123, 58, 38, 35, 26, 7, 7, 65, 65],
    [148, 168, 164, 98, 70, 70, 7, 65, 65, 65, 65],
    [193, 193, 206, 248, 57, 25, 26, 7, 7, 65, 65],
    [168, 160, 132, 164, 98, 70, 7, 65, 65, 65, 65],
    [253, 60, 52, 51, 46, 54, 43, 44, 7, 65, 65],
    [138, 183, 191, 191, 56, 56, 35, 26, 7, 65, 65, 65],
    [136, 78, 115, 70, 7, 65, 65, 65, 65, 65],
    [214, 206, 15, 50, 7, 35, 26, 7, 65, 65, 65]]

/-- A finite certificate checks each signed letter against adjacent literal states. -/
def leechSeventhFrameStatesCheck : List (Fin 18 × Bool) → List (Fin 256) → Prop
  | [], [x] => x = 65
  | l :: w, x :: y :: s => leechSeventhFrameStatesCheck w (y :: s) ∧
      leechSeventhFrameLetterMatrix l *ᵥ generatedAxisE8FrameLabelBits y =
        generatedAxisE8FrameLabelBits x
  | _, _ => False

/-- Structural decision procedure for the finite adjacent-state certificate. -/
instance leechSeventhFrameStatesCheckDecidable : (w : List (Fin 18 × Bool)) →
    (s : List (Fin 256)) → Decidable (leechSeventhFrameStatesCheck w s)
  | [], [] => isFalse id
  | [], [x] => inferInstanceAs (Decidable (x = 65))
  | [], _ :: _ :: _ => isFalse id
  | _ :: _, [] => isFalse id
  | _ :: _, [_] => isFalse id
  | l :: w, x :: y :: s =>
    letI := leechSeventhFrameStatesCheckDecidable w (y :: s)
    inferInstanceAs (Decidable (leechSeventhFrameStatesCheck w (y :: s) ∧
      leechSeventhFrameLetterMatrix l *ᵥ generatedAxisE8FrameLabelBits y =
        generatedAxisE8FrameLabelBits x))

/-- Replaying adjacent-state equalities proves the exact original word action. -/
theorem leechSeventhFrameStatesCheck_replay (w : List (Fin 18 × Bool)) (x : Fin 256)
    (s : List (Fin 256)) (h : leechSeventhFrameStatesCheck w (x :: s)) :
    leechSeventhFrameWordBinary w (generatedAxisE8FrameLabelBits 65) =
      generatedAxisE8FrameLabelBits x := by
  induction w generalizing x s with
  | nil =>
    cases s with
    | nil =>
      change x = 65 at h
      subst x
      rfl
    | cons y s => simp only [leechSeventhFrameStatesCheck] at h
  | cons l w ih =>
    cases s with
    | nil => simp only [leechSeventhFrameStatesCheck] at h
    | cons y s =>
      change leechSeventhFrameStatesCheck w (y :: s) ∧ _ at h
      change leechSeventhFrameLetterMatrix l *ᵥ
        leechSeventhFrameWordBinary w (generatedAxisE8FrameLabelBits 65) = _
      rw [ih y s h.1]
      exact h.2

set_option maxHeartbeats 4000000 in
-- Only 27 words with at most thirteen adjacent eight-dimensional state checks occur.
/-- Every intermediate state is checked using the original forward or inverse binary matrix. -/
theorem leechSeventhFrameOrbitWord_states : ∀ k : Fin 27,
    leechSeventhFrameStatesCheck (leechSeventhFrameOrbitWord k)
      (leechSeventhFrameOrbitLabel k :: leechSeventhFrameOrbitStateTail k) := by
  decide +kernel

/-- All 27 original signed words have their actual intrinsic binary target. -/
theorem leechSeventhFrameOrbitWord_binary (k : Fin 27) :
    leechSeventhFrameWordBinary (leechSeventhFrameOrbitWord k)
      (generatedAxisE8FrameLabelBits 65) =
        generatedAxisE8FrameLabelBits (leechSeventhFrameOrbitLabel k) :=
  leechSeventhFrameStatesCheck_replay _ _ _ (leechSeventhFrameOrbitWord_states k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
