/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIntrinsicDifferenceSpan

/-! A finite affine reordering of the actual original144 marking coordinates. Separate
certificates bind the affine formulas, their independent directions and quotient anchors.
No full-axis stabilizer count is asserted by these data. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Eight discovered binary directions of the proposed intrinsic section. -/
def generatedNinthAffineRootMasks : Fin 8 → ℕ :=
  ![3917824, 755712, 77824, 1218411, 159531, 64, 7946500, 7328]

/-- Nine original marking anchors, retaining their actual dictionary enumeration indices. -/
def generatedNinthAffineAnchorIndex : Fin 9 → Fin 144 := ![0, 16, 17, 18, 19, 24, 25, 26, 27]

/-- The sixteen original marking indices in each proposed affine fiber. -/
def generatedNinthAffineMarkingIndex : Fin 9 → Fin 16 → Fin 144 := ![
    ![0, 1, 2, 5, 3, 4, 7, 6, 8, 14, 13, 11, 15, 9, 10, 12],
    ![16, 20, 32, 36, 57, 61, 73, 77, 88, 92, 104, 108, 113, 117, 129, 133],
    ![17, 21, 33, 37, 56, 60, 72, 76, 89, 93, 105, 109, 112, 116, 128, 132],
    ![18, 22, 34, 38, 59, 63, 75, 79, 90, 94, 106, 110, 115, 119, 131, 135],
    ![19, 23, 35, 39, 58, 62, 74, 78, 91, 95, 107, 111, 114, 118, 130, 134],
    ![24, 28, 40, 44, 49, 53, 65, 69, 80, 84, 96, 100, 121, 125, 137, 141],
    ![25, 29, 41, 45, 48, 52, 64, 68, 81, 85, 97, 101, 120, 124, 136, 140],
    ![26, 30, 42, 46, 51, 55, 67, 71, 82, 86, 98, 102, 123, 127, 139, 143],
    ![27, 31, 43, 47, 50, 54, 66, 70, 83, 87, 99, 103, 122, 126, 138, 142]]

/-- Four proposed independent binary difference directions per actual marking fiber. -/
def generatedNinthAffineDirectionMasks : Fin 9 → Fin 4 → ℕ := ![
    ![3917824, 755712, 77824, 1218411],
    ![1112128, 7946500, 7064207, 697504],
    ![77888, 5456132, 6386319, 3859616],
    ![1798208, 4731140, 7387791, 1107104],
    ![702528, 6435076, 7996047, 2139296],
    ![2830400, 5896452, 7441039, 3921056],
    ![3864640, 7600388, 8073871, 758944],
    ![2144320, 6850820, 7010959, 2200736],
    ![3240000, 4360452, 6308495, 1168544]]

/-- The little-endian label of a binary four-coordinate vector. -/
def generatedNinthAffineCoefficientLabel (a : Fin 4 → ZMod 2) : Fin 16 :=
  ⟨(∑ j, (a j).val * 2 ^ j.val) % 16, Nat.mod_lt _ (by decide)⟩

/-- The actual linear four-direction binary map of the proposed affine fiber. -/
def generatedNinthAffineDirectionMap (i : Fin 9) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  Matrix.mulVecLin (fun j k =>
    monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineDirectionMasks i k) j)

/-- The proposed eight-dimensional binary section embedding. -/
def generatedNinthAffineRootMap :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  Matrix.mulVecLin (fun j k =>
    monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineRootMasks k) j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
