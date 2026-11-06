/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-source inverse column orbit data for the D6A5 parabolic cover. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationD6A5Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationInverseWordOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteCodes

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
open scoped Matrix

/-- Literal parent labels of the original D6A5 source cover. -/
def y322Orthogonal3D6A5Parent : Fin 32 → Fin 32 :=
![
  0, 0, 1, 2, 2, 3, 3, 5, 5, 6, 7, 8, 9, 10, 11, 11, 13, 13, 14, 16, 16, 18, 19, 20, 21, 22, 23,
  25, 25, 27, 29, 30]

/-- Literal generator labels of the original D6A5 source cover. -/
def y322Orthogonal3D6A5Generator : Fin 32 → Fin 8 :=
![
  0, 6, 0, 1, 4, 2, 4, 3, 4, 0, 4, 0, 6, 0, 1, 6, 1, 6, 6, 2, 6, 0, 6, 0, 4, 0, 4, 1, 4, 4, 0, 6]

/-- Literal sortedcode labels of the original D6A5 source cover. -/
def y322Orthogonal3D6A5SortedCode : Fin 32 → ℕ :=
![
  146, 208, 759, 761, 762, 776, 777, 779, 786, 788, 789, 798, 923, 937, 938, 941, 950, 1488,
  1491, 1492, 1506, 1515, 1518, 1519, 1522, 1527, 1528, 1573, 1600, 1603, 1604, 1609]

/-- Literal sortposition labels of the original D6A5 source cover. -/
def y322Orthogonal3D6A5SortPosition : Fin 32 → Fin 32 :=
![
  0, 30, 29, 31, 24, 28, 26, 27, 23, 25, 19, 22, 11, 18, 21, 10, 17, 4, 8, 20, 2, 9, 6, 3, 16,
  7, 12, 5, 15, 14, 13, 1]

/-- Literal inversesortposition labels of the original D6A5 source cover. -/
def y322Orthogonal3D6A5InverseSortPosition : Fin 32 → Fin 32 :=
![
  0, 31, 20, 23, 17, 27, 22, 25, 18, 21, 15, 12, 26, 30, 29, 28, 24, 16, 13, 10, 19, 14, 11, 8,
  4, 9, 6, 7, 5, 2, 1, 3]

/-- The exact fundamental-weight vector reduced modulo three for D6A5. -/
def y322Orthogonal3D6A5Point : Fin 7 → ZMod 3 :=
  ![2, 0, 1, 2, 1, 0, 0]

/-- The exact finite inverse transports of the original D6A5 source representatives. -/
def y322Orthogonal3D6A5Orbit : Fin 32 → Fin 7 → ZMod 3 :=
![
  ![2, 0, 1, 2, 1, 0, 0],
  ![2, 0, 1, 2, 1, 0, 2],
  ![1, 0, 1, 2, 1, 0, 2],
  ![1, 2, 1, 2, 1, 0, 2],
  ![1, 0, 1, 2, 0, 0, 2],
  ![1, 2, 0, 2, 1, 0, 2],
  ![1, 2, 1, 2, 0, 0, 2],
  ![1, 2, 0, 1, 1, 0, 2],
  ![1, 2, 0, 2, 0, 0, 2],
  ![0, 2, 1, 2, 0, 0, 2],
  ![1, 2, 0, 1, 0, 0, 2],
  ![0, 2, 0, 2, 0, 0, 2],
  ![0, 2, 1, 2, 0, 0, 1],
  ![0, 2, 0, 1, 0, 0, 2],
  ![0, 1, 0, 2, 0, 0, 2],
  ![0, 2, 0, 2, 0, 0, 1],
  ![0, 1, 0, 1, 0, 0, 2],
  ![0, 2, 0, 1, 0, 0, 1],
  ![0, 1, 0, 2, 0, 0, 1],
  ![0, 1, 2, 1, 0, 0, 2],
  ![0, 1, 0, 1, 0, 0, 1],
  ![2, 1, 0, 2, 0, 0, 1],
  ![0, 1, 2, 1, 0, 0, 1],
  ![2, 1, 0, 1, 0, 0, 1],
  ![2, 1, 0, 2, 2, 0, 1],
  ![2, 1, 2, 1, 0, 0, 1],
  ![2, 1, 0, 1, 2, 0, 1],
  ![2, 0, 2, 1, 0, 0, 1],
  ![2, 1, 2, 1, 2, 0, 1],
  ![2, 0, 2, 1, 2, 0, 1],
  ![1, 0, 2, 1, 2, 0, 1],
  ![1, 0, 2, 1, 2, 0, 0]]

/-- The exact finite column encoding used to distinguish original D6A5 inverse transports. -/
def y322Orthogonal3D6A5Code (i : Fin 32) : ℕ :=
  ∑ j : Fin 7, (y322Orthogonal3D6A5Orbit i j).val * 3 ^ j.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
