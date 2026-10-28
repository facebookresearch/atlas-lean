/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete characteristic-three Cartan-quotient data for the original C422 source diagram. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The exact nonsingular E8 Cartan block, reduced modulo three. -/
def y422Orthogonal3Gram : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![2, 2, 0, 0, 0, 2, 0, 2],
    ![2, 2, 2, 0, 0, 0, 0, 0],
    ![0, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 2, 2, 2, 0, 0, 0],
    ![0, 0, 0, 2, 2, 0, 0, 0],
    ![2, 0, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 2, 2, 0],
    ![2, 0, 0, 0, 0, 0, 0, 2]]

/-- An explicit two-sided inverse of the actual source Cartan block. -/
def y422Orthogonal3GramInverse : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![0, 0, 0, 0, 0, 2, 1, 0],
    ![0, 2, 0, 1, 2, 1, 2, 0],
    ![0, 0, 0, 2, 1, 0, 0, 0],
    ![0, 1, 2, 0, 0, 2, 1, 0],
    ![0, 2, 1, 0, 2, 1, 2, 0],
    ![2, 1, 0, 2, 1, 2, 1, 1],
    ![1, 2, 0, 1, 2, 1, 1, 2],
    ![0, 0, 0, 0, 0, 1, 2, 2]]

/-- Coordinate roots for the first eight source vertices and the exact ninth quotient root. -/
def y422Orthogonal3Root (i : Fin 9) : Fin 8 → ZMod 3 :=
  if h : i.val < 8 then Pi.single ⟨i.val, h⟩ 1
  else ![0, 0, 0, 0, 0, 2, 1, 1]

/-- The concrete norm-two reflection in each original source root. -/
def y422Orthogonal3Reflection (i : Fin 9) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  1 - Matrix.vecMulVec (y422Orthogonal3Root i)
    (y422Orthogonal3Gram *ᵥ y422Orthogonal3Root i)

/-- The actual source form is symmetric. -/
theorem y422Orthogonal3Gram_symmetric : y422Orthogonal3Gram.transpose = y422Orthogonal3Gram := by
  decide +kernel

/-- The supplied inverse certifies actual nonsingularity. -/
theorem y422Orthogonal3Gram_inverse :
    y422Orthogonal3Gram * y422Orthogonal3GramInverse = 1 ∧
      y422Orthogonal3GramInverse * y422Orthogonal3Gram = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Every concrete source reflection is an actual involution. -/
theorem y422Orthogonal3Reflection_square (i : Fin 9) :
    y422Orthogonal3Reflection i * y422Orthogonal3Reflection i = 1 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Concrete reflection pairs satisfy the exact original source Coxeter exponents. -/
theorem y422Orthogonal3Reflection_coxeter (i j : Fin 9) (h : i ≠ j) :
    (y422Orthogonal3Reflection i * y422Orthogonal3Reflection j) ^
      (if y444Adjacent (y422Vertex i) (y422Vertex j) then 3 else 2 : ℕ) = 1 := by
  revert i j
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Every concrete source reflection preserves the actual nonsingular form. -/
theorem y422Orthogonal3Reflection_preserves (i : Fin 9) :
    (y422Orthogonal3Reflection i).transpose * y422Orthogonal3Gram *
      y422Orthogonal3Reflection i = y422Orthogonal3Gram := by
  revert i
  decide +kernel

/-- The literal original source spider in the concrete reflection matrices. -/
def y422Orthogonal3Spider : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 1 * y422Orthogonal3Reflection 2 *
    y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 5 * y422Orthogonal3Reflection 6 *
      y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 7 * y422Orthogonal3Reflection 8

/-- The exact corrected first longest source word in the concrete reflection matrices. -/
def y422Orthogonal3Longest : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  (y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 1 *
    y422Orthogonal3Reflection 5 * y422Orthogonal3Reflection 7 *
    y422Orthogonal3Reflection 2 * y422Orthogonal3Reflection 6 * y422Orthogonal3Reflection 3) ^ 9

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
