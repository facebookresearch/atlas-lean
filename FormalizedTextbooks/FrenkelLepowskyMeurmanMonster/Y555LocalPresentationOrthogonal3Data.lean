/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit characteristic-three reflection data of the exact source C322 diagram.
The coefficients are derived from its Cartan form; no matrix-faithfulness claim is assumed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The first seven source vertices have their E7 Cartan form reduced modulo three. -/
def y322Orthogonal3Gram : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![2, 2, 0, 0, 2, 0, 2],
    ![2, 2, 2, 0, 0, 0, 0],
    ![0, 2, 2, 2, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 0],
    ![2, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 2, 2, 0],
    ![2, 0, 0, 0, 0, 0, 2]]

/-- The explicit inverse certifies that the reduced seven-dimensional form is nonsingular. -/
def y322Orthogonal3GramInverse : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![0, 0, 0, 0, 2, 1, 0],
    ![0, 0, 2, 1, 0, 0, 0],
    ![0, 2, 1, 2, 1, 2, 0],
    ![0, 1, 2, 0, 2, 1, 0],
    ![2, 0, 1, 2, 0, 0, 1],
    ![1, 0, 2, 1, 0, 2, 2],
    ![0, 0, 0, 0, 1, 2, 2]]

/-- First seven source roots are coordinate roots; the eighth is the Cartan quotient root. -/
def y322Orthogonal3Root (i : Fin 8) : Fin 7 → ZMod 3 :=
  if h : i.val < 7 then Pi.single ⟨i.val, h⟩ 1
  else ![0, 0, 0, 0, 2, 1, 1]

/-- The actual finite matrix reflection in each norm-two source root. -/
def y322Orthogonal3Reflection (i : Fin 8) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  1 - Matrix.vecMulVec (y322Orthogonal3Root i)
    (y322Orthogonal3Gram *ᵥ y322Orthogonal3Root i)

/-- The finite source Cartan form is symmetric. -/
theorem y322Orthogonal3Gram_symmetric : y322Orthogonal3Gram.transpose = y322Orthogonal3Gram := by
  decide +kernel

/-- The explicit inverse is a two-sided inverse of the actual finite source Gram matrix. -/
theorem y322Orthogonal3Gram_inverse :
    y322Orthogonal3Gram * y322Orthogonal3GramInverse = 1 ∧
      y322Orthogonal3GramInverse * y322Orthogonal3Gram = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel verifies eight small finite matrix squares, with no runtime assertion trusted.
/-- Every explicit source reflection is an actual involution. -/
theorem y322Orthogonal3Reflection_square (i : Fin 8) :
    y322Orthogonal3Reflection i * y322Orthogonal3Reflection i = 1 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- All finite matrix products use the exact original source adjacency, not a replacement diagram.
/-- Each pair satisfies its genuine defining Coxeter exponent in the source C322 diagram. -/
theorem y322Orthogonal3Reflection_coxeter (i j : Fin 8) (h : i ≠ j) :
    (y322Orthogonal3Reflection i * y322Orthogonal3Reflection j) ^
      (if y555Adjacent (y322Vertex i) (y322Vertex j) then 3 else 2 : ℕ) = 1 := by
  revert i j
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks every entry of eight small Gram-preservation matrix products.
/-- All source reflections preserve the actual nonsingular characteristic-three form. -/
theorem y322Orthogonal3Reflection_preserves (i : Fin 8) :
    (y322Orthogonal3Reflection i).transpose * y322Orthogonal3Gram *
      y322Orthogonal3Reflection i = y322Orthogonal3Gram := by
  revert i
  decide +kernel

/-- The literal original nine-letter source spider in these actual finite reflection matrices. -/
def y322Orthogonal3Spider : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  y322Orthogonal3Reflection 0 * y322Orthogonal3Reflection 1 * y322Orthogonal3Reflection 2 *
    y322Orthogonal3Reflection 0 * y322Orthogonal3Reflection 4 * y322Orthogonal3Reflection 5 *
      y322Orthogonal3Reflection 0 * y322Orthogonal3Reflection 6 * y322Orthogonal3Reflection 7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
