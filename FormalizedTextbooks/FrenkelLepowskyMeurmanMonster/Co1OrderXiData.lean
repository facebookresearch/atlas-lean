/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The nonmonomial Leech isometry in Seysen §9.5.
The source matrix R=A*B acts on row vectors. This module constructs the
physical column action Rᵀ=B*A, and its inverse, without assigning either
orientation to an mmgroup generator label. Each of the six MOG columns is
contiguous in the repository's column-major coordinate order.
The integral basis matrix below is merely a certificate: its relation to
the source matrix and actual lattice basis is checked by the kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Twice the physical column matrix B*A of the three-bases transformation. -/
def co1XiNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i.val / 4 = j.val / 4 then
    (if i.val % 4 = 0 then -1 else 1) * (if i.val % 4 = j.val % 4 then 1 else -1)
  else 0

/-- Exact rational source transformation, in physical column convention. -/
def co1XiMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  co1XiNumerator.map (fun z => (z : ℚ) / 2)

/-- The integer matrix of that transformation in the proved integral Leech basis. -/
def co1XiBasisMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![1, 1, 1, 1, 0, -1, -1, 0, 0, -1, -1, 0, -3, -4, -4, -5, -4, -5, -5, -5, 1, 3, 2, 2],
  ![-1, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 0, -1],
  ![-1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 0, -1],
  ![-1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 0, -1, 0, -1],
  ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, -1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1]]

set_option maxHeartbeats 12000000 in
-- Check the 576 entries of the integral change-of-basis identity.
theorem co1Xi_basis_certificate :
    co1XiMatrixQ * leechBasisMatrix.map (Int.castRingHom ℚ) =
      leechBasisMatrix.map (Int.castRingHom ℚ) * co1XiBasisMatrix.map (Int.castRingHom ℚ) := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Check orthogonality of the explicit rational source matrix.
theorem co1Xi_orthogonal_certificate : co1XiMatrixQ.transpose * co1XiMatrixQ = 1 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Two matrix products certify the source transformation's cube.
theorem co1Xi_cube_certificate : co1XiMatrixQ * co1XiMatrixQ * co1XiMatrixQ = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
