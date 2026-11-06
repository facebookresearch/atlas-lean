/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Integer basis and binary hyperbolic coordinates derived from the
Golay congruences in Seysen, arXiv:2002.10921v3, §6.1.

The integer matrix is the column Hermite normal form of the 37 vectors
8e₀, 4(eᵢ-e₀) (1≤i<24), twice the twelve published Golay generators, and
(-3,1,…,1). The supplied coordinates express those generators in this
matrix. No basis or source-comparison theorem is assumed by these data.
The finite matrix identities below are checked by Lean's kernel.
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Golay generators in column-major MOG coordinates, with coordinate 0 the least
significant bit. Source: Seysen, mmgroup, `docs/source/golay_basis_data.inc`,
commit 728688938a1c9fd27f3aee9b63464ea6b8d17965. -/
def golayGeneratorMasks : Fin 12 → ℕ := ![0xfff0f0, 0xff0ff0, 0xf0fff0, 0x0ffff0,
  0xcccc00, 0xaaaa00, 0x6ac0c0, 0xc6a0a0, 0xa6c00c, 0x6ca00a, 0x11111e, 0xffffff]
/-- The integer 0 or 1 at coordinate `i` of Golay generator `j`. -/
def golayGeneratorBit (j : Fin 12) (i : Fin 24) : ℤ :=
  if (golayGeneratorMasks j).testBit i.val then 1 else 0

/-- Integral basis matrix, with basis vectors as columns; the basis proof is in Definitions. -/
def leechBasisMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![8, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 2, 4, 2, 2, 2, 4, 0, 2, 0, 0, 2, 0, 5],
  ![0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 2, 2, 2, 1],
  ![0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 1],
  ![0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 2, 2, 2, 0, 0, 1],
  ![0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 2, 0, 2, 1],
  ![0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 2, 0, 0, 0, 2, 1],
  ![0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 1],
  ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 2, 2, 0, 0, 2, 2, 0, 2, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 2, 2, 2, 2, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integer coordinates of the 37 congruence generators in the explicit basis. -/
def leechGeneratorCoordinates : Matrix (Fin 24) (Fin 37) ℤ :=
  ![![1, -1, -1, -1, -1, -1, -1, 2, -1, -1, -1, 2, -1, 2, 2, 2, -1, 3, 2, 3, 3, 2, 3, -29, -1, -4,
    -5, 9, -6, -6, 10, -6, -8, 8, 0, -1, -1],
  ![0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, -1, -1, -1, 6, 0, 0, 0, -2, 2,
    1, -2, 1, 2, -1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1, -1, -1, 0, 5, 0, 0, 0, -2, 1,
    1, -2, 2, 2, -1, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0, 6, 0, 0, 1, -3, 1,
    1, -2, 1, 2, -1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0, -1, 6, 0, 1, 1, -2, 1,
    2, -2, 1, 2, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, 5, 0, 1, 1, -2, 1,
    1, -2, 0, 1, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, 6, 0, 1, 1, -2, 1,
    1, -3, 1, 1, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 1, -1, -1,
    1, 0, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, 5, 0, 1, 1, -2, 1,
    1, -1, 1, 1, -1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 5, 0, 1, 1, -2, 1,
    0, -2, 1, 1, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 5, 0, 1, 1, -2, 0,
    1, -2, 1, 1, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 1, 0, 0, 0,
    -1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, 0, 0, 0, 0, -1, -1, -1, 5, 0, 1, 0, -1, 1,
    1, -2, 1, 1, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, 0, 1, -1, 0,
    0, 0, -1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, 0, 1, 0, -1,
    1, -1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, 0, 1, 0, 0, 1,
    0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, -1, -1, -1, 5, 0, 0, 1, -1, 1,
    1, -2, 1, 1, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, -1, 1, -1, 0,
    1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, -1, 1, 0, -1,
    0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, -1, 1, 0, 0, 1,
    -1, -1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, -1, -1,
    0, -1, -1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 0, -1, 0, 1,
    -1, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, -1, 1,
    0, -1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 2, 0, 2, 2, 0,
    2, 2, 0, 0, 2, 1]]

/-- Integral Gram matrix for the standard normalization by 1/sqrt(8). -/
def leechBasisGram : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![8, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 2, 4, 2, 2, 2, 4, 0, 2, 0, 0, 2, 0, 5],
  ![4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 0, 1, 2, 1, 3],
  ![4, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 0, 1, 1, 1, 2, 0, 3],
  ![4, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 0, 3],
  ![4, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 0, 2, 1, 1, 1, 1, 3],
  ![4, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 0, 0, 1, 1, 3],
  ![4, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 0, 2, 1, 3],
  ![2, 2, 2, 2, 2, 2, 2, 4, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 3],
  ![4, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 0, 1, 1, 0, 3],
  ![4, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 0, 2, 0, 3],
  ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 0, 2, 1, 0, 1, 1, 3],
  ![2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3],
  ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 0, 1, 0, 1, 2, 1, 3],
  ![2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3],
  ![2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 2, 2, 2, 2, 3],
  ![2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 3],
  ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3],
  ![0, 1, 0, 1, 0, 1, 1, 2, 1, 1, 0, 2, 0, 2, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2],
  ![2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 3],
  ![0, 0, 1, 1, 1, 0, 1, 2, 0, 1, 1, 2, 0, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 2],
  ![0, 1, 1, 1, 1, 0, 0, 2, 1, 0, 0, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2],
  ![2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 3],
  ![0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2],
  ![5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 2, 3, 2, 6]]

/-- Golay coefficient masks witnessing the residues of the basis columns. -/
def leechBasisCodeMasks : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 2063, 0, 0, 0, 2049, 0, 2396, 2732, 3058, 0, 725, 2922, 443, 1024, 3990,
    1513, 0]

/-- Binary hyperbolic change-of-basis matrix for the integral Gram matrix. -/
def leechHyperbolicMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1],
  ![1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0],
  ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0],
  ![1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0],
  ![0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Explicit inverse of the binary change-of-basis matrix. -/
def leechHyperbolicInverse : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0],
  ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0],
  ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0],
  ![0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Published representatives of the dual Golay cocode basis, in the same MOG
coordinates as `golayGeneratorMasks`. Source: mmgroup `golay_basis_data.inc`,
commit 728688938a1c9fd27f3aee9b63464ea6b8d17965. -/
def golayCocodeGeneratorMasks : Fin 12 → ℕ :=
  ![0x000110, 0x001010, 0x010010, 0x100010, 0x000a00, 0x000c00,
    0x0000a0, 0x0000c0, 0x00000a, 0x00000c, 0x111111, 0x000001]

/-- Published values θ(bᵢ), as twelve-bit dual-basis masks. The first bit
is coordinate zero. Source: the cocycle column of `golay_basis_data.inc`. -/
def parkerBasisThetaMasks : Fin 12 → ℕ :=
  ![14, 13, 11, 7, 15, 15, 14, 14, 1025, 1025, 0, 0]

/-- Associator A(bᵢ,bⱼ), as a dual-basis mask. The defining triple-intersection
identity is checked below. Seysen §3.1, equation (3.1.1). -/
def parkerBasisAssociatorMasks : Matrix (Fin 12) (Fin 12) ℕ :=
  ![![0, 1024, 1024, 1024, 32, 16, 0, 0, 512, 256, 14, 0],
  ![1024, 0, 1024, 1024, 672, 336, 672, 336, 160, 80, 13, 0],
  ![1024, 1024, 0, 1024, 480, 912, 912, 624, 112, 224, 11, 0],
  ![1024, 1024, 1024, 0, 864, 720, 432, 864, 208, 176, 7, 0],
  ![32, 672, 480, 864, 0, 15, 524, 774, 140, 202, 0, 0],
  ![16, 336, 912, 720, 15, 0, 778, 268, 198, 76, 0, 0],
  ![0, 672, 912, 432, 524, 778, 0, 14, 44, 54, 0, 0],
  ![0, 336, 624, 864, 774, 268, 14, 0, 58, 28, 0, 0],
  ![512, 160, 112, 208, 140, 198, 44, 58, 0, 1025, 512, 0],
  ![256, 80, 224, 176, 202, 76, 54, 28, 1025, 0, 256, 0],
  ![14, 13, 11, 7, 0, 0, 0, 0, 512, 256, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Integer lattice coordinates of the source frame: first the modified code
generators x̃_b = x_b x_θ(b), then the cocode generators x_c.
Seysen §5.3, equation (5.3.4), and §6.1 specify these vectors. -/
def leechSourceFrameCoordinates : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![-5, -8, -9, 9, -10, -10, 6, -10, -13, 3, 0, -1, 0, 0, 0, -4, -3, -3, -3, -3, 0, 0, -5, -1],
  ![1, 1, 1, -2, 3, 2, -1, 2, 3, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, -1, 0, 1, 0],
  ![1, 1, 1, -2, 2, 2, -1, 3, 3, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, -1, 1, 0],
  ![1, 1, 2, -3, 2, 2, -1, 2, 3, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, -1, -1, 1, 0],
  ![-2, -1, -1, -5, -2, -1, -4, -1, 1, -3, 0, 0, -1, -1, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 1, 1, -2, 1, 1, -2, 0, 1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 1, 1, -2, 1, 1, -3, 1, 1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, -1, -1, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0],
  ![1, 1, 1, -3, 1, 1, 0, 2, 0, -2, 0, 0, -1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, -2, 1, 0, -2, 1, 1, -2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, -2, 0, 1, -2, 1, 1, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0],
  ![0, 2, 0, -2, 1, 1, -2, 1, 1, -2, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 2, -2, 1, 1, -2, 1, 1, -2, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, -1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, -1, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, -1, 1, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-2, -2, -2, 0, -3, -3, -2, -3, -3, -2, 1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -2, 0],
  ![0, 0, 0, 0, -1, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, -1, 1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![8, 8, 8, 6, 10, 10, 6, 8, 10, 8, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 6, 1]]

/-- Integral Gram matrix of that source frame, in the normalization by sqrt(8). -/
def leechSourceFrameGram : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![140, 138, 138, 138, 166, 166, 130, 130, 156, 156, 8, 38, 37, 38, 38, 38, 32, 32, 30, 30,
    32, 32, 104, 16],
  ![138, 140, 138, 138, 166, 166, 128, 128, 156, 156, 8, 38, 38, 37, 38, 38, 30, 30, 30, 30, 32,
    32, 104, 16],
  ![138, 138, 140, 138, 166, 166, 128, 128, 156, 156, 8, 38, 38, 38, 37, 38, 30, 30, 30, 30, 32,
    32, 104, 16],
  ![138, 138, 138, 140, 166, 166, 128, 128, 156, 156, 8, 38, 38, 38, 38, 37, 30, 30, 30, 30, 32,
    32, 104, 16],
  ![166, 166, 166, 166, 204, 202, 156, 156, 188, 188, 8, 44, 46, 46, 46, 46, 35, 34, 36, 36, 36,
    36, 124, 18],
  ![166, 166, 166, 166, 202, 204, 156, 156, 188, 188, 8, 44, 46, 46, 46, 46, 34, 35, 36, 36, 36,
    36, 124, 18],
  ![130, 128, 128, 128, 156, 156, 124, 122, 144, 144, 6, 34, 34, 36, 36, 36, 28, 28, 27, 26, 28,
    28, 96, 14],
  ![130, 128, 128, 128, 156, 156, 122, 124, 144, 144, 6, 34, 34, 36, 36, 36, 28, 28, 26, 27, 28,
    28, 96, 14],
  ![156, 156, 156, 156, 188, 188, 144, 144, 188, 186, 10, 44, 44, 42, 42, 42, 36, 36, 36, 36,
    35, 34, 124, 20],
  ![156, 156, 156, 156, 188, 188, 144, 144, 186, 188, 10, 44, 44, 42, 42, 42, 36, 36, 36, 36,
    34, 35, 124, 20],
  ![8, 8, 8, 8, 8, 8, 6, 6, 10, 10, 4, 4, 2, 2, 2, 2, 4, 4, 4, 4, 2, 2, 7, 2],
  ![38, 38, 38, 38, 44, 44, 34, 34, 44, 44, 4, 12, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 30, 5],
  ![37, 38, 38, 38, 46, 46, 34, 34, 44, 44, 2, 10, 12, 10, 10, 10, 8, 8, 8, 8, 8, 8, 28, 4],
  ![38, 37, 38, 38, 46, 46, 36, 36, 42, 42, 2, 10, 10, 12, 10, 10, 8, 8, 8, 8, 8, 8, 28, 4],
  ![38, 38, 37, 38, 46, 46, 36, 36, 42, 42, 2, 10, 10, 10, 12, 10, 8, 8, 8, 8, 8, 8, 28, 4],
  ![38, 38, 38, 37, 46, 46, 36, 36, 42, 42, 2, 10, 10, 10, 10, 12, 8, 8, 8, 8, 8, 8, 28, 4],
  ![32, 30, 30, 30, 35, 34, 28, 28, 36, 36, 4, 10, 8, 8, 8, 8, 12, 10, 8, 8, 8, 8, 24, 4],
  ![32, 30, 30, 30, 34, 35, 28, 28, 36, 36, 4, 10, 8, 8, 8, 8, 10, 12, 8, 8, 8, 8, 24, 4],
  ![30, 30, 30, 30, 36, 36, 27, 26, 36, 36, 4, 10, 8, 8, 8, 8, 8, 8, 12, 10, 8, 8, 24, 4],
  ![30, 30, 30, 30, 36, 36, 26, 27, 36, 36, 4, 10, 8, 8, 8, 8, 8, 8, 10, 12, 8, 8, 24, 4],
  ![32, 32, 32, 32, 36, 36, 28, 28, 35, 34, 2, 10, 8, 8, 8, 8, 8, 8, 8, 8, 12, 10, 24, 4],
  ![32, 32, 32, 32, 36, 36, 28, 28, 34, 35, 2, 10, 8, 8, 8, 8, 8, 8, 8, 8, 10, 12, 24, 4],
  ![104, 104, 104, 104, 124, 124, 96, 96, 124, 124, 7, 30, 28, 28, 28, 28, 24, 24, 24, 24, 24,
    24, 84, 14],
  ![16, 16, 16, 16, 18, 18, 14, 14, 20, 20, 2, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 14, 4]]

/-- Number of occupied MOG coordinates of a mask. -/
def golayMaskWeight (m : ℕ) : ℕ := ∑ i : Fin 24, if m.testBit i.val then 1 else 0

/-- The lattice representative λ_b of a code generator, with the complement
convention for codewords of weight 4 modulo 8. Seysen Theorem 6.1. -/
def leechSourceCodeVector (j : Fin 12) (i : Fin 24) : ℤ :=
  if golayMaskWeight (golayGeneratorMasks j) % 8 = 0 then 2 * golayGeneratorBit j i
  else 2 * (1 - golayGeneratorBit j i)

/-- The sum of λ_i over a published cocode representative. -/
def leechSourceCocodeVector (j : Fin 12) (i : Fin 24) : ℤ :=
  (golayMaskWeight (golayCocodeGeneratorMasks j) : ℤ) -
    4 * (if (golayCocodeGeneratorMasks j).testBit i.val then 1 else 0)

/-- The source's modified-code/cocode hyperbolic frame, in physical integer
lattice coordinates. This formula fixes its relationship to the Parker dictionary. -/
def leechSourceFrameVectors : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if h : j.val < 12 then leechSourceCodeVector ⟨j.val, h⟩ i +
    ∑ k : Fin 12, if (parkerBasisThetaMasks ⟨j.val, h⟩).testBit k.val then
      leechSourceCocodeVector k i else 0
  else leechSourceCocodeVector ⟨j.val - 12, by omega⟩ i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- A 24×24 matrix product unfolds many finite scalar operations.
/-- The supplied Gram matrix is exactly the scaled dot product of the columns. -/
theorem leechBasisMatrix_gram :
    leechBasisMatrix.transpose * leechBasisMatrix = (8 : ℤ) • leechBasisGram := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- A 24×24 matrix product unfolds many finite scalar operations.
/-- The two binary matrices are actual inverses, with both orders checked. -/
theorem leechHyperbolicMatrix_inverse :
    leechHyperbolicMatrix * leechHyperbolicInverse = 1 ∧
      leechHyperbolicInverse * leechHyperbolicMatrix = 1 := by
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The exact matrix identity checks all source-frame coordinates against their formulas.
theorem leechSourceFrameVectors_coordinates :
    leechBasisMatrix * leechSourceFrameCoordinates = leechSourceFrameVectors := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Binary reduction checks the 576 entries of the source change of basis.
theorem leechSourceFrameCoordinates_parity :
    ∀ i j, (leechSourceFrameCoordinates i j : ZMod 2) = leechHyperbolicMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Two integer matrix multiplications certify the Gram matrix of the source frame.
theorem leechSourceFrameGram_identity :
    leechSourceFrameCoordinates.transpose * leechBasisGram * leechSourceFrameCoordinates =
      leechSourceFrameGram := by
  decide +kernel

/-- Every source-frame vector has even half norm. -/
theorem leechSourceFrameGram_diagonal : ∀ i, 4 ∣ leechSourceFrameGram i i := by
  decide +kernel

/-- The twelve source pairs have the canonical hyperbolic polar pairing modulo two. -/
theorem leechSourceFrameGram_parity : ∀ i j,
    (leechSourceFrameGram i j : ZMod 2) = if i.val + 12 = j.val ∨ j.val + 12 = i.val
      then 1 else 0 := by
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The 1728 basis triples are checked against their 24-coordinate intersections.
theorem parkerBasisAssociatorMasks_identity : ∀ i j k,
    (parkerBasisAssociatorMasks i j).testBit k.val =
      decide (golayMaskWeight (golayGeneratorMasks i &&& golayGeneratorMasks j &&&
        golayGeneratorMasks k) % 2 = 1) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
