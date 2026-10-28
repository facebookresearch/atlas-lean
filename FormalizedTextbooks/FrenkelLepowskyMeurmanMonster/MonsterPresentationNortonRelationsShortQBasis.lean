/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Twenty-four actual preferred short-Q lifts whose binary images form a basis. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Source-code labels for a concrete preferred-short binary basis. -/
def monsterNortonShortBasisCode : Fin 24 → Fin 2048 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 1024]

/-- Physical coordinates for the same genuine short labels. -/
def monsterNortonShortBasisCoordinate : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The 24 preferred short labels, all in the actual odd-coordinate short family. -/
def monsterNortonShortBasisIndex (j : Fin 24) : GriessShortIndex :=
  Sum.inr (Sum.inr (monsterNortonShortBasisCode j, monsterNortonShortBasisCoordinate j))

/-- Compact row masks of their actual binary coordinate columns. -/
def monsterNortonShortBasisRows : Fin 24 → ℕ :=
  ![0x1000, 0x2000, 0x4000, 0x8000, 0x10000,
    0x20000, 0x40000, 0x80000, 0x100000, 0x200000,
    0xc00000, 0x800000, 0x33ec70, 0xfdbf0, 0xfb7f0,
    0xf7ff0, 0x200, 0x100, 0x40, 0x20,
    0xc, 0x80000a, 0xb00c9e, 0xffffff]

/-- Compact row masks of an inverse of that actual coordinate matrix. -/
def monsterNortonShortBasisInverseRows : Fin 24 → ℕ :=
  ![0xcf0cff, 0x5f8bf7, 0x6f83f7, 0x7f83f7, 0xc7338,
    0x80000, 0x40000, 0x393c9, 0x20000, 0x10000,
    0xa00a, 0xc00c, 0x1, 0x2, 0x4,
    0x8, 0x10, 0x20, 0x40, 0x80,
    0x100, 0x200, 0xc00, 0x800]

/-- The finite binary coordinate matrix. -/
def monsterNortonShortBasisMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((monsterNortonShortBasisRows i).testBit j.val)

/-- Its finite inverse matrix. -/
def monsterNortonShortBasisInverse : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((monsterNortonShortBasisInverseRows i).testBit j.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- All 576 bits are computed using the actual preferred short vectors and the certified8B inverse.
/-- The columns are the actual intrinsic Q classes of the stated short labels. -/
theorem monsterNortonShortBasis_binary_certificate (j : Fin 24) : ∀ i : Fin 24,
    toAdd (monsterNortonShortQ (monsterNortonShortBasisIndex j)).base i =
      monsterNortonShortBasisMatrix i j := by
  fin_cases j <;> decide +kernel

set_option maxHeartbeats 16000000 in
-- Check all 576 entries of the product over the two-element field.
/-- The displayed actual binary matrix has a checked right inverse. -/
theorem monsterNortonShortBasis_inverse_certificate :
    monsterNortonShortBasisMatrix * monsterNortonShortBasisInverse = 1 := by
  decide +kernel

/-- The preferred short lifts have the precise binary columns used by the inverse. -/
theorem monsterNortonShortBasis_binary (j : Fin 24) :
    toAdd (qQuotHom (monsterNortonShortQ (monsterNortonShortBasisIndex j))) =
      monsterNortonShortBasisMatrix.col j := by
  funext i
  exact monsterNortonShortBasis_binary_certificate j i

/-- A subgroup containing the 24 genuine preferred short lifts has full binary image. -/
theorem monsterNortonShortBasis_binaryImage_eq_top (K : Subgroup Q)
    (h : ∀ j : Fin 24, monsterNortonShortQ (monsterNortonShortBasisIndex j) ∈ K) :
    qSubgroupBinaryImage K = ⊤ := by
  apply top_unique
  intro v _
  let b := monsterNortonShortBasisInverse *ᵥ v
  have hv : monsterNortonShortBasisMatrix *ᵥ b = v := by
    change monsterNortonShortBasisMatrix *ᵥ (monsterNortonShortBasisInverse *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, monsterNortonShortBasis_inverse_certificate, Matrix.one_mulVec]
  have he : monsterNortonShortBasisMatrix *ᵥ b =
      ∑ j : Fin 24, b j • monsterNortonShortBasisMatrix.col j := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [← hv, he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact ⟨monsterNortonShortQ (monsterNortonShortBasisIndex j), h j,
    monsterNortonShortBasis_binary j⟩

/-- These 24 short lifts and the actual central involution generate all of Q with phases. -/
theorem monsterNortonShortBasis_subgroup_eq_top (K : Subgroup Q)
    (h : ∀ j : Fin 24, monsterNortonShortQ (monsterNortonShortBasisIndex j) ∈ K)
    (hz : qCentralInvolution ∈ K) : K = ⊤ :=
  qSubgroup_eq_top_of_binaryImage_eq_top K (centerQ_le_of_central_mem K hz)
    (monsterNortonShortBasis_binaryImage_eq_top K h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
