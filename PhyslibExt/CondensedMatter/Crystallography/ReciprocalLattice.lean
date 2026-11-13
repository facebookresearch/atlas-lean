/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Reciprocal lattices and Brillouin zones

The reciprocal basis of three direct lattice vectors, G_hkl vectors, FCC/BCC duality,
the first Brillouin zone, and discrete Fourier coefficients of lattice-periodic functions.

## i. Overview

Three direct primitive vectors `a₁ a₂ a₃ : Fin 3 → ℝ` with nonzero signed cell volume
`V = a₁ ⬝ᵥ (a₂ ⨯₃ a₃)` determine the reciprocal basis `b₁ b₂ b₃` by
`b₁ = (2π/V) • (a₂ ⨯₃ a₃)` and cyclic permutations. Convention (frozen in this file):
the physics `2π` convention throughout, `a_i ⬝ᵥ b_j = 2π δ_ij`, reciprocal vectors in
units of 1/length. The crystallography no-`2π` convention is explicitly NOT used.

The reciprocal basis satisfies duality (`recip_duality`), has cell volume
`V* = (2π)³/V` (`recip_volume`), and applying the construction twice returns the direct
vectors (`recip_of_recip`). Reciprocal-lattice vectors `G = h • b₁ + k • b₂ + l • b₃`
pair with direct-lattice vectors `R` by `G ⬝ᵥ R = 2π(hn₁ + kn₂ + ln₃) ∈ 2πℤ`
(`recipVec_dot_lattice`), so `G` is perpendicular to the `(hkl)` plane
`G ⬝ᵥ x = 2π` (`plane_perp`) with interplanar spacing `d = 2π/‖G‖` (`spacing_mul_norm`,
with the Euclidean norm `euclidNorm x = √(x ⬝ᵥ x)`). The reciprocal of FCC(`a`) is
BCC(`4π/a`) and conversely (`fcc_bcc`, `bcc_fcc`), both by explicit computation.

The first Brillouin zone is defined as the Wigner-Seitz cell of the reciprocal lattice
(`firstBrillouinZone`). Its volume is proved ONLY in the fundamental-parallelepiped form
(`firstBZ_volume`, the same identity as `recip_volume`); the step from the parallelepiped
cell to the Wigner-Seitz cell volume (both are fundamental domains) is interpretation,
flagged in the docstring, not a proved volume theorem.

Fourier analysis is a DEFINITION (discrete coefficients `fourierCoeffDiscrete` on an
`N × N × N` grid plus finite plane-wave orthogonality `fourierCoeffDiscrete_planeWave`,
with aliasing in the explicit phase-vanishing sense) with L²/pointwise/uniform convergence
EXPLICITLY DEFERRED: stronger convergence needs stronger hypotheses and is a non-goal here.

Reuse-verified against Mathlib/Physlib/ATLAS main; no ATLAS-50 prerequisite PR dependency.
This file imports only Mathlib. It does not import PhyslibAlpha or any other ATLAS-50
module. The reciprocal-basis identities are proved directly from Mathlib cross/dot
products. A grep for `reciprocal`, `brillouin`, `wigner-seitz` over ATLAS main found no
canonical reciprocal-lattice or Brillouin-zone API, so this module defines its own.

## ii. Key results

- `Crystallography.cellVolume` : the signed cell volume `a₁ ⬝ᵥ (a₂ ⨯₃ a₃)`.
- `Crystallography.b₁`, `Crystallography.b₂`, `Crystallography.b₃` : the reciprocal basis.
- `Crystallography.recip_duality` : `a_i ⬝ᵥ b_j = 2π δ_ij`.
- `Crystallography.recip_volume` : `V* = (2π)³/V`.
- `Crystallography.recip_of_recip` : the reciprocal of the reciprocal is the direct basis.
- `Crystallography.recipVec`, `Crystallography.latticeVec` : `G_hkl` and lattice vectors.
- `Crystallography.recipVec_dot_lattice` : `G ⬝ᵥ R = 2π(hn₁ + kn₂ + ln₃)`.
- `Crystallography.recipVec_dot_lattice_int` : `G ⬝ᵥ R ∈ 2πℤ`.
- `Crystallography.euclidNorm` : the Euclidean norm `√(x ⬝ᵥ x)`.
- `Crystallography.interplanarSpacing` : `d = 2π/‖G‖`.
- `Crystallography.plane_perp` : `G` is perpendicular to the `(hkl)` plane.
- `Crystallography.spacing_mul_norm` : `d * ‖G‖ = 2π`.
- `Crystallography.fcc_bcc`, `Crystallography.bcc_fcc` : FCC/BCC duality, both directions.
- `Crystallography.firstBrillouinZone` : the Wigner-Seitz cell of the reciprocal lattice.
- `Crystallography.firstBZ_volume` : the reciprocal-cell volume identity (parallelepiped
  form; see the Wigner-Seitz flag in its docstring).
- `Crystallography.fourierCoeffDiscrete` : discrete Fourier coefficients on an `N³` grid.
- `Crystallography.fourierCoeffDiscrete_planeWave` : finite plane-wave orthogonality.

## iii. Table of contents

- A. Cell volume and the reciprocal basis
- B. Reciprocal volume and the double dual
- C. Reciprocal-lattice vectors, G_hkl, and spacing
- D. FCC/BCC duality
- E. The first Brillouin zone
- F. Discrete Fourier coefficients

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapters 4 and 5, for the reciprocal lattice, Brillouin zones, and Fourier expansions of
  lattice-periodic functions.
* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2004), Chapter 2.

-/

@[expose] public section

open scoped Matrix

namespace Crystallography

/-! ## A. Cell volume and the reciprocal basis -/

/-- The signed cell volume `V = a₁ ⬝ᵥ (a₂ ⨯₃ a₃)`, the scalar triple product. -/
def cellVolume (a₁ a₂ a₃ : Fin 3 → ℝ) : ℝ :=
  a₁ ⬝ᵥ (a₂ ⨯₃ a₃)

/-- First reciprocal vector: `b₁ = (2π/V) • (a₂ ⨯₃ a₃)`. Physics `2π` convention. -/
noncomputable def b₁ (a₁ a₂ a₃ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (2 * Real.pi / cellVolume a₁ a₂ a₃) • (a₂ ⨯₃ a₃)

/-- Second reciprocal vector: `b₂ = (2π/V) • (a₃ ⨯₃ a₁)`. Physics `2π` convention. -/
noncomputable def b₂ (a₁ a₂ a₃ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (2 * Real.pi / cellVolume a₁ a₂ a₃) • (a₃ ⨯₃ a₁)

/-- Third reciprocal vector: `b₃ = (2π/V) • (a₁ ⨯₃ a₂)`. Physics `2π` convention. -/
noncomputable def b₃ (a₁ a₂ a₃ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (2 * Real.pi / cellVolume a₁ a₂ a₃) • (a₁ ⨯₃ a₂)

/-- Unfolding equation for `cellVolume`, kept private so rewrites stay targeted. -/
private lemma cellVolume_eq (x y z : Fin 3 → ℝ) :
    cellVolume x y z = x ⬝ᵥ (y ⨯₃ z) :=
  rfl

/-- Unfolding equation for `b₁`. -/
private lemma b₁_eq (x y z : Fin 3 → ℝ) :
    b₁ x y z = (2 * Real.pi / cellVolume x y z) • (y ⨯₃ z) :=
  rfl

/-- Unfolding equation for `b₂`. -/
private lemma b₂_eq (x y z : Fin 3 → ℝ) :
    b₂ x y z = (2 * Real.pi / cellVolume x y z) • (z ⨯₃ x) :=
  rfl

/-- Unfolding equation for `b₃`. -/
private lemma b₃_eq (x y z : Fin 3 → ℝ) :
    b₃ x y z = (2 * Real.pi / cellVolume x y z) • (x ⨯₃ y) :=
  rfl

/-- Duality, case `(1, 1)`. -/
private lemma h11 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₁ ⬝ᵥ b₁ a₁ a₂ a₃ = 2 * Real.pi := by
  simp only [b₁, dotProduct_smul, smul_eq_mul,
    show a₁ ⬝ᵥ (a₂ ⨯₃ a₃) = cellVolume a₁ a₂ a₃ from rfl]
  exact div_mul_cancel₀ _ hV

/-- Duality, case `(1, 2)`: off-diagonal, vanishes by `dot_cross_self`. -/
private lemma h12 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₁ ⬝ᵥ b₂ a₁ a₂ a₃ = 0 := by
  simp only [b₂, dotProduct_smul, smul_eq_mul, dot_self_cross, dot_cross_self, mul_zero]

/-- Duality, case `(1, 3)`: off-diagonal, vanishes by `dot_self_cross`. -/
private lemma h13 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₁ ⬝ᵥ b₃ a₁ a₂ a₃ = 0 := by
  simp only [b₃, dotProduct_smul, smul_eq_mul, dot_self_cross, dot_cross_self, mul_zero]

/-- Duality, case `(2, 1)`: off-diagonal, vanishes by `dot_self_cross`. -/
private lemma h21 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₂ ⬝ᵥ b₁ a₁ a₂ a₃ = 0 := by
  simp only [b₁, dotProduct_smul, smul_eq_mul, dot_self_cross, dot_cross_self, mul_zero]

/-- Duality, case `(2, 2)`: diagonal, via cyclic permutation of the triple product. -/
private lemma h22 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₂ ⬝ᵥ b₂ a₁ a₂ a₃ = 2 * Real.pi := by
  have hperm : a₂ ⬝ᵥ (a₃ ⨯₃ a₁) = cellVolume a₁ a₂ a₃ :=
    (triple_product_permutation a₁ a₂ a₃).symm
  simp only [b₂, dotProduct_smul, smul_eq_mul, hperm]
  exact div_mul_cancel₀ _ hV

/-- Duality, case `(2, 3)`: off-diagonal, vanishes by `dot_cross_self`. -/
private lemma h23 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₂ ⬝ᵥ b₃ a₁ a₂ a₃ = 0 := by
  simp only [b₃, dotProduct_smul, smul_eq_mul, dot_self_cross, dot_cross_self, mul_zero]

/-- Duality, case `(3, 1)`: off-diagonal, vanishes by `dot_cross_self`. -/
private lemma h31 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₃ ⬝ᵥ b₁ a₁ a₂ a₃ = 0 := by
  simp only [b₁, dotProduct_smul, smul_eq_mul, dot_self_cross, dot_cross_self, mul_zero]

/-- Duality, case `(3, 2)`: off-diagonal, vanishes by `dot_self_cross`. -/
private lemma h32 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₃ ⬝ᵥ b₂ a₁ a₂ a₃ = 0 := by
  simp only [b₂, dotProduct_smul, smul_eq_mul, dot_self_cross, dot_cross_self, mul_zero]

/-- Duality, case `(3, 3)`: diagonal, via two cyclic permutations. -/
private lemma h33 (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    a₃ ⬝ᵥ b₃ a₁ a₂ a₃ = 2 * Real.pi := by
  have hperm : a₃ ⬝ᵥ (a₁ ⨯₃ a₂) = cellVolume a₁ a₂ a₃ := by
    rw [← triple_product_permutation a₂ a₃ a₁]
    exact (triple_product_permutation a₁ a₂ a₃).symm
  simp only [b₃, dotProduct_smul, smul_eq_mul, hperm]
  exact div_mul_cancel₀ _ hV

/-- Reciprocal-basis duality: `a_i ⬝ᵥ b_j = 2π δ_ij`, in indexed form. -/
lemma recip_duality (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0)
    (i j : Fin 3) :
    ![a₁, a₂, a₃] i ⬝ᵥ ![b₁ a₁ a₂ a₃, b₂ a₁ a₂ a₃, b₃ a₁ a₂ a₃] j
      = 2 * Real.pi * (if i = j then (1 : ℝ) else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val] <;>
    simp [h11 _ _ _ hV, h12 _ _ _ hV, h13 _ _ _ hV, h21 _ _ _ hV, h22 _ _ _ hV,
      h23 _ _ _ hV, h31 _ _ _ hV, h32 _ _ _ hV, h33 _ _ _ hV]

/-! ## B. Reciprocal volume and the double dual -/

/-- Double cross product identity for the first reciprocal-of-reciprocal vector. -/
private lemma crossSq1 (a₁ a₂ a₃ : Fin 3 → ℝ) :
    (a₃ ⨯₃ a₁) ⨯₃ (a₁ ⨯₃ a₂) = (cellVolume a₁ a₂ a₃) • a₁ := by
  rw [cross_cross_eq_smul_sub_smul, dot_self_cross, zero_smul, sub_zero]
  congr 1
  rw [← triple_product_permutation a₂ a₃ a₁]
  exact (triple_product_permutation a₁ a₂ a₃).symm

/-- Double cross product identity for the second reciprocal-of-reciprocal vector. -/
private lemma crossSq2 (a₁ a₂ a₃ : Fin 3 → ℝ) :
    (a₁ ⨯₃ a₂) ⨯₃ (a₂ ⨯₃ a₃) = (cellVolume a₁ a₂ a₃) • a₂ := by
  rw [cross_cross_eq_smul_sub_smul, dot_self_cross, zero_smul, sub_zero,
    show a₁ ⬝ᵥ (a₂ ⨯₃ a₃) = cellVolume a₁ a₂ a₃ from rfl]

/-- Double cross product identity for the third reciprocal-of-reciprocal vector. -/
private lemma crossSq3 (a₁ a₂ a₃ : Fin 3 → ℝ) :
    (a₂ ⨯₃ a₃) ⨯₃ (a₃ ⨯₃ a₁) = (cellVolume a₁ a₂ a₃) • a₃ := by
  rw [cross_cross_eq_smul_sub_smul, dot_self_cross, zero_smul, sub_zero]
  congr 1
  exact (triple_product_permutation a₁ a₂ a₃).symm

/-- Scalar factors pull out of both cross-product arguments. -/
private lemma cross_smul_smul (c : ℝ) (Y Z : Fin 3 → ℝ) :
    (c • Y) ⨯₃ (c • Z) = (c * c) • (Y ⨯₃ Z) := by
  simp only [map_smul, LinearMap.smul_apply, smul_smul]

/-- The reciprocal cell volume: `V* = (2π)³/V`. -/
lemma recip_volume (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    cellVolume (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃)
      = (2 * Real.pi)^3 / cellVolume a₁ a₂ a₃ := by
  have hXYZ : (a₂ ⨯₃ a₃) ⬝ᵥ ((a₃ ⨯₃ a₁) ⨯₃ (a₁ ⨯₃ a₂))
      = (cellVolume a₁ a₂ a₃)^2 := by
    rw [crossSq1 a₁ a₂ a₃, dotProduct_smul, smul_eq_mul]
    have hcomm : (a₂ ⨯₃ a₃) ⬝ᵥ a₁ = cellVolume a₁ a₂ a₃ := by
      rw [dotProduct_comm]
      rfl
    rw [hcomm]
    ring
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  rw [cellVolume_eq]
  simp only [b₁, b₂, b₃, cross_smul_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hXYZ]
  field_simp

/-- The reciprocal of the reciprocal basis is the direct basis. -/
lemma recip_of_recip (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    b₁ (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) = a₁ ∧
    b₂ (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) = a₂ ∧
    b₃ (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) = a₃ := by
  have hpi2 : (2 : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  have hpi3 : ((2 : ℝ) * Real.pi)^3 ≠ 0 := pow_ne_zero 3 hpi2
  have hVstar : cellVolume (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) ≠ 0 := by
    rw [recip_volume a₁ a₂ a₃ hV]
    exact div_ne_zero hpi3 hV
  have hVstar' : (2 * Real.pi)^3 / cellVolume a₁ a₂ a₃ ≠ 0 := by
    rw [← recip_volume a₁ a₂ a₃ hV]
    exact hVstar
  have hS : ((2 * Real.pi / cellVolume (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃))
        * ((2 * Real.pi / cellVolume a₁ a₂ a₃) * (2 * Real.pi / cellVolume a₁ a₂ a₃)))
        * cellVolume a₁ a₂ a₃ = 1 := by
    rw [recip_volume a₁ a₂ a₃ hV]
    field_simp
  have hinner1 : (b₂ a₁ a₂ a₃) ⨯₃ (b₃ a₁ a₂ a₃)
      = ((2 * Real.pi / cellVolume a₁ a₂ a₃) * (2 * Real.pi / cellVolume a₁ a₂ a₃))
        • ((a₃ ⨯₃ a₁) ⨯₃ (a₁ ⨯₃ a₂)) := by
    simp only [b₂, b₃, cross_smul_smul]
  have hinner2 : (b₃ a₁ a₂ a₃) ⨯₃ (b₁ a₁ a₂ a₃)
      = ((2 * Real.pi / cellVolume a₁ a₂ a₃) * (2 * Real.pi / cellVolume a₁ a₂ a₃))
        • ((a₁ ⨯₃ a₂) ⨯₃ (a₂ ⨯₃ a₃)) := by
    simp only [b₃, b₁, cross_smul_smul]
  have hinner3 : (b₁ a₁ a₂ a₃) ⨯₃ (b₂ a₁ a₂ a₃)
      = ((2 * Real.pi / cellVolume a₁ a₂ a₃) * (2 * Real.pi / cellVolume a₁ a₂ a₃))
        • ((a₂ ⨯₃ a₃) ⨯₃ (a₃ ⨯₃ a₁)) := by
    simp only [b₁, b₂, cross_smul_smul]
  have c1 : b₁ (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) = a₁ := by
    rw [b₁_eq, hinner1, crossSq1 a₁ a₂ a₃, smul_smul, smul_smul, hS, one_smul]
  have c2 : b₂ (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) = a₂ := by
    rw [b₂_eq, hinner2, crossSq2 a₁ a₂ a₃, smul_smul, smul_smul, hS, one_smul]
  have c3 : b₃ (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃) = a₃ := by
    rw [b₃_eq, hinner3, crossSq3 a₁ a₂ a₃, smul_smul, smul_smul, hS, one_smul]
  exact ⟨c1, c2, c3⟩

/-! ## C. Reciprocal-lattice vectors, G_hkl, and spacing -/

/-- Reciprocal-lattice vector `G = h • b₁ + k • b₂ + l • b₃` for integers `h k l`. -/
noncomputable def recipVec (a₁ a₂ a₃ : Fin 3 → ℝ) (h k l : ℤ) : Fin 3 → ℝ :=
  ((h : ℤ) : ℝ) • b₁ a₁ a₂ a₃ + ((k : ℤ) : ℝ) • b₂ a₁ a₂ a₃
    + ((l : ℤ) : ℝ) • b₃ a₁ a₂ a₃

/-- Direct-lattice vector `R = n₁ • a₁ + n₂ • a₂ + n₃ • a₃` for integers `n₁ n₂ n₃`. -/
def latticeVec (a₁ a₂ a₃ : Fin 3 → ℝ) (n₁ n₂ n₃ : ℤ) : Fin 3 → ℝ :=
  ((n₁ : ℤ) : ℝ) • a₁ + ((n₂ : ℤ) : ℝ) • a₂ + ((n₃ : ℤ) : ℝ) • a₃

/-- The `G ⬝ᵥ R` pairing for real coefficients, from the nine duality identities. -/
private lemma dot_lattice_general (a₁ a₂ a₃ : Fin 3 → ℝ)
    (hV : cellVolume a₁ a₂ a₃ ≠ 0) (h k l c₁ c₂ c₃ : ℝ) :
    ((h • b₁ a₁ a₂ a₃ + k • b₂ a₁ a₂ a₃ + l • b₃ a₁ a₂ a₃) ⬝ᵥ
      (c₁ • a₁ + c₂ • a₂ + c₃ • a₃))
      = 2 * Real.pi * (h * c₁ + k * c₂ + l * c₃) := by
  rw [dotProduct_comm]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, h11 _ _ _ hV, h12 _ _ _ hV, h13 _ _ _ hV, h21 _ _ _ hV,
    h22 _ _ _ hV, h23 _ _ _ hV, h31 _ _ _ hV, h32 _ _ _ hV, h33 _ _ _ hV]
  ring

/-- `G ⬝ᵥ R = 2π(hn₁ + kn₂ + ln₃)` for a reciprocal-lattice vector `G` and lattice
vector `R`. -/
lemma recipVec_dot_lattice (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0)
    (h k l n₁ n₂ n₃ : ℤ) :
    recipVec a₁ a₂ a₃ h k l ⬝ᵥ latticeVec a₁ a₂ a₃ n₁ n₂ n₃
      = 2 * Real.pi * (((h * n₁ + k * n₂ + l * n₃ : ℤ)) : ℝ) := by
  simp only [recipVec, latticeVec, dot_lattice_general a₁ a₂ a₃ hV, Int.cast_add,
    Int.cast_mul]

/-- Hence `G ⬝ᵥ R ∈ 2πℤ` for every reciprocal-lattice vector `G` and lattice vector `R`. -/
lemma recipVec_dot_lattice_int (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0)
    (h k l n₁ n₂ n₃ : ℤ) :
    ∃ m : ℤ, recipVec a₁ a₂ a₃ h k l ⬝ᵥ latticeVec a₁ a₂ a₃ n₁ n₂ n₃
      = 2 * Real.pi * ((m : ℤ) : ℝ) :=
  ⟨h * n₁ + k * n₂ + l * n₃, recipVec_dot_lattice a₁ a₂ a₃ hV h k l n₁ n₂ n₃⟩

/-- The Euclidean norm `‖x‖ = √(x ⬝ᵥ x)`, used for spacing and Brillouin-zone radii.
This is the Euclidean norm on `Fin 3 → ℝ` (not the sup-norm `‖·‖` instance). -/
noncomputable def euclidNorm (x : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (x ⬝ᵥ x)

/-- A vector has nonnegative self dot product. -/
private lemma dotProduct_self_nonneg (x : Fin 3 → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- A nonzero vector has positive self dot product. -/
private lemma dotProduct_self_pos_of_ne_zero (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ x := by
  by_contra h
  push_neg at h
  have hle := dotProduct_self_nonneg x
  have heq : x ⬝ᵥ x = 0 := le_antisymm h hle
  exact hx (dotProduct_self_eq_zero.mp heq)

/-- The Euclidean norm of a nonzero vector is positive. -/
private lemma euclidNorm_pos_of_ne_zero (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < euclidNorm x :=
  Real.sqrt_pos.mpr (dotProduct_self_pos_of_ne_zero x hx)

/-- Interplanar spacing `d = 2π/‖G‖` for a nonzero reciprocal-lattice vector `G`. -/
noncomputable def interplanarSpacing (G : Fin 3 → ℝ) : ℝ :=
  2 * Real.pi / euclidNorm G

/-- `G` is perpendicular to the `(hkl)` plane: the `(hkl)` plane is the affine plane
`G ⬝ᵥ x = 2π` (for the primitive-family normalisation used here), so any two of its
points differ by a vector orthogonal to `G`. -/
lemma plane_perp (G x y : Fin 3 → ℝ) (hG : G ≠ 0) (hx : G ⬝ᵥ x = 2 * Real.pi)
    (hy : G ⬝ᵥ y = 2 * Real.pi) :
    G ⬝ᵥ (x - y) = 0 := by
  rw [dotProduct_sub, hx, hy, sub_self]

/-- The spacing and the norm multiply to `2π`: `d * ‖G‖ = 2π` for `G ≠ 0`. -/
lemma spacing_mul_norm (G : Fin 3 → ℝ) (hG : G ≠ 0) :
    interplanarSpacing G * euclidNorm G = 2 * Real.pi := by
  have hpos : 0 < euclidNorm G := euclidNorm_pos_of_ne_zero G hG
  simp only [interplanarSpacing]
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)]

/-! ## D. FCC/BCC duality -/

/-- The reciprocal of FCC(`a`) is BCC(`4π/a`): with FCC primitive vectors
`(a/2) • ![0,1,1]`, `(a/2) • ![1,0,1]`, `(a/2) • ![1,1,0]`, the reciprocal basis is
`(2π/a) • ![-1,1,1]`, `(2π/a) • ![1,-1,1]`, `(2π/a) • ![1,1,-1]`, by explicit
computation. -/
lemma fcc_bcc (a : ℝ) (ha : 0 < a) :
    b₁ ((a / 2) • ![0, 1, 1]) ((a / 2) • ![1, 0, 1]) ((a / 2) • ![1, 1, 0])
        = (2 * Real.pi / a) • ![-1, 1, 1] ∧
      b₂ ((a / 2) • ![0, 1, 1]) ((a / 2) • ![1, 0, 1]) ((a / 2) • ![1, 1, 0])
        = (2 * Real.pi / a) • ![1, -1, 1] ∧
      b₃ ((a / 2) • ![0, 1, 1]) ((a / 2) • ![1, 0, 1]) ((a / 2) • ![1, 1, 0])
        = (2 * Real.pi / a) • ![1, 1, -1] := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hV : cellVolume ((a / 2) • ![0, 1, 1]) ((a / 2) • ![1, 0, 1])
      ((a / 2) • ![1, 1, 0]) = a^3 / 4 := by
    simp [cellVolume, cross_apply]
    ring
  have hVne : (a : ℝ)^3 / 4 ≠ 0 := div_ne_zero (pow_ne_zero 3 ha0) (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [b₁, b₂, b₃] <;> ext i <;> fin_cases i <;>
    rw [hV] <;> simp [cross_apply] <;> field_simp <;> ring

/-- The reciprocal of BCC(`4π/a`) is FCC(`a`): starting from BCC primitive vectors
`(2π/a) • ![-1,1,1]`, `(2π/a) • ![1,-1,1]`, `(2π/a) • ![1,1,-1]` as direct vectors
with the same parameter `a`, the reciprocal basis is `(a/2) • ![0,1,1]`,
`(a/2) • ![1,0,1]`, `(a/2) • ![1,1,0]`, by explicit computation. -/
lemma bcc_fcc (a : ℝ) (ha : 0 < a) :
    b₁ ((2 * Real.pi / a) • ![-1, 1, 1]) ((2 * Real.pi / a) • ![1, -1, 1])
          ((2 * Real.pi / a) • ![1, 1, -1])
        = (a / 2) • ![0, 1, 1] ∧
      b₂ ((2 * Real.pi / a) • ![-1, 1, 1]) ((2 * Real.pi / a) • ![1, -1, 1])
          ((2 * Real.pi / a) • ![1, 1, -1])
        = (a / 2) • ![1, 0, 1] ∧
      b₃ ((2 * Real.pi / a) • ![-1, 1, 1]) ((2 * Real.pi / a) • ![1, -1, 1])
          ((2 * Real.pi / a) • ![1, 1, -1])
        = (a / 2) • ![1, 1, 0] := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hV : cellVolume ((2 * Real.pi / a) • ![-1, 1, 1])
      ((2 * Real.pi / a) • ![1, -1, 1]) ((2 * Real.pi / a) • ![1, 1, -1])
      = (2 * Real.pi / a)^3 * 4 := by
    simp [cellVolume, cross_apply]
    ring
  have hc : (2 * Real.pi / a : ℝ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hpi) ha0
  have hc3 : ((2 * Real.pi / a : ℝ))^3 ≠ 0 := pow_ne_zero 3 hc
  have hVne : ((2 * Real.pi / a : ℝ))^3 * 4 ≠ 0 :=
    mul_ne_zero hc3 (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [b₁, b₂, b₃] <;> ext i <;> fin_cases i <;>
    rw [hV] <;> simp [cross_apply] <;> field_simp <;> ring

/-! ## E. The first Brillouin zone -/

/-- A reciprocal-lattice vector: an integer combination of the reciprocal basis. -/
noncomputable def IsRecipLatticeVec (a₁ a₂ a₃ : Fin 3 → ℝ) (G : Fin 3 → ℝ) :
    Prop :=
  ∃ h k l : ℤ, G = recipVec a₁ a₂ a₃ h k l

/-- The first Brillouin zone: the Wigner-Seitz cell of the reciprocal lattice, the set
of `k` closer to the origin than to any other reciprocal-lattice vector `G`. -/
noncomputable def firstBrillouinZone (a₁ a₂ a₃ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {k | ∀ G : Fin 3 → ℝ, IsRecipLatticeVec a₁ a₂ a₃ G →
    euclidNorm k ≤ euclidNorm (k - G)}

/-- The reciprocal-cell volume identity `V* = (2π)³/V`, stated for the first Brillouin
zone. PROVED FORM: this is the volume identity for the fundamental parallelepiped cell
of the reciprocal lattice (the same identity as `recip_volume`). The equality of the
Wigner-Seitz-cell volume with the parallelepiped-cell volume (both are fundamental
domains of the reciprocal lattice) is interpretation flagged here, NOT a proved volume
theorem: this lemma must not be read as a proof of the Wigner-Seitz volume. -/
lemma firstBZ_volume (a₁ a₂ a₃ : Fin 3 → ℝ) (hV : cellVolume a₁ a₂ a₃ ≠ 0) :
    cellVolume (b₁ a₁ a₂ a₃) (b₂ a₁ a₂ a₃) (b₃ a₁ a₂ a₃)
      = (2 * Real.pi)^3 / cellVolume a₁ a₂ a₃ :=
  recip_volume a₁ a₂ a₃ hV

/-! ## F. Discrete Fourier coefficients -/

/-- Grid point `(j₁/N) • a₁ + (j₂/N) • a₂ + (j₃/N) • a₃` in the fundamental cell,
for a grid index `j : Fin N × Fin N × Fin N`. -/
noncomputable def gridPoint (a₁ a₂ a₃ : Fin 3 → ℝ) (N : ℕ) (j : Fin N × Fin N × Fin N) :
    Fin 3 → ℝ :=
  (((j.1.val : ℕ) : ℝ) / ((N : ℕ) : ℝ)) • a₁
    + (((j.2.1.val : ℕ) : ℝ) / ((N : ℕ) : ℝ)) • a₂
    + (((j.2.2.val : ℕ) : ℝ) / ((N : ℕ) : ℝ)) • a₃

/-- Discrete Fourier coefficient of `f` at `G`: the average over the `N × N × N` grid
of `f x * exp(-I * (G ⬝ᵥ x))`. This is the discrete form; the integral form over the
fundamental parallelepiped is not stated here. -/
noncomputable def fourierCoeffDiscrete (a₁ a₂ a₃ : Fin 3 → ℝ) (N : ℕ)
    (f : (Fin 3 → ℝ) → ℂ) (G : Fin 3 → ℝ) : ℂ :=
  (1 / ((N : ℕ) : ℂ)^3) * ∑ j : Fin N × Fin N × Fin N,
    f (gridPoint a₁ a₂ a₃ N j)
      * Complex.exp (-Complex.I * (((G ⬝ᵥ gridPoint a₁ a₂ a₃ N j : ℝ)) : ℂ))

/-- Plane wave `x ↦ exp(I * (G₀ ⬝ᵥ x))` for a reciprocal-lattice vector `G₀`. -/
noncomputable def planeWave (G₀ : Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (((G₀ ⬝ᵥ x : ℝ)) : ℂ))

/-- One-dimensional geometric-sum orthogonality: if `ω^N = 1` then the sum of powers
is `N` when `ω = 1` and `0` otherwise. -/
private lemma geom_sum_omega (ω : ℂ) (N : ℕ) (hω : ω^N = 1) :
    (∑ i ∈ Finset.range N, ω^i) = (if ω = 1 then ((N : ℕ) : ℂ) else 0) := by
  by_cases h : ω = 1
  · subst h
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      eq_self_iff_true, if_true]
  · have h1 : ω - 1 ≠ 0 := sub_ne_zero.mpr h
    have h2 : (∑ i ∈ Finset.range N, ω^i) * (ω - 1) = 0 := by
      rw [geom_sum_mul, hω, sub_self]
    have h3 : (∑ i ∈ Finset.range N, ω^i) = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 h1
    rw [h3]
    simp [h]

/-- The grid phase `exp(2πi m/N)` raised to `N` is `1`. -/
private lemma hexp_pow (N : ℕ) (hN : N ≠ 0) (m : ℤ) :
    (Complex.exp (2 * ↑Real.pi * Complex.I * ↑m / ↑N))^N = 1 := by
  have hNc : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [← Complex.exp_nat_mul,
    show ((N : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I * ↑m / ↑N)
      = ↑m * (2 * ↑Real.pi * Complex.I) from by field_simp,
    Complex.exp_eq_one_iff]
  exact ⟨m, rfl⟩

/-- Finite plane-wave orthogonality for the discrete coefficients: the coefficient of
the plane wave `x ↦ exp(I * (G₀ ⬝ᵥ x))` at `G` is `1` if `G = G₀` and `0` otherwise,
where equality is in the aliasing sense made explicit here: each of the three grid
phases `exp(2πi mᵢ/N)` (for the integer coefficient differences `mᵢ`) equals `1`.
The L² Fourier expansion and any pointwise/uniform convergence theorem are explicitly
deferred (stronger convergence needs stronger hypotheses) and are not stated. -/
lemma fourierCoeffDiscrete_planeWave (a₁ a₂ a₃ : Fin 3 → ℝ)
    (hV : cellVolume a₁ a₂ a₃ ≠ 0) (N : ℕ) (hN : N ≠ 0) (h k l h₀ k₀ l₀ : ℤ) :
    fourierCoeffDiscrete a₁ a₂ a₃ N (planeWave (recipVec a₁ a₂ a₃ h₀ k₀ l₀))
        (recipVec a₁ a₂ a₃ h k l)
      = if Complex.exp (2 * ↑Real.pi * Complex.I * ↑(h₀ - h) / ↑N) = 1
          ∧ Complex.exp (2 * ↑Real.pi * Complex.I * ↑(k₀ - k) / ↑N) = 1
          ∧ Complex.exp (2 * ↑Real.pi * Complex.I * ↑(l₀ - l) / ↑N) = 1
        then (1 : ℂ) else (0 : ℂ) := by
  have hNc : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have hN3 : (((N : ℕ) : ℂ))^3 ≠ 0 := pow_ne_zero 3 hNc
  have hsummand : ∀ j : Fin N × Fin N × Fin N,
      planeWave (recipVec a₁ a₂ a₃ h₀ k₀ l₀) (gridPoint a₁ a₂ a₃ N j)
        * Complex.exp (-Complex.I
          * ((((recipVec a₁ a₂ a₃ h k l) ⬝ᵥ gridPoint a₁ a₂ a₃ N j : ℝ)) : ℂ))
      = Complex.exp (Complex.I * (((((recipVec a₁ a₂ a₃ h₀ k₀ l₀)
          - recipVec a₁ a₂ a₃ h k l) ⬝ᵥ gridPoint a₁ a₂ a₃ N j : ℝ)) : ℂ)) := by
    intro j
    simp only [planeWave, ← Complex.exp_add]
    congr 1
    rw [sub_dotProduct, sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_neg]
    ring
  have hdot : ∀ j : Fin N × Fin N × Fin N,
      ((recipVec a₁ a₂ a₃ h₀ k₀ l₀) - recipVec a₁ a₂ a₃ h k l) ⬝ᵥ
        gridPoint a₁ a₂ a₃ N j
      = 2 * Real.pi * ((((h₀ - h : ℤ)) : ℝ) * ((((j.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
        + (((k₀ - k : ℤ)) : ℝ) * ((((j.2.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
        + (((l₀ - l : ℤ)) : ℝ) * ((((j.2.2.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))) := by
    intro j
    have h0 := dot_lattice_general a₁ a₂ a₃ hV ((h₀ : ℤ) : ℝ) ((k₀ : ℤ) : ℝ)
      ((l₀ : ℤ) : ℝ) ((((j.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
      ((((j.2.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
      ((((j.2.2.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
    have h1 := dot_lattice_general a₁ a₂ a₃ hV ((h : ℤ) : ℝ) ((k : ℤ) : ℝ)
      ((l : ℤ) : ℝ) ((((j.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
      ((((j.2.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
      ((((j.2.2.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
    simp only [sub_dotProduct, recipVec, gridPoint]
    rw [h0, h1]
    simp only [Int.cast_sub]
    ring
  have hpt : ∀ j : Fin N × Fin N × Fin N,
      Complex.exp (Complex.I * (((((recipVec a₁ a₂ a₃ h₀ k₀ l₀)
          - recipVec a₁ a₂ a₃ h k l) ⬝ᵥ gridPoint a₁ a₂ a₃ N j : ℝ)) : ℂ))
      = (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(h₀ - h) / ↑N))^(j.1.val)
        * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(k₀ - k) / ↑N))^(j.2.1.val)
        * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(l₀ - l) / ↑N))^(j.2.2.val) := by
    intro j
    rw [hdot j]
    have harg : (Complex.I * (((2 * Real.pi * ((((h₀ - h : ℤ)) : ℝ) * ((((j.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
        + (((k₀ - k : ℤ)) : ℝ) * ((((j.2.1.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ))
        + (((l₀ - l : ℤ)) : ℝ) * ((((j.2.2.val : ℕ)) : ℝ) / (((N : ℕ)) : ℝ)))
        : ℝ)) : ℂ))
        = (((↑(j.1.val) : ℂ)
          * (2 * ↑Real.pi * Complex.I * ↑(h₀ - h) / ↑N)
          + (↑(j.2.1.val) : ℂ)
          * (2 * ↑Real.pi * Complex.I * ↑(k₀ - k) / ↑N))
          + (↑(j.2.2.val) : ℂ)
          * (2 * ↑Real.pi * Complex.I * ↑(l₀ - l) / ↑N)) := by
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_natCast, Complex.ofReal_intCast, Complex.ofReal_ofNat,
        Int.cast_sub]
      simp only [Complex.ofReal_sub, Complex.ofReal_intCast]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul,
      Complex.exp_nat_mul, Complex.exp_nat_mul]
  have hpt_full : ∀ j : Fin N × Fin N × Fin N,
      planeWave (recipVec a₁ a₂ a₃ h₀ k₀ l₀) (gridPoint a₁ a₂ a₃ N j)
        * Complex.exp (-Complex.I
          * ((((recipVec a₁ a₂ a₃ h k l) ⬝ᵥ gridPoint a₁ a₂ a₃ N j : ℝ)) : ℂ))
      = (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(h₀ - h) / ↑N))^(j.1.val)
        * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(k₀ - k) / ↑N))^(j.2.1.val)
        * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(l₀ - l) / ↑N))^(j.2.2.val) := by
    intro j
    rw [hsummand j]
    exact hpt j
  simp only [fourierCoeffDiscrete, hpt_full]
  simp only [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, ← Finset.mul_sum,
    ← Finset.sum_mul, mul_assoc]
  simp only [Fin.sum_univ_eq_sum_range]
  simp only [← mul_assoc]
  rw [geom_sum_omega _ N (hexp_pow N hN (h₀ - h)),
    geom_sum_omega _ N (hexp_pow N hN (k₀ - k)),
    geom_sum_omega _ N (hexp_pow N hN (l₀ - l))]
  by_cases h1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑(h₀ - h) / ↑N) = 1
    <;> by_cases h2 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑(k₀ - k) / ↑N) = 1
    <;> by_cases h3 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑(l₀ - l) / ↑N) = 1
    <;> simp only [h1, h2, h3, true_and, false_and, if_true, if_false, zero_mul,
      mul_zero]
    <;> field_simp
    <;> ring

end Crystallography
