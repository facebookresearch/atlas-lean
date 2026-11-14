/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.BravaisLattice
public import PhyslibExt.CondensedMatter.Crystallography.ReciprocalLattice
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lattice directions, planes, Miller indices and the metric tensor

Directions `[u v w]`, families of lattice planes `(h k l)`, the metric tensor `G`, and
Miller-Bravais indices for hexagonal crystals, built on the merged `BravaisLattice` API.

## i. Overview

A Bravais lattice `Λ` has primitive vectors `a₁ a₂ a₃`, the columns of its basis matrix `B`.
The metric tensor `G i j = aᵢ ⬝ aⱼ` is the Gram matrix `G = Bᵀ * B`, with inverse
`G⁻¹ = B⁻¹ * B⁻¹ᵀ`. Lengths and angles of vectors given by fractional coordinates are read
off `G`: `|x|² = ∑ i j, v i * G i j * v j` and
`⟪x, y⟫ = ∑ i j, v i * G i j * w j`, so `cos θ` is the `G`-form over `‖x‖ * ‖y‖`.

The crystallographic reciprocal basis `bⱼ`, the columns of `(B⁻¹)ᵀ`, satisfies `aᵢ ⬝ bⱼ = δᵢⱼ`
with no factor of `2π`. It is related to the physics-convention reciprocal lattice of
`ReciprocalLattice` by `(2π) • G_hkl = B* *ᵥ h`. The reciprocal-lattice vector of the Miller
indices `(h k l)` is `G_hkl = ∑ j, h j • bⱼ`, the interplanar spacing is `d = 1 / ‖G_hkl‖`,
and `1 / d² = ∑ i j, h i * G⁻¹ i j * h j`. For the simple cubic lattice of side `a` this
gives `d = a / √(h² + k² + l²)`. The `(h k l)` planes are `{x | ⟪G_hkl, x⟫ = n}` for
`n : ℤ`; shifting a plane by `G / ‖G‖²` reaches the next plane, and `d` is the shortest
distance between adjacent planes.

A direction `[u v w]` lies in the plane `(h k l)` exactly when `hu + kv + lw = 0` (the Weiss
zone law), and the zone axis shared by two planes is their index cross product. The direction
`[h k l]` is normal to the `(h k l)` planes only for cubic lattices: this holds for
`simpleCubic` and fails in general, as shown by an explicit non-cubic counterexample.
Unreduced indices scale the spacing: `d_(nh) = d_h / |n|`, so `(200)` has half the spacing
of `(100)` but obeys the same zone law up to the nonzero factor `n`.

For hexagonal crystals, Miller-Bravais plane indices `(h k i l)` satisfy `i = -(h + k)`,
and direction conversion uses the exact rational factors `U = (2u-v)/3`, `V = (2v-u)/3`,
`T = -(u+v)/3`, `W = w`, inverted by `u = U - T`, `v = V - T`, `w = W`.

## ii. Key results

- `Crystallography.BravaisLattice.metricTensor` : the metric tensor `G i j = aᵢ ⬝ aⱼ`.
- `Crystallography.BravaisLattice.normSq_fractional` : `|x|²` from `G`.
- `Crystallography.BravaisLattice.inner_fractional` : `⟪x, y⟫` from `G`.
- `Crystallography.BravaisLattice.angle_cos_fractional` : `cos θ` from `G`.
- `Crystallography.BravaisLattice.crystReciprocal` : the crystallographic reciprocal basis.
- `Crystallography.BravaisLattice.reciprocalVector` : `G_hkl`.
- `Crystallography.BravaisLattice.interplanarSpacing` : `d = 1 / ‖G_hkl‖`.
- `Crystallography.BravaisLattice.invSq_interplanarSpacing` : `1 / d²` from `G⁻¹`.
- `Crystallography.BravaisLattice.spacing_simpleCubic` : cubic `d = a / √(h²+k²+l²)`.
- `Crystallography.BravaisLattice.latticePlane` : the `(h k l)` planes.
- `Crystallography.BravaisLattice.planeShift_mem`,
  `Crystallography.BravaisLattice.planeDist_ge` : `d` is the adjacent-plane distance.
- `Crystallography.BravaisLattice.latticeDirection` : the direction `[u v w]`.
- `Crystallography.BravaisLattice.weissZoneLaw` : `hu + kv + lw = 0`.
- `Crystallography.zoneAxis` : the zone axis `h ⨯₃ h'`.
- `Crystallography.BravaisLattice.zoneAxis_mem` : the zone axis lies in both planes.
- `Crystallography.BravaisLattice.latticeDirection_eq_smul_reciprocalVector_cubic` :
  `[h k l]` is normal to `(h k l)` for cubic lattices.
- `Crystallography.BravaisLattice.exists_latticeDirection_not_parallel_reciprocalVector` :
  not so in general.
- `Crystallography.millerBravaisPlane` : `(h k i l)` with `i = -(h + k)`.
- `Crystallography.toMillerBravaisDir`, `Crystallography.ofMillerBravaisDir` : direction
  conversion and its inverse.

## iii. Table of contents

- A. The metric tensor: lengths and angles
- B. Reciprocal vectors and interplanar spacing
- C. Directions and the zone law
- D. Miller-Bravais indices

## iv. References

* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2005), Chapter 1, for
  crystal geometry, lattice planes and Miller indices.
* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapters 4 and 5, for Bravais lattices, the reciprocal lattice and lattice planes.

-/

@[expose] public section

open MeasureTheory Real
open scoped Matrix RealInnerProductSpace

namespace Crystallography

/-! ## A. The metric tensor: lengths and angles -/

namespace BravaisLattice

/-- The metric tensor `G` of a Bravais lattice: `G i j = aᵢ ⬝ aⱼ`. -/
noncomputable def metricTensor (Λ : BravaisLattice) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ⟪Λ.primitiveVector i, Λ.primitiveVector j⟫

/-- The `(i, j)` entry of the metric tensor is `aᵢ ⬝ aⱼ`. -/
@[simp] lemma metricTensor_apply (Λ : BravaisLattice) (i j : Fin 3) :
    (metricTensor Λ) i j = ⟪Λ.primitiveVector i, Λ.primitiveVector j⟫ :=
  rfl

/-- The metric tensor is the Gram matrix `G = Bᵀ * B` of the basis matrix. -/
lemma metricTensor_eq (Λ : BravaisLattice) :
    metricTensor Λ = Λ.basisMatrixᵀ * Λ.basisMatrix := by
  ext i j
  simp [metricTensor, primitiveVector, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mul_apply, dotProduct, mul_comm]

/-- The metric tensor is symmetric. -/
lemma metricTensor_symmetric (Λ : BravaisLattice) :
    (metricTensor Λ)ᵀ = metricTensor Λ := by
  ext i j
  simp only [Matrix.transpose_apply, metricTensor_apply]
  exact real_inner_comm _ _

/-- The inverse metric tensor is `G⁻¹ = B⁻¹ * B⁻¹ᵀ`. -/
lemma metricTensor_inv (Λ : BravaisLattice) :
    (metricTensor Λ)⁻¹ = Λ.basisMatrix⁻¹ * Λ.basisMatrix⁻¹ᵀ := by
  rw [metricTensor_eq, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

/-- **Lengths from the metric tensor**: the squared length of the vector with fractional
coordinates `v` is `|x|² = ∑ i j, v i * G i j * v j`. -/
theorem normSq_fractional (Λ : BravaisLattice) (v : Fin 3 → ℝ) :
    ‖∑ i, v i • Λ.primitiveVector i‖ ^ 2
      = ∑ i, ∑ j, v i * (metricTensor Λ) i j * v j := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, metricTensor_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Inner products from the metric tensor**: `⟪x, y⟫ = ∑ i j, v i * G i j * w j`. -/
lemma inner_fractional (Λ : BravaisLattice) (v w : Fin 3 → ℝ) :
    ⟪∑ i, v i • Λ.primitiveVector i, ∑ j, w j • Λ.primitiveVector j⟫
      = ∑ i, ∑ j, v i * (metricTensor Λ) i j * w j := by
  rw [sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, metricTensor_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Angles from the metric tensor**: `cos θ = ⟪x, y⟫ / (‖x‖ * ‖y‖)` with the inner product
given by `G`. -/
lemma angle_cos_fractional (Λ : BravaisLattice) (v w : Fin 3 → ℝ)
    (x y : EuclideanSpace ℝ (Fin 3))
    (hx : x = ∑ i, v i • Λ.primitiveVector i)
    (hy : y = ∑ j, w j • Λ.primitiveVector j) :
    ⟪x, y⟫ / (‖x‖ * ‖y‖)
      = (∑ i, ∑ j, v i * (metricTensor Λ) i j * w j) / (‖x‖ * ‖y‖) := by
  rw [hx, hy, inner_fractional]

end BravaisLattice

/-! ## B. Reciprocal vectors and interplanar spacing -/

namespace BravaisLattice

/-- The crystallographic reciprocal basis vector `bⱼ` (no `2π` factor): column `j` of
`(B⁻¹)ᵀ`. -/
noncomputable def crystReciprocal (Λ : BravaisLattice) (j : Fin 3) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (Λ.basisMatrix⁻¹ᵀ.col j)

/-- Duality of the crystallographic reciprocal basis: `aᵢ ⬝ bⱼ = δᵢⱼ`. -/
lemma inner_primitiveVector_crystReciprocal (Λ : BravaisLattice) (i j : Fin 3) :
    ⟪Λ.primitiveVector i, Λ.crystReciprocal j⟫ = if i = j then 1 else 0 := by
  have hB : IsUnit Λ.basisMatrix.det := isUnit_iff_ne_zero.mpr Λ.det_ne_zero
  have hT : IsUnit Λ.basisMatrixᵀ.det := by rwa [Matrix.det_transpose]
  have h1 : Λ.basisMatrixᵀ * Λ.basisMatrix⁻¹ᵀ = 1 := by
    rw [Matrix.transpose_nonsing_inv, Matrix.mul_nonsing_inv _ hT]
  have hbridge : ⟪Λ.primitiveVector i, Λ.crystReciprocal j⟫
      = (Λ.basisMatrixᵀ * Λ.basisMatrix⁻¹ᵀ) i j := by
    simp [crystReciprocal, primitiveVector, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.mul_apply, dotProduct, mul_comm]
  rw [hbridge, h1]
  exact Matrix.one_apply

/-- Duality with the factors swapped: `bⱼ ⬝ aᵢ = δⱼᵢ`. -/
lemma inner_crystReciprocal_primitiveVector (Λ : BravaisLattice) (j i : Fin 3) :
    ⟪Λ.crystReciprocal j, Λ.primitiveVector i⟫ = if j = i then 1 else 0 := by
  rw [real_inner_comm, inner_primitiveVector_crystReciprocal]
  by_cases hij : i = j
  · subst hij
    rfl
  · simp [hij, Ne.symm hij]

/-- The Gram matrix of the crystallographic reciprocal basis is the inverse metric:
`bⱼ ⬝ bₖ = G⁻¹ j k`. -/
lemma inner_crystReciprocal (Λ : BravaisLattice) (j k : Fin 3) :
    ⟪Λ.crystReciprocal j, Λ.crystReciprocal k⟫ = (metricTensor Λ)⁻¹ j k := by
  have hbridge : ⟪Λ.crystReciprocal j, Λ.crystReciprocal k⟫
      = ((Λ.basisMatrix⁻¹ᵀ)ᵀ * Λ.basisMatrix⁻¹ᵀ) j k := by
    simp [crystReciprocal, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply,
      dotProduct, mul_comm]
  rw [hbridge, Matrix.transpose_transpose, ← metricTensor_inv]

/-- The crystallographic reciprocal-lattice vector `G_hkl = ∑ j, h j • bⱼ` (no `2π`
factor). -/
noncomputable def reciprocalVector (Λ : BravaisLattice) (h : Fin 3 → ℤ) :
    EuclideanSpace ℝ (Fin 3) :=
  ∑ j, (h j : ℝ) • Λ.crystReciprocal j

/-- The reciprocal vector of the zero indices is zero. -/
lemma reciprocalVector_zero (Λ : BravaisLattice) : reciprocalVector Λ 0 = 0 := by
  simp [reciprocalVector]

/-- Pairing a reciprocal vector with a primitive vector reads off the index:
`G_h ⬝ aᵢ = h i`. -/
lemma inner_reciprocalVector_primitiveVector (Λ : BravaisLattice) (h : Fin 3 → ℤ)
    (i : Fin 3) :
    ⟪reciprocalVector Λ h, Λ.primitiveVector i⟫ = (h i : ℝ) := by
  simp only [reciprocalVector]
  rw [sum_inner]
  simp_rw [real_inner_smul_left, inner_crystReciprocal_primitiveVector]
  simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

/-- Distinct index triples give distinct reciprocal vectors. -/
lemma reciprocalVector_injective (Λ : BravaisLattice) :
    Function.Injective (reciprocalVector Λ) := by
  intro h h' hGh
  funext i
  have e := congrArg (fun G => ⟪G, Λ.primitiveVector i⟫) hGh
  simp only [inner_reciprocalVector_primitiveVector] at e
  exact_mod_cast e

/-- A nonzero index triple gives a nonzero reciprocal vector. -/
private lemma reciprocalVector_ne_zero (Λ : BravaisLattice) (h : Fin 3 → ℤ)
    (h0 : h ≠ 0) : reciprocalVector Λ h ≠ 0 := by
  intro hcon
  apply h0
  have h0' : reciprocalVector Λ h = reciprocalVector Λ 0 := by
    rw [hcon, reciprocalVector_zero]
  exact reciprocalVector_injective Λ h0'

/-- Scaling the indices scales the reciprocal vector: `G_(n h) = n • G_h`. Unreduced indices
such as `(200)` give a multiple of the reduced `(100)` vector. -/
lemma reciprocalVector_smul (Λ : BravaisLattice) (n : ℤ) (h : Fin 3 → ℤ) :
    reciprocalVector Λ (n • h) = (n : ℝ) • reciprocalVector Λ h := by
  simp only [reciprocalVector, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul,
    ← Finset.smul_sum]

/-- Pairing a reciprocal vector with a general vector sums the indices against its fractional
coordinates. -/
lemma inner_reciprocalVector_eq (Λ : BravaisLattice) (h : Fin 3 → ℤ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ⟪reciprocalVector Λ h, x⟫ = ∑ j, (h j : ℝ) * (Λ.basis.repr x) j := by
  have hdual : ∀ j, ⟪reciprocalVector Λ h, Λ.basis j⟫ = (h j : ℝ) := by
    intro j
    rw [coe_basis]
    exact inner_reciprocalVector_primitiveVector Λ h j
  nth_rewrite 1 [eq_sum_repr_smul Λ.basis x]
  rw [inner_sum]
  simp_rw [real_inner_smul_right, hdual]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The squared length of a reciprocal vector is the `G⁻¹` quadratic form of its indices. -/
lemma normSq_reciprocalVector (Λ : BravaisLattice) (h : Fin 3 → ℤ) :
    ‖reciprocalVector Λ h‖ ^ 2
      = ∑ i, ∑ j, (h i : ℝ) * ((metricTensor Λ)⁻¹ i j) * (h j : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [reciprocalVector]
  rw [sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, inner_crystReciprocal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The interplanar spacing `d = 1 / ‖G_hkl‖`. -/
noncomputable def interplanarSpacing (Λ : BravaisLattice) (h : Fin 3 → ℤ) : ℝ :=
  1 / ‖reciprocalVector Λ h‖

/-- The spacing of a nonzero family is positive. -/
lemma interplanarSpacing_pos (Λ : BravaisLattice) (h : Fin 3 → ℤ) (h0 : h ≠ 0) :
    0 < interplanarSpacing Λ h := by
  simp only [interplanarSpacing]
  exact div_pos one_pos (norm_pos_iff.mpr (reciprocalVector_ne_zero Λ h h0))

/-- **Interplanar spacing from the inverse metric**:
`1 / d² = ∑ i j, h i * G⁻¹ i j * h j`. -/
theorem invSq_interplanarSpacing (Λ : BravaisLattice) (h : Fin 3 → ℤ) (h0 : h ≠ 0) :
    1 / (interplanarSpacing Λ h) ^ 2
      = ∑ i, ∑ j, (h i : ℝ) * ((metricTensor Λ)⁻¹ i j) * (h j : ℝ) := by
  have hd2 : (interplanarSpacing Λ h) ^ 2 = 1 / ‖reciprocalVector Λ h‖ ^ 2 := by
    simp only [interplanarSpacing, div_pow, one_pow]
  rw [hd2, one_div_one_div, normSq_reciprocalVector]

/-- The crystallographic reciprocal vector is the physics (`2π`) reciprocal lattice vector
divided by `2π`: `(2π) • G_h = B* *ᵥ h`. -/
lemma reciprocalVector_eq_phys_smul (Λ : BravaisLattice) (h : Fin 3 → ℤ) :
    (2 * π) • reciprocalVector Λ h = Λ.reciprocal.latticeVector h := by
  refine InnerProductSpace.ext_inner_right_basis Λ.basis fun j => ?_
  rw [real_inner_smul_left, coe_basis, inner_reciprocalVector_primitiveVector,
    inner_reciprocal_latticeVector_primitiveVector]

/-- The metric tensor of the simple cubic lattice of side `a` is `G = a² • 1`. -/
lemma metricTensor_simpleCubic (a : ℝ) (ha : 0 < a) :
    metricTensor (simpleCubic a ha) = a ^ 2 • 1 := by
  rw [metricTensor_eq]
  simp only [simpleCubic, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.one_mul, smul_smul]
  congr 1
  ring

/-- Entries of the cubic metric tensor: `G i j = a² δᵢⱼ`. -/
lemma metricTensor_simpleCubic_apply (a : ℝ) (ha : 0 < a) (i j : Fin 3) :
    (metricTensor (simpleCubic a ha)) i j = if i = j then a ^ 2 else 0 := by
  rw [metricTensor_simpleCubic a ha]
  simp [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The inverse metric tensor of the simple cubic lattice is `G⁻¹ = (a²)⁻¹ • 1`. -/
lemma metricTensor_inv_simpleCubic (a : ℝ) (ha : 0 < a) :
    (metricTensor (simpleCubic a ha))⁻¹ = (a ^ 2)⁻¹ • 1 := by
  rw [metricTensor_simpleCubic a ha]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), one_smul]

/-- Entries of the cubic inverse metric tensor: `G⁻¹ i j = (a²)⁻¹ δᵢⱼ`. -/
lemma metricTensor_inv_simpleCubic_apply (a : ℝ) (ha : 0 < a) (i j : Fin 3) :
    ((metricTensor (simpleCubic a ha))⁻¹) i j
      = if i = j then (a ^ 2)⁻¹ else 0 := by
  rw [metricTensor_inv_simpleCubic a ha]
  simp [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- Quadratic form of a scalar matrix: `∑ i j, f i * (c δᵢⱼ) * f j = c * ∑ i, f i * f i`. -/
private lemma quadraticForm_diag (f : Fin 3 → ℝ) (c : ℝ) :
    (∑ i, ∑ j, f i * (if i = j then c else 0) * f j) = c * ∑ i, f i * f i := by
  have h1 : ∀ i, (∑ j, f i * (if i = j then c else 0) * f j) = (f i * c) * f i := by
    intro i
    simp [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq]
  simp_rw [h1]
  have h2 : (∑ i, (f i * c) * f i) = ∑ i, c * (f i * f i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h2, ← Finset.mul_sum]

/-- A nonzero index triple has positive sum of squares. -/
private lemma sumSq_pos_of_ne_zero (h : Fin 3 → ℤ) (h0 : h ≠ 0) :
    0 < ((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
  fin_cases i
  · have hi0 : h 0 ≠ 0 := hi
    have hne0 : ((h 0 : ℝ)) ≠ 0 := by exact_mod_cast hi0
    have p : 0 < ((h 0 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hne0
    have n1 : 0 ≤ ((h 1 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_nonneg _
    have n2 : 0 ≤ ((h 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_nonneg _
    linarith
  · have hi1 : h 1 ≠ 0 := hi
    have hne1 : ((h 1 : ℝ)) ≠ 0 := by exact_mod_cast hi1
    have p : 0 < ((h 1 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hne1
    have n0 : 0 ≤ ((h 0 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_nonneg _
    have n2 : 0 ≤ ((h 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_nonneg _
    linarith
  · have hi2 : h 2 ≠ 0 := hi
    have hne2 : ((h 2 : ℝ)) ≠ 0 := by exact_mod_cast hi2
    have p : 0 < ((h 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hne2
    have n0 : 0 ≤ ((h 0 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_nonneg _
    have n1 : 0 ≤ ((h 1 : ℝ)) ^ 2 := by
      rw [pow_two]
      exact mul_self_nonneg _
    linarith

/-- **Cubic interplanar spacing**: `d = a / √(h² + k² + l²)` for the simple cubic lattice of
side `a`. -/
theorem spacing_simpleCubic (a : ℝ) (ha : 0 < a) (h : Fin 3 → ℤ) (h0 : h ≠ 0) :
    interplanarSpacing (simpleCubic a ha) h
      = a / Real.sqrt (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2) := by
  have hS : 0 < ((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2 :=
    sumSq_pos_of_ne_zero h h0
  have hQF : (∑ i, ∑ j, (h i : ℝ) * ((metricTensor (simpleCubic a ha))⁻¹ i j)
        * (h j : ℝ))
      = (a ^ 2)⁻¹ * (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2) := by
    simp_rw [metricTensor_inv_simpleCubic_apply]
    rw [quadraticForm_diag]
    congr 1
    rw [Fin.sum_univ_three]
    ring
  have hInv := invSq_interplanarSpacing (simpleCubic a ha) h h0
  rw [hQF] at hInv
  have hd : 0 < interplanarSpacing (simpleCubic a ha) h :=
    interplanarSpacing_pos _ _ h0
  have hRHS : 0 < a / Real.sqrt
      (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2) :=
    div_pos ha (Real.sqrt_pos_of_pos hS)
  have h3 : (interplanarSpacing (simpleCubic a ha) h) ^ 2
      = 1 / ((a ^ 2)⁻¹ * (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2)) := by
    rw [← hInv, one_div_one_div]
  have e2 : (1 : ℝ) / ((a ^ 2)⁻¹ * (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2
      + ((h 2 : ℝ)) ^ 2))
      = a ^ 2 / (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2) := by
    rw [mul_comm ((a ^ 2)⁻¹) _, ← div_eq_mul_inv, one_div_div]
  have e1 : (interplanarSpacing (simpleCubic a ha) h) ^ 2
      = a ^ 2 / (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2) :=
    h3.trans e2
  have eR : (a / Real.sqrt (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2)) ^ 2
      = a ^ 2 / (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hS)]
  have hsq : (interplanarSpacing (simpleCubic a ha) h) ^ 2
      = (a / Real.sqrt (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2)) ^ 2 :=
    e1.trans eR.symm
  have g1 : Real.sqrt ((interplanarSpacing (simpleCubic a ha) h) ^ 2)
      = Real.sqrt ((a / Real.sqrt
        (((h 0 : ℝ)) ^ 2 + ((h 1 : ℝ)) ^ 2 + ((h 2 : ℝ)) ^ 2)) ^ 2) := by
    rw [hsq]
  rw [Real.sqrt_sq (le_of_lt hd), Real.sqrt_sq (le_of_lt hRHS)] at g1
  exact g1

/-- The `n`-th plane of the `(h k l)` family: `{x | ⟪G_hkl, x⟫ = n}`. -/
noncomputable def latticePlane (Λ : BravaisLattice) (h : Fin 3 → ℤ) (n : ℤ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ⟪reciprocalVector Λ h, x⟫ = (n : ℝ)}

/-- A point lies in the `n`-th `(h k l)` plane exactly when its fractional coordinates satisfy
`∑ j, h j * c j = n`. -/
lemma mem_latticePlane_iff (Λ : BravaisLattice) (h : Fin 3 → ℤ) (n : ℤ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ latticePlane Λ h n ↔ ∑ j, (h j : ℝ) * (Λ.basis.repr x) j = (n : ℝ) := by
  simp [latticePlane, Set.mem_ofPred_eq, inner_reciprocalVector_eq]

/-- Shifting a point of the `n`-th plane by `G / ‖G‖²` reaches the `(n+1)`-st plane. -/
lemma planeShift_mem (Λ : BravaisLattice) (h : Fin 3 → ℤ) (n : ℤ)
    (x : EuclideanSpace ℝ (Fin 3)) (hG : reciprocalVector Λ h ≠ 0)
    (hx : x ∈ latticePlane Λ h n) :
    x + (‖reciprocalVector Λ h‖ ^ 2)⁻¹ • reciprocalVector Λ h
      ∈ latticePlane Λ h (n + 1) := by
  have hGn : ‖reciprocalVector Λ h‖ ≠ 0 := norm_ne_zero_iff.mpr hG
  have hGs : ⟪reciprocalVector Λ h,
      (‖reciprocalVector Λ h‖ ^ 2)⁻¹ • reciprocalVector Λ h⟫ = 1 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq,
      inv_mul_cancel₀ (pow_ne_zero 2 hGn)]
  simp only [latticePlane, Set.mem_ofPred_eq] at hx ⊢
  rw [inner_add_right, hx, hGs, Int.cast_add, Int.cast_one]

/-- The plane-to-plane shift has length `d`. -/
lemma planeShift_norm (Λ : BravaisLattice) (h : Fin 3 → ℤ)
    (hG : reciprocalVector Λ h ≠ 0) :
    ‖(‖reciprocalVector Λ h‖ ^ 2)⁻¹ • reciprocalVector Λ h‖
      = interplanarSpacing Λ h := by
  have hGpos : 0 < ‖reciprocalVector Λ h‖ := norm_pos_iff.mpr hG
  have hc : (‖reciprocalVector Λ h‖ ^ 2)⁻¹ * ‖reciprocalVector Λ h‖
      = (‖reciprocalVector Λ h‖)⁻¹ := by
    rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hGpos.ne', mul_one]
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr (pow_pos hGpos 2))), hc]
  simp [interplanarSpacing, one_div]

/-- The spacing `d` is a lower bound for the distance between adjacent `(h k l)` planes. -/
lemma planeDist_ge (Λ : BravaisLattice) (h : Fin 3 → ℤ)
    (x y : EuclideanSpace ℝ (Fin 3)) (hG : reciprocalVector Λ h ≠ 0)
    (hx : x ∈ latticePlane Λ h 0) (hy : y ∈ latticePlane Λ h 1) :
    interplanarSpacing Λ h ≤ ‖x - y‖ := by
  simp only [latticePlane, Set.mem_ofPred_eq, Int.cast_zero, Int.cast_one] at hx hy
  have hval : ⟪reciprocalVector Λ h, y - x⟫ = 1 := by
    rw [inner_sub_right, hy, hx, sub_zero]
  have hGpos : 0 < ‖reciprocalVector Λ h‖ := norm_pos_iff.mpr hG
  have hCS : (1 : ℝ) ≤ ‖reciprocalVector Λ h‖ * ‖y - x‖ := by
    rw [← hval]
    exact real_inner_le_norm _ _
  have h2 : (1 / ‖reciprocalVector Λ h‖) * ‖reciprocalVector Λ h‖
      ≤ ‖y - x‖ * ‖reciprocalVector Λ h‖ := by
    rw [div_mul_cancel₀ 1 hGpos.ne']
    calc (1 : ℝ) ≤ ‖reciprocalVector Λ h‖ * ‖y - x‖ := hCS
    _ = ‖y - x‖ * ‖reciprocalVector Λ h‖ := mul_comm _ _
  have h3 : 1 / ‖reciprocalVector Λ h‖ ≤ ‖y - x‖ :=
    le_of_mul_le_mul_right h2 hGpos
  rw [norm_sub_rev] at h3
  exact h3

/-- Unreduced indices shrink the spacing: `d_(n h) = d_h / |n|`. -/
lemma interplanarSpacing_smul (Λ : BravaisLattice) (n : ℤ) (h : Fin 3 → ℤ)
    (hn : n ≠ 0) (h0 : h ≠ 0) :
    interplanarSpacing Λ (n • h) = interplanarSpacing Λ h / |(n : ℝ)| := by
  simp only [interplanarSpacing, reciprocalVector_smul, norm_smul, Real.norm_eq_abs]
  rw [div_div, mul_comm |(n : ℝ)| _]

end BravaisLattice

/-! ## C. Directions and the zone law -/

/-- The zone axis of two lattice planes: the index cross product `h ⨯₃ h'`. -/
noncomputable def zoneAxis (h h' : Fin 3 → ℤ) : Fin 3 → ℤ :=
  h ⨯₃ h'

/-- The zone axis is perpendicular to the first plane's indices. -/
lemma dotProduct_zoneAxis_left (h h' : Fin 3 → ℤ) : h ⬝ᵥ zoneAxis h h' = 0 := by
  simp [zoneAxis, dotProduct, Fin.sum_univ_three, cross_apply]
  ring

/-- The zone axis is perpendicular to the second plane's indices. -/
lemma dotProduct_zoneAxis_right (h h' : Fin 3 → ℤ) : h' ⬝ᵥ zoneAxis h h' = 0 := by
  simp [zoneAxis, dotProduct, Fin.sum_univ_three, cross_apply]
  ring

/-- The Weiss sum is the index dot product. -/
private lemma weissSum_eq_dotProduct (h u : Fin 3 → ℤ) :
    h 0 * u 0 + h 1 * u 1 + h 2 * u 2 = h ⬝ᵥ u := by
  simp [dotProduct, Fin.sum_univ_three]

namespace BravaisLattice

/-- The lattice direction `[u v w]`: the lattice vector with cell index `u`. -/
noncomputable def latticeDirection (Λ : BravaisLattice) (u : Fin 3 → ℤ) :
    EuclideanSpace ℝ (Fin 3) :=
  Λ.latticeVector u

/-- A lattice direction is the lattice vector of its index triple. -/
lemma latticeDirection_eq_latticeVector (Λ : BravaisLattice) (u : Fin 3 → ℤ) :
    latticeDirection Λ u = Λ.latticeVector u :=
  rfl

/-- A lattice direction is the integer combination `∑ j, u j • aⱼ` of the primitive
vectors. -/
lemma latticeDirection_eq_sum (Λ : BravaisLattice) (u : Fin 3 → ℤ) :
    latticeDirection Λ u = ∑ j, (u j : ℝ) • Λ.primitiveVector j := by
  change Λ.latticeVector u = _
  rw [latticeVector_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coe_basis]

/-- Pairing a lattice direction with a primitive vector contracts the indices against a row
of `G`. -/
lemma inner_latticeDirection_primitiveVector (Λ : BravaisLattice) (u : Fin 3 → ℤ)
    (i : Fin 3) :
    ⟪latticeDirection Λ u, Λ.primitiveVector i⟫
      = ∑ j, (u j : ℝ) * (metricTensor Λ) j i := by
  simp only [latticeDirection_eq_sum, sum_inner]
  simp_rw [real_inner_smul_left, ← metricTensor_apply]

/-- A reciprocal vector pairs with a lattice direction to the index sum
`h 0 * u 0 + h 1 * u 1 + h 2 * u 2`. -/
lemma inner_reciprocalVector_latticeDirection (Λ : BravaisLattice) (h u : Fin 3 → ℤ) :
    ⟪reciprocalVector Λ h, latticeDirection Λ u⟫
      = ((h 0 * u 0 + h 1 * u 1 + h 2 * u 2 : ℤ) : ℝ) := by
  rw [inner_reciprocalVector_eq]
  simp only [latticeDirection, repr_latticeVector, Fin.sum_univ_three, Int.cast_add,
    Int.cast_mul]

/-- **Weiss zone law**: the direction `[u v w]` lies in the plane `(h k l)` exactly when
`hu + kv + lw = 0`. -/
theorem weissZoneLaw (Λ : BravaisLattice) (h u : Fin 3 → ℤ) :
    ⟪reciprocalVector Λ h, latticeDirection Λ u⟫ = 0
      ↔ h 0 * u 0 + h 1 * u 1 + h 2 * u 2 = 0 := by
  rw [inner_reciprocalVector_latticeDirection, Int.cast_eq_zero]

/-- **The zone axis of two planes is their index cross product**: the direction with indices
`h ⨯₃ h'` lies in both the `(h k l)` and the `(h' k' l')` planes. -/
theorem zoneAxis_mem (Λ : BravaisLattice) (h h' : Fin 3 → ℤ) :
    ⟪reciprocalVector Λ h, latticeDirection Λ (zoneAxis h h')⟫ = 0
      ∧ ⟪reciprocalVector Λ h', latticeDirection Λ (zoneAxis h h')⟫ = 0 := by
  constructor
  · rw [weissZoneLaw, weissSum_eq_dotProduct, dotProduct_zoneAxis_left]
  · rw [weissZoneLaw, weissSum_eq_dotProduct, dotProduct_zoneAxis_right]

/-- In a cubic lattice the direction `[h k l]` is a multiple of `G_hkl`, hence normal to the
`(h k l)` planes: `d = a² • G`. -/
lemma latticeDirection_eq_smul_reciprocalVector_cubic (a : ℝ) (ha : 0 < a)
    (h : Fin 3 → ℤ) :
    latticeDirection (simpleCubic a ha) h
      = (a ^ 2) • reciprocalVector (simpleCubic a ha) h := by
  refine InnerProductSpace.ext_inner_right_basis (simpleCubic a ha).basis fun j => ?_
  rw [coe_basis, inner_latticeDirection_primitiveVector, real_inner_smul_left,
    inner_reciprocalVector_primitiveVector]
  simp_rw [metricTensor_simpleCubic_apply]
  simp [mul_ite, mul_zero, Finset.sum_ite_eq']
  ring

/-- `[h k l]` is normal to `(h k l)` only for cubic lattices: an explicit non-cubic lattice
and indices whose direction is not a multiple of the reciprocal vector. -/
lemma exists_latticeDirection_not_parallel_reciprocalVector :
    ∃ (Λ : BravaisLattice) (h : Fin 3 → ℤ),
      ¬ ∃ c : ℝ, latticeDirection Λ h = c • reciprocalVector Λ h := by
  set B : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 2] with hBdef
  have hdet : B.det ≠ 0 := by
    norm_num [hBdef, Matrix.det_fin_three]
  set Λ₀ : BravaisLattice := ⟨B, hdet⟩ with hΛdef
  have hB : Λ₀.basisMatrix = B := by rw [hΛdef]
  have hG : metricTensor Λ₀ = Bᵀ * B := by
    rw [metricTensor_eq, hB]
  set h : Fin 3 → ℤ := ![1, 0, 1] with hhdef
  have hh0 : h 0 = 1 := by simp [hhdef]
  have hh1 : h 1 = 0 := by simp [hhdef]
  have hh2 : h 2 = 1 := by simp [hhdef]
  have g00 : (metricTensor Λ₀) 0 0 = 1 := by
    rw [hG]
    norm_num [hBdef, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  have g10 : (metricTensor Λ₀) 1 0 = 0 := by
    rw [hG]
    norm_num [hBdef, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  have g20 : (metricTensor Λ₀) 2 0 = 0 := by
    rw [hG]
    norm_num [hBdef, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  have g02 : (metricTensor Λ₀) 0 2 = 0 := by
    rw [hG]
    norm_num [hBdef, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  have g12 : (metricTensor Λ₀) 1 2 = 0 := by
    rw [hG]
    norm_num [hBdef, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  have g22 : (metricTensor Λ₀) 2 2 = 4 := by
    rw [hG]
    norm_num [hBdef, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  refine ⟨Λ₀, h, ?_⟩
  rintro ⟨c, hc⟩
  have e0 := congrArg (fun x => ⟪x, Λ₀.primitiveVector 0⟫) hc
  have e2 := congrArg (fun x => ⟪x, Λ₀.primitiveVector 2⟫) hc
  simp only [real_inner_smul_left, inner_reciprocalVector_primitiveVector,
    inner_latticeDirection_primitiveVector, Fin.sum_univ_three] at e0 e2
  rw [hh0, hh1, hh2, g00, g10, g20] at e0
  rw [hh0, hh1, hh2, g02, g12, g22] at e2
  norm_num at e0 e2
  linarith

end BravaisLattice

/-! ## D. Miller-Bravais indices -/

/-- Miller-Bravais plane indices `(h k i l)` with `i = -(h + k)`. -/
noncomputable def millerBravaisPlane (h : Fin 3 → ℤ) : Fin 4 → ℤ :=
  ![h 0, h 1, -(h 0 + h 1), h 2]

/-- The redundant Miller-Bravais index is `i = -(h + k)`. -/
lemma millerBravaisPlane_third (h : Fin 3 → ℤ) :
    (millerBravaisPlane h) 2 = -(h 0 + h 1) := by
  simp [millerBravaisPlane]

/-- The first three Miller-Bravais plane indices sum to zero. -/
lemma millerBravaisPlane_sum (h : Fin 3 → ℤ) :
    (millerBravaisPlane h) 0 + (millerBravaisPlane h) 1 + (millerBravaisPlane h) 2
      = 0 := by
  have e0 : (millerBravaisPlane h) 0 = h 0 := by simp [millerBravaisPlane]
  have e1 : (millerBravaisPlane h) 1 = h 1 := by simp [millerBravaisPlane]
  have e2 : (millerBravaisPlane h) 2 = -(h 0 + h 1) := by simp [millerBravaisPlane]
  rw [e0, e1, e2]
  ring

/-- Miller-Bravais direction conversion with exact rational factors: `U = (2u-v)/3`,
`V = (2v-u)/3`, `T = -(u+v)/3`, `W = w`. -/
noncomputable def toMillerBravaisDirQ (u : Fin 3 → ℚ) : Fin 4 → ℚ :=
  ![((2 * u 0 - u 1) / 3), ((2 * u 1 - u 0) / 3), (-(u 0 + u 1) / 3), u 2]

/-- Inverse Miller-Bravais direction conversion: `u = U - T`, `v = V - T`, `w = W`. -/
noncomputable def ofMillerBravaisDir (U : Fin 4 → ℚ) : Fin 3 → ℚ :=
  ![U 0 - U 2, U 1 - U 2, U 3]

/-- Miller-Bravais direction conversion for integer directions. -/
noncomputable def toMillerBravaisDir (u : Fin 3 → ℤ) : Fin 4 → ℚ :=
  toMillerBravaisDirQ (fun i => (u i : ℚ))

/-- Converted directions satisfy `U + V + T = 0`. -/
lemma toMillerBravaisDirQ_sum (u : Fin 3 → ℚ) :
    (toMillerBravaisDirQ u) 0 + (toMillerBravaisDirQ u) 1 + (toMillerBravaisDirQ u) 2
      = 0 := by
  have e0 : (toMillerBravaisDirQ u) 0 = (2 * u 0 - u 1) / 3 := by
    simp [toMillerBravaisDirQ]
  have e1 : (toMillerBravaisDirQ u) 1 = (2 * u 1 - u 0) / 3 := by
    simp [toMillerBravaisDirQ]
  have e2 : (toMillerBravaisDirQ u) 2 = (-(u 0 + u 1) / 3) := by
    simp [toMillerBravaisDirQ]
  rw [e0, e1, e2]
  field_simp
  ring

/-- The Miller-Bravais direction conversion is left-invertible. -/
theorem ofMillerBravaisDir_toMillerBravaisDirQ (u : Fin 3 → ℚ) :
    ofMillerBravaisDir (toMillerBravaisDirQ u) = u := by
  funext i
  fin_cases i <;> simp [toMillerBravaisDirQ, ofMillerBravaisDir] <;> field_simp <;> ring

/-- The Miller-Bravais direction conversion is right-invertible on indices with
`U + V + T = 0`. -/
theorem toMillerBravaisDirQ_ofMillerBravaisDir (U : Fin 4 → ℚ)
    (hsum : U 0 + U 1 + U 2 = 0) :
    toMillerBravaisDirQ (ofMillerBravaisDir U) = U := by
  funext i
  fin_cases i <;> simp [toMillerBravaisDirQ, ofMillerBravaisDir] <;> linarith

/-- Round trip for integer directions, as rational vectors. -/
lemma ofMillerBravaisDir_toMillerBravaisDir (u : Fin 3 → ℤ) :
    ofMillerBravaisDir (toMillerBravaisDir u) = fun i => ((u i : ℤ) : ℚ) := by
  funext i
  fin_cases i <;> simp [toMillerBravaisDir, toMillerBravaisDirQ, ofMillerBravaisDir]
    <;> field_simp <;> ring

end Crystallography
