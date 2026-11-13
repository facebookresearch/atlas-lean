/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.CrossProduct
public import PhyslibExt.CondensedMatter.Crystallography.BravaisLattice

/-!
# Reciprocal lattices and Brillouin zones

The reciprocal of a Bravais lattice in the physics `2π` convention, and the first Brillouin zone.

## i. Overview

A Bravais lattice `Λ` has primitive vectors `a₁ a₂ a₃`, the columns of its basis matrix `B` (in
Lean `Λ.primitiveVector 0`, `Λ.primitiveVector 1` and `Λ.primitiveVector 2`), and oriented cell
volume `V = det B = a₁ ⬝ᵥ (a₂ ⨯₃ a₃)`, which is nonzero by the definition of `BravaisLattice`.

Convention: this file uses the physics convention `aᵢ ⬝ bⱼ = 2π δᵢⱼ` throughout, not the
crystallographic convention without the factor `2π`. The reciprocal lattice `Λ.reciprocal` is the
Bravais lattice whose primitive vectors are given by the cross-product formula

  `b₁ = (2π / V) • (a₂ ⨯₃ a₃)`, `b₂ = (2π / V) • (a₃ ⨯₃ a₁)`, `b₃ = (2π / V) • (a₁ ⨯₃ a₂)`,

that is `bⱼ = (2π / V) • (a_{j+1} ⨯₃ a_{j+2})` with indices modulo `3`. Because `V ≠ 0` is part
of the data of a `BravaisLattice`, the construction never meets a singular basis.

The reciprocal basis satisfies `aᵢ ⬝ bⱼ = 2π δᵢⱼ`, equivalently `Bᵀ B* = 2π • 1`, and it is the
only basis with this property, so `B* = 2π • (B⁻¹)ᵀ`. Its oriented cell volume is `(2π)³ / V`, so
its primitive cell has Lebesgue volume `(2π)³ / |V|`, and taking the reciprocal twice gives back
the original Bravais lattice. A vector `G` lies in the reciprocal lattice exactly when
`G ⬝ R ∈ 2πℤ`, equivalently `exp (i G ⬝ R) = 1`, for every lattice vector `R`. In particular the
reciprocal lattice depends only on the lattice and not on the choice of primitive vectors. The
reciprocal of the simple cubic lattice of side `a` is the simple cubic lattice of side `2π / a`,
and the reciprocal of the face-centered cubic lattice with conventional cubic cell of side `a` is
the body-centered cubic lattice of side `4π / a`, and conversely.

The Wigner–Seitz cell of a Bravais lattice, the set of points at least as close to the origin as to
any lattice point, is a fundamental domain for the lattice translations; hence its volume is the
cell volume `|V|`. The first Brillouin zone is the Wigner–Seitz cell of the reciprocal lattice. It
is a fundamental domain for the reciprocal lattice and has volume `(2π)³ / |V|`.

PhyslibAlpha's `CondensedMatter.Crystal.reciprocalLattice` is the additive subgroup cut out by
the conditions `aⱼ ⬝ G ∈ 2πℤ` for a family of vectors `aⱼ` in any dimension. This file works with
`BravaisLattice` and does not import PhyslibAlpha.

## ii. Key results

- `Crystallography.crossColumns` : the matrix with columns `a₂ ⨯₃ a₃`, `a₃ ⨯₃ a₁`, `a₁ ⨯₃ a₂`.
- `Crystallography.BravaisLattice.reciprocal` : the reciprocal Bravais lattice.
- `Crystallography.BravaisLattice.reciprocal_primitiveVector` : the cross-product formula.
- `Crystallography.BravaisLattice.inner_primitiveVector_reciprocal` : `aᵢ ⬝ bⱼ = 2π δᵢⱼ`.
- `Crystallography.BravaisLattice.reciprocal_basisMatrix_eq_iff` : `B*` is the only matrix `M`
  with `Bᵀ M = 2π • 1`.
- `Crystallography.BravaisLattice.reciprocal_basisMatrix_eq_inv_transpose` : `B* = 2π • (B⁻¹)ᵀ`.
- `Crystallography.BravaisLattice.det_reciprocal_basisMatrix` : `det B* = (2π)³ / det B`.
- `Crystallography.BravaisLattice.volume_parallelepiped_reciprocal` : the reciprocal primitive
  cell has volume `(2π)³ / |det B|`.
- `Crystallography.BravaisLattice.reciprocal_reciprocal` : the reciprocal of the reciprocal
  lattice is the original lattice.
- `Crystallography.BravaisLattice.inner_reciprocal_latticeVector` :
  `(B* m) ⬝ (B n) = 2π (m ⬝ᵥ n)`.
- `Crystallography.BravaisLattice.mem_lattice_reciprocal_iff` : `G` is a reciprocal lattice
  vector exactly when `G ⬝ R ∈ 2πℤ` for every lattice vector `R`.
- `Crystallography.BravaisLattice.mem_lattice_reciprocal_iff_exp` : the same condition in the
  form `exp (i G ⬝ R) = 1`.
- `Crystallography.BravaisLattice.lattice_reciprocal_relabel` : the reciprocal lattice does not
  depend on the choice of primitive vectors.
- `Crystallography.BravaisLattice.reciprocal_simpleCubic` : the reciprocal of the simple cubic
  lattice of side `a` is the simple cubic lattice of side `2π / a`.
- `Crystallography.BravaisLattice.reciprocal_faceCenteredCubic`,
  `Crystallography.BravaisLattice.reciprocal_bodyCenteredCubic` : fcc of side `a` and bcc of side
  `4π / a` are reciprocal to each other.
- `Crystallography.BravaisLattice.isAddFundamentalDomain_wignerSeitzCell` : the Wigner–Seitz cell
  is a fundamental domain for the lattice translations.
- `Crystallography.BravaisLattice.volume_wignerSeitzCell` : the Wigner–Seitz cell has volume
  `|det B|`.
- `Crystallography.BravaisLattice.volume_firstBrillouinZone` : the first Brillouin zone has volume
  `(2π)³ / |det B|`.

## iii. Table of contents

- A. The reciprocal lattice
- B. Duality, cell volume and the double reciprocal
- C. Reciprocal lattice vectors
- D. Cubic lattices
- E. The Wigner–Seitz cell and the first Brillouin zone

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapter 4 for the Wigner–Seitz primitive cell, and Chapter 5 for the reciprocal lattice: its
  definition by `exp (i K ⬝ R) = 1`, the primitive vectors `b₁ = 2π (a₂ × a₃) / (a₁ ⬝ (a₂ × a₃))`
  and their cyclic permutations, the relation `bᵢ ⬝ aⱼ = 2π δᵢⱼ`, the reciprocal of the reciprocal
  lattice, the volume `(2π)³ / v` of its primitive cell, the reciprocals of the simple cubic, fcc
  and bcc lattices, and the first Brillouin zone as the Wigner–Seitz cell of the reciprocal
  lattice.
* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2005), Chapter 2, for the
  reciprocal lattice vectors in the `2π` convention, Brillouin zones, and the reciprocal lattices
  of the simple cubic, bcc and fcc lattices.

-/

@[expose] public section

open MeasureTheory Real
open scoped Matrix RealInnerProductSpace

namespace Crystallography

/-! ## A. The reciprocal lattice -/

/-- The matrix whose `j`-th column is the cross product `B.col (j + 1) ⨯₃ B.col (j + 2)`, indices
modulo `3`: for the columns `a₁ a₂ a₃` of `B`, its columns are `a₂ ⨯₃ a₃`, `a₃ ⨯₃ a₁` and
`a₁ ⨯₃ a₂`. It is the transpose of the adjugate of `B` (`crossColumns_eq_transpose_adjugate`). -/
def crossColumns (B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (B.col (j + 1) ⨯₃ B.col (j + 2)) i

/-- The `j`-th column of `crossColumns B` is `B.col (j + 1) ⨯₃ B.col (j + 2)`. -/
lemma col_crossColumns (B : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (crossColumns B).col j = B.col (j + 1) ⨯₃ B.col (j + 2) :=
  rfl

/-- The cross products of the columns of `B` form the transposed adjugate of `B`. -/
lemma crossColumns_eq_transpose_adjugate (B : Matrix (Fin 3) (Fin 3) ℝ) :
    crossColumns B = B.adjugateᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossColumns, Matrix.adjugate_fin_three, cross_apply] <;>
    ring

/-- The triple products of the columns of `B`: `aᵢ ⬝ᵥ (a_{j+1} ⨯₃ a_{j+2})` is `det B` for `i = j`
and `0` otherwise, that is `Bᵀ * crossColumns B = det B • 1`. -/
lemma transpose_mul_crossColumns (B : Matrix (Fin 3) (Fin 3) ℝ) :
    Bᵀ * crossColumns B = B.det • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossColumns, Matrix.mul_apply, Fin.sum_univ_three, cross_apply, Matrix.det_fin_three] <;>
    ring

/-- For a nonsingular `B`, the matrix `(2π / det B) • crossColumns B` satisfies
`Bᵀ * ((2π / det B) • crossColumns B) = 2π • 1`. -/
lemma transpose_mul_smul_crossColumns {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.det ≠ 0) :
    Bᵀ * ((2 * π / B.det) • crossColumns B) = (2 * π) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [Matrix.mul_smul, transpose_mul_crossColumns, smul_smul, div_mul_cancel₀ _ hB]

namespace BravaisLattice

/-- The reciprocal lattice, in the physics convention `aᵢ ⬝ bⱼ = 2π δᵢⱼ`. Its basis matrix is
`(2π / V) • crossColumns B` with `V = det B ≠ 0`, so its primitive vectors are
`b₁ = (2π / V) • (a₂ ⨯₃ a₃)`, `b₂ = (2π / V) • (a₃ ⨯₃ a₁)` and `b₃ = (2π / V) • (a₁ ⨯₃ a₂)`. -/
noncomputable def reciprocal (Λ : BravaisLattice) : BravaisLattice where
  basisMatrix := (2 * π / Λ.basisMatrix.det) • crossColumns Λ.basisMatrix
  det_ne_zero := by
    have h := congrArg Matrix.det (transpose_mul_smul_crossColumns Λ.det_ne_zero)
    rw [Matrix.det_mul, Matrix.det_smul (1 : Matrix (Fin 3) (Fin 3) ℝ), Matrix.det_one,
      mul_one] at h
    exact right_ne_zero_of_mul (by rw [h]; positivity)

/-- The basis matrix of the reciprocal lattice is `(2π / det B) • crossColumns B`. -/
lemma reciprocal_basisMatrix (Λ : BravaisLattice) :
    Λ.reciprocal.basisMatrix = (2 * π / Λ.basisMatrix.det) • crossColumns Λ.basisMatrix :=
  rfl

/-- The oriented cell volume is the scalar triple product: `det B = a₁ ⬝ᵥ (a₂ ⨯₃ a₃)`. -/
lemma det_basisMatrix_eq_triple_product (Λ : BravaisLattice) :
    Λ.basisMatrix.det =
      (Λ.primitiveVector 0).ofLp ⬝ᵥ (Λ.primitiveVector 1).ofLp ⨯₃ (Λ.primitiveVector 2).ofLp := by
  rw [triple_product_eq_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i <;> rfl

/-- The cross-product formula for the reciprocal primitive vectors:
`bⱼ = (2π / V) • (a_{j+1} ⨯₃ a_{j+2})` with indices modulo `3` and `V = det B`. -/
lemma reciprocal_primitiveVector (Λ : BravaisLattice) (j : Fin 3) :
    Λ.reciprocal.primitiveVector j = WithLp.toLp 2 ((2 * π / Λ.basisMatrix.det) •
      (Λ.primitiveVector (j + 1)).ofLp ⨯₃ (Λ.primitiveVector (j + 2)).ofLp) :=
  rfl

/-! ## B. Duality, cell volume and the double reciprocal -/

/-- A Bravais lattice is determined by its basis matrix. -/
lemma basisMatrix_injective : Function.Injective basisMatrix := by
  rintro ⟨B, hB⟩ ⟨B', hB'⟩ (rfl : B = B')
  rfl

/-- The inner product of two primitive vectors is an entry of the product of the basis
matrices. -/
private lemma inner_primitiveVector_primitiveVector (Λ Λ' : BravaisLattice) (i j : Fin 3) :
    ⟪Λ.primitiveVector i, Λ'.primitiveVector j⟫ = (Λ.basisMatrixᵀ * Λ'.basisMatrix) i j := by
  simp [primitiveVector, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, dotProduct,
    mul_comm]

/-- Duality in matrix form: `Bᵀ * B* = 2π • 1`. -/
lemma transpose_mul_reciprocal_basisMatrix (Λ : BravaisLattice) :
    Λ.basisMatrixᵀ * Λ.reciprocal.basisMatrix = (2 * π) • (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
  transpose_mul_smul_crossColumns Λ.det_ne_zero

/-- **Duality of the reciprocal basis**: `aᵢ ⬝ bⱼ = 2π δᵢⱼ`. -/
theorem inner_primitiveVector_reciprocal (Λ : BravaisLattice) (i j : Fin 3) :
    ⟪Λ.primitiveVector i, Λ.reciprocal.primitiveVector j⟫ = if i = j then 2 * π else 0 := by
  rw [inner_primitiveVector_primitiveVector, transpose_mul_reciprocal_basisMatrix]
  simp [Matrix.one_apply]

/-- Duality with the factors swapped: `bᵢ ⬝ aⱼ = 2π δᵢⱼ`. -/
lemma inner_reciprocal_primitiveVector (Λ : BravaisLattice) (i j : Fin 3) :
    ⟪Λ.reciprocal.primitiveVector i, Λ.primitiveVector j⟫ = if i = j then 2 * π else 0 := by
  rw [real_inner_comm, inner_primitiveVector_reciprocal]
  exact if_congr eq_comm rfl rfl

/-- The reciprocal basis is the only basis dual to the primitive vectors: `B*` is the only matrix
`M` with `Bᵀ * M = 2π • 1`. -/
lemma reciprocal_basisMatrix_eq_iff (Λ : BravaisLattice) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Λ.reciprocal.basisMatrix = M ↔ Λ.basisMatrixᵀ * M = (2 * π) • 1 := by
  refine ⟨fun h => h ▸ Λ.transpose_mul_reciprocal_basisMatrix, fun h => ?_⟩
  have hT : IsUnit Λ.basisMatrixᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr Λ.det_ne_zero
  calc Λ.reciprocal.basisMatrix
      = Λ.basisMatrixᵀ⁻¹ * (Λ.basisMatrixᵀ * Λ.reciprocal.basisMatrix) :=
        (Matrix.nonsing_inv_mul_cancel_left _ _ hT).symm
    _ = Λ.basisMatrixᵀ⁻¹ * (Λ.basisMatrixᵀ * M) := by
        rw [Λ.transpose_mul_reciprocal_basisMatrix, h]
    _ = M := Matrix.nonsing_inv_mul_cancel_left _ _ hT

/-- The reciprocal basis matrix is `2π` times the inverse transpose: `B* = 2π • (B⁻¹)ᵀ`. -/
lemma reciprocal_basisMatrix_eq_inv_transpose (Λ : BravaisLattice) :
    Λ.reciprocal.basisMatrix = (2 * π) • Λ.basisMatrix⁻¹ᵀ := by
  rw [reciprocal_basisMatrix_eq_iff, Matrix.mul_smul, Matrix.transpose_nonsing_inv,
    Matrix.mul_nonsing_inv]
  rw [Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mpr Λ.det_ne_zero

/-- **The reciprocal cell volume**: the reciprocal basis has oriented volume
`det B* = (2π)³ / det B`. -/
theorem det_reciprocal_basisMatrix (Λ : BravaisLattice) :
    Λ.reciprocal.basisMatrix.det = (2 * π) ^ 3 / Λ.basisMatrix.det := by
  rw [reciprocal_basisMatrix_eq_inv_transpose, Matrix.det_smul, Matrix.det_transpose,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, div_eq_mul_inv]

/-- The reciprocal primitive cell has Lebesgue volume `(2π)³ / |det B|`. -/
theorem volume_parallelepiped_reciprocal (Λ : BravaisLattice) :
    volume (parallelepiped Λ.reciprocal.primitiveVector) =
      ENNReal.ofReal ((2 * π) ^ 3 / |Λ.basisMatrix.det|) := by
  rw [volume_parallelepiped_primitiveVector, det_reciprocal_basisMatrix, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ 3)]

/-- **The reciprocal of the reciprocal lattice is the original lattice**, with the same primitive
vectors. -/
theorem reciprocal_reciprocal (Λ : BravaisLattice) : Λ.reciprocal.reciprocal = Λ := by
  apply basisMatrix_injective
  rw [reciprocal_basisMatrix_eq_iff]
  have h := congrArg Matrix.transpose Λ.transpose_mul_reciprocal_basisMatrix
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul,
    Matrix.transpose_one] at h

/-! ## C. Reciprocal lattice vectors -/

/-- Each primitive vector is a lattice vector. -/
lemma primitiveVector_mem_lattice (Λ : BravaisLattice) (j : Fin 3) :
    Λ.primitiveVector j ∈ Λ.lattice := by
  rw [← coe_basis]
  exact Submodule.subset_span (Set.mem_range_self j)

/-- A reciprocal lattice vector pairs with a primitive vector to `(B* m) ⬝ aⱼ = 2π mⱼ`. -/
lemma inner_reciprocal_latticeVector_primitiveVector (Λ : BravaisLattice) (m : Fin 3 → ℤ)
    (j : Fin 3) :
    ⟪Λ.reciprocal.latticeVector m, Λ.primitiveVector j⟫ = 2 * π * m j := by
  simp [latticeVector_eq_sum, sum_inner, real_inner_smul_left, inner_reciprocal_primitiveVector]
  ring

/-- A reciprocal lattice vector pairs with a lattice vector to an integer multiple of `2π`:
`(B* m) ⬝ (B n) = 2π (m ⬝ᵥ n) = 2π (m₁ n₁ + m₂ n₂ + m₃ n₃)`. -/
lemma inner_reciprocal_latticeVector (Λ : BravaisLattice) (m n : Fin 3 → ℤ) :
    ⟪Λ.reciprocal.latticeVector m, Λ.latticeVector n⟫ = 2 * π * ((m ⬝ᵥ n : ℤ) : ℝ) := by
  simp only [Λ.latticeVector_eq_sum n, coe_basis, inner_sum, real_inner_smul_right,
    inner_reciprocal_latticeVector_primitiveVector, dotProduct, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The reciprocal lattice consists of the wave vectors `G` with `G ⬝ R ∈ 2πℤ` for every lattice
vector `R`.** -/
theorem mem_lattice_reciprocal_iff (Λ : BravaisLattice) (G : EuclideanSpace ℝ (Fin 3)) :
    G ∈ Λ.reciprocal.lattice ↔ ∀ R ∈ Λ.lattice, ∃ k : ℤ, ⟪G, R⟫ = 2 * π * k := by
  constructor
  · intro hG R hR
    obtain ⟨m, rfl⟩ := (Λ.reciprocal.mem_lattice_iff G).mp hG
    obtain ⟨n, rfl⟩ := (Λ.mem_lattice_iff R).mp hR
    exact ⟨m ⬝ᵥ n, Λ.inner_reciprocal_latticeVector m n⟩
  · intro h
    choose k hk using fun j => h _ (Λ.primitiveVector_mem_lattice j)
    refine (Λ.reciprocal.mem_lattice_iff G).mpr
      ⟨k, InnerProductSpace.ext_inner_right_basis Λ.basis fun j => ?_⟩
    rw [coe_basis, hk j, inner_reciprocal_latticeVector_primitiveVector]

/-- **Plane-wave form**: `G` is a reciprocal lattice vector exactly when `exp (i G ⬝ R) = 1` for
every lattice vector `R`, that is when the plane wave `r ↦ exp (i G ⬝ r)` has the periodicity of
the lattice. -/
theorem mem_lattice_reciprocal_iff_exp (Λ : BravaisLattice) (G : EuclideanSpace ℝ (Fin 3)) :
    G ∈ Λ.reciprocal.lattice ↔ ∀ R ∈ Λ.lattice, Complex.exp (⟪G, R⟫ * Complex.I) = 1 := by
  rw [mem_lattice_reciprocal_iff]
  refine forall₂_congr fun R _ => ?_
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [hk]
    push_cast
    ring
  · have h : ((⟪G, R⟫ : ℝ) : ℂ) = ((2 * π * k : ℝ) : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      rw [hk]
      push_cast
      ring
    exact_mod_cast h

/-- The reciprocal lattice depends only on the lattice: relabeling the cells by a unimodular
integer matrix, which changes the primitive vectors but not the lattice, does not change it. -/
lemma lattice_reciprocal_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) :
    (Λ.relabel P hP).reciprocal.lattice = Λ.reciprocal.lattice := by
  ext G
  rw [mem_lattice_reciprocal_iff, mem_lattice_reciprocal_iff, lattice_relabel]

/-! ## D. Cubic lattices -/

/-- The simple cubic lattice of side `a > 0`, with primitive vectors `a e₁`, `a e₂` and `a e₃`. -/
noncomputable def simpleCubic (a : ℝ) (ha : 0 < a) : BravaisLattice where
  basisMatrix := a • 1
  det_ne_zero := by simp [ha.ne']

/-- The face-centered cubic lattice whose conventional cubic cell has side `a > 0`, with primitive
vectors `(a / 2) (0, 1, 1)`, `(a / 2) (1, 0, 1)` and `(a / 2) (1, 1, 0)`. -/
noncomputable def faceCenteredCubic (a : ℝ) (ha : 0 < a) : BravaisLattice where
  basisMatrix := (a / 2) • !![0, 1, 1; 1, 0, 1; 1, 1, 0]
  det_ne_zero := by
    rw [Matrix.det_smul, Matrix.det_fin_three]
    simp [ha.ne']

/-- The body-centered cubic lattice whose conventional cubic cell has side `a > 0`, with primitive
vectors `(a / 2) (-1, 1, 1)`, `(a / 2) (1, -1, 1)` and `(a / 2) (1, 1, -1)`. -/
noncomputable def bodyCenteredCubic (a : ℝ) (ha : 0 < a) : BravaisLattice where
  basisMatrix := (a / 2) • !![-1, 1, 1; 1, -1, 1; 1, 1, -1]
  det_ne_zero := by
    rw [Matrix.det_smul, Matrix.det_fin_three]
    norm_num [ha.ne']

/-- **The reciprocal of the simple cubic lattice of side `a` is the simple cubic lattice of side
`2π / a`.** -/
theorem reciprocal_simpleCubic (a : ℝ) (ha : 0 < a) :
    (simpleCubic a ha).reciprocal = simpleCubic (2 * π / a) (div_pos two_pi_pos ha) := by
  apply basisMatrix_injective
  rw [reciprocal_basisMatrix_eq_iff]
  simp only [simpleCubic, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.one_mul, smul_smul]
  rw [mul_div_cancel₀ _ ha.ne']

/-- **The reciprocal of the face-centered cubic lattice of side `a` is the body-centered cubic
lattice of side `4π / a`.** -/
theorem reciprocal_faceCenteredCubic (a : ℝ) (ha : 0 < a) :
    (faceCenteredCubic a ha).reciprocal =
      bodyCenteredCubic (4 * π / a) (div_pos (by positivity) ha) := by
  apply basisMatrix_injective
  rw [reciprocal_basisMatrix_eq_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [faceCenteredCubic, bodyCenteredCubic, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- **The reciprocal of the body-centered cubic lattice of side `a` is the face-centered cubic
lattice of side `4π / a`.** -/
theorem reciprocal_bodyCenteredCubic (a : ℝ) (ha : 0 < a) :
    (bodyCenteredCubic a ha).reciprocal =
      faceCenteredCubic (4 * π / a) (div_pos (by positivity) ha) := by
  apply basisMatrix_injective
  rw [reciprocal_basisMatrix_eq_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [faceCenteredCubic, bodyCenteredCubic, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-! ## E. The Wigner–Seitz cell and the first Brillouin zone -/

/-- The Wigner–Seitz cell of a Bravais lattice: the closed set of points that are at least as close
to the origin as to any lattice point. -/
def wignerSeitzCell (Λ : BravaisLattice) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ R ∈ Λ.lattice, ‖x‖ ≤ ‖x - R‖}

/-- The Wigner–Seitz cell is closed, as an intersection of closed half-spaces. -/
lemma isClosed_wignerSeitzCell (Λ : BravaisLattice) : IsClosed Λ.wignerSeitzCell := by
  have h : Λ.wignerSeitzCell = ⋂ R ∈ Λ.lattice, {x | ‖x‖ ≤ ‖x - R‖} := by
    ext x
    simp [wignerSeitzCell]
  rw [h]
  exact isClosed_biInter fun R _ =>
    isClosed_le continuous_norm (continuous_id.sub continuous_const).norm

/-- Every point has a nearest lattice point. -/
lemma exists_forall_norm_sub_le (Λ : BravaisLattice) (x : EuclideanSpace ℝ (Fin 3)) :
    ∃ R₀ ∈ Λ.lattice, ∀ R ∈ Λ.lattice, ‖x - R₀‖ ≤ ‖x - R‖ := by
  have hfin : (Metric.closedBall x ‖x‖ ∩ (Λ.lattice : Set (EuclideanSpace ℝ (Fin 3)))).Finite :=
    ZSpan.setFinite_inter Λ.basis Metric.isBounded_closedBall
  obtain ⟨R₀, ⟨hR₀b, hR₀L⟩, hmin⟩ := Set.exists_min_image _ (fun R => ‖x - R‖) hfin
    ⟨0, by simp [Metric.mem_closedBall, dist_eq_norm], Λ.lattice.zero_mem⟩
  refine ⟨R₀, hR₀L, fun R hR => ?_⟩
  by_cases hRb : R ∈ Metric.closedBall x ‖x‖
  · exact hmin R ⟨hRb, hR⟩
  · rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, not_le] at hRb
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm] at hR₀b
    exact hR₀b.trans hRb.le

/-- An affine plane `{x | v ⬝ x = c}` with `v ≠ 0` has Lebesgue measure zero. -/
private lemma volume_setOf_inner_eq {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) (c : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin 3) | ⟪v, x⟫ = c} = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := LinearMap.ker (innerₛₗ ℝ v) with hKdef
  have hK : K ≠ ⊤ := by
    intro h
    have hvK : v ∈ K := h ▸ Submodule.mem_top
    rw [hKdef, LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at hvK
    exact hv hvK
  have hsub : {x | ⟪v, x⟫ = c} ⊆
      (AffineSubspace.mk' ((c / ‖v‖ ^ 2) • v) K : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro x hx
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, hKdef, LinearMap.mem_ker,
      innerₛₗ_apply_apply, inner_sub_right, hx, real_inner_smul_right,
      real_inner_self_eq_norm_sq, div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)),
      sub_self]
  refine measure_mono_null hsub (Measure.addHaar_affineSubspace volume _ fun h => hK ?_)
  rw [← AffineSubspace.direction_mk' ((c / ‖v‖ ^ 2) • v) K, h, AffineSubspace.direction_top]

/-- **The Wigner–Seitz cell is a fundamental domain for the lattice translations**: its translates
by lattice vectors cover space and overlap only in sets of measure zero. -/
theorem isAddFundamentalDomain_wignerSeitzCell (Λ : BravaisLattice) :
    IsAddFundamentalDomain Λ.lattice Λ.wignerSeitzCell volume where
  nullMeasurableSet := Λ.isClosed_wignerSeitzCell.measurableSet.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun x => by
    obtain ⟨R₀, hR₀, hmin⟩ := Λ.exists_forall_norm_sub_le x
    refine ⟨-⟨R₀, hR₀⟩, fun R hR => ?_⟩
    simp only [Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, neg_add_eq_sub, sub_sub]
    exact hmin _ (Λ.lattice.add_mem hR₀ hR)
  aedisjoint := by
    intro g₁ g₂ hne
    have hv : (g₂ : EuclideanSpace ℝ (Fin 3)) - g₁ ≠ 0 :=
      sub_ne_zero.mpr fun h => hne (Subtype.ext h).symm
    refine measure_mono_null (fun x hx => ?_)
      (volume_setOf_inner_eq hv
        ((‖(g₂ : EuclideanSpace ℝ (Fin 3))‖ ^ 2 - ‖(g₁ : EuclideanSpace ℝ (Fin 3))‖ ^ 2) / 2))
    obtain ⟨hx₁, hx₂⟩ := hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx₁ hx₂
    simp only [wignerSeitzCell, Set.mem_ofPred_eq, Submodule.vadd_def, vadd_eq_add,
      Submodule.coe_neg, neg_add_eq_sub] at hx₁ hx₂
    have h₁ := hx₁ _ (sub_mem g₂.2 g₁.2)
    have h₂ := hx₂ _ (sub_mem g₁.2 g₂.2)
    rw [sub_sub, add_sub_cancel] at h₁ h₂
    have heq := congrArg (· ^ 2) (le_antisymm h₁ h₂)
    simp only [norm_sub_sq_real] at heq
    rw [Set.mem_ofPred_eq, inner_sub_left, real_inner_comm x, real_inner_comm x]
    linarith

/-- **The Wigner–Seitz cell has volume `|det B|`**, the volume of a primitive cell. -/
theorem volume_wignerSeitzCell (Λ : BravaisLattice) :
    volume Λ.wignerSeitzCell = ENNReal.ofReal |Λ.basisMatrix.det| := by
  have : MeasurableVAdd Λ.lattice (EuclideanSpace ℝ (Fin 3)) :=
    (inferInstance : MeasurableVAdd Λ.lattice.toAddSubgroup _)
  have : VAddInvariantMeasure Λ.lattice (EuclideanSpace ℝ (Fin 3)) volume :=
    (inferInstance : VAddInvariantMeasure Λ.lattice.toAddSubgroup _ volume)
  rw [Λ.isAddFundamentalDomain_wignerSeitzCell.measure_eq
      (ZSpan.isAddFundamentalDomain Λ.basis volume), volume_fundamentalDomain]

/-- The first Brillouin zone: the Wigner–Seitz cell of the reciprocal lattice. -/
def firstBrillouinZone (Λ : BravaisLattice) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Λ.reciprocal.wignerSeitzCell

/-- The first Brillouin zone is a fundamental domain for the translations by reciprocal lattice
vectors: every wave vector is equivalent modulo the reciprocal lattice to a point of the zone, and
distinct translates of the zone overlap only in sets of measure zero. -/
lemma isAddFundamentalDomain_firstBrillouinZone (Λ : BravaisLattice) :
    IsAddFundamentalDomain Λ.reciprocal.lattice Λ.firstBrillouinZone volume :=
  Λ.reciprocal.isAddFundamentalDomain_wignerSeitzCell

/-- **The first Brillouin zone has volume `(2π)³ / |det B|`**, the volume of a primitive cell of the
reciprocal lattice. -/
theorem volume_firstBrillouinZone (Λ : BravaisLattice) :
    volume Λ.firstBrillouinZone = ENNReal.ofReal ((2 * π) ^ 3 / |Λ.basisMatrix.det|) := by
  rw [firstBrillouinZone, volume_wignerSeitzCell, det_reciprocal_basisMatrix, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ 3)]

end BravaisLattice

end Crystallography
