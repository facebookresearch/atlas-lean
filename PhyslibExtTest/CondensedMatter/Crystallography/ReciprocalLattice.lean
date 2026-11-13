/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.ReciprocalLattice

/-!
# Tests for `PhyslibExt.CondensedMatter.Crystallography.ReciprocalLattice`

* Cross-product formula: the cyclic indices give `b₃ = (2π / V) • (a₁ ⨯₃ a₂)` for every Bravais
  lattice, and for the simple cubic lattice of side `1` they give `b₁ = 2π e₁`.
* Simple cubic: the reciprocal basis matrix of the simple cubic lattice of side `1` is `2π • 1`,
  the duality relations hold, and the reciprocal cell has volume `(2π)³`. For side `a`, the
  Wigner–Seitz cell has volume `a³` and the first Brillouin zone has volume `(2π / a)³`.
* fcc and bcc: at `a = 2` the reciprocal basis matrix of the fcc lattice is
  `π • !![-1, 1, 1; 1, -1, 1; 1, 1, -1]`, the fcc primitive cell has volume `a³ / 4 = 2` and the
  reciprocal one `(2π)³ / 2`; composing `reciprocal_faceCenteredCubic` and
  `reciprocal_bodyCenteredCubic` returns the fcc lattice of side `a`, as `reciprocal_reciprocal`
  predicts.
* `G₁₁₁` for side `1`: `G = 2π (1, 1, 1)`, `‖G‖ = 2π √3`, `2π / ‖G‖ = 1 / √3`, and
  `G ⬝ R = 2π (n₁ + n₂ + n₃)` for the lattice vector `R` with cell index `n`.
* Membership for side `1`: `2π e₁` is a reciprocal lattice vector and `π e₁` is not, since
  `exp (i π) = -1`. The first Brillouin zone is not all of space: it does not contain `2π e₁`.
* A shear relabeling of the cells changes the reciprocal primitive vectors but not the reciprocal
  lattice.
* Singular bases are excluded by type: no Bravais lattice has the coplanar primitive vectors
  `e₁, e₂, e₁ + e₂`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Crystallography.ReciprocalLattice

open _root_.Crystallography _root_.Crystallography.BravaisLattice MeasureTheory Real
open scoped Matrix RealInnerProductSpace

/-! ### The cross-product formula -/

-- The indices are taken modulo `3`: `b₃ = (2π / V) • (a₁ ⨯₃ a₂)`.
example (Λ : BravaisLattice) :
    Λ.reciprocal.primitiveVector 2 = WithLp.toLp 2 ((2 * π / Λ.basisMatrix.det) •
      (Λ.primitiveVector 0).ofLp ⨯₃ (Λ.primitiveVector 1).ofLp) :=
  Λ.reciprocal_primitiveVector 2

/-- The simple cubic lattice of side `1`. -/
noncomputable abbrev simpleCubicOne : BravaisLattice := simpleCubic 1 one_pos

/-- The simple cubic lattice of side `1` has `det B = 1`. -/
lemma det_simpleCubicOne : simpleCubicOne.basisMatrix.det = 1 := by
  simp [simpleCubic]

-- For side `1`: `b₁ = (2π / 1) • (e₂ ⨯₃ e₃) = 2π e₁`.
example : (simpleCubicOne.reciprocal.primitiveVector 0).ofLp = ![2 * π, 0, 0] := by
  rw [reciprocal_primitiveVector, det_simpleCubicOne]
  ext i
  fin_cases i <;>
    simp [simpleCubic, BravaisLattice.primitiveVector, cross_apply]

/-! ### Simple cubic lattices -/

-- The reciprocal of the simple cubic lattice of side `1` has basis matrix `2π • 1`.
example : simpleCubicOne.reciprocal.basisMatrix = (2 * π) • 1 := by
  rw [reciprocal_simpleCubic]
  simp [simpleCubic]

-- Duality, diagonal case: `a₁ ⬝ b₁ = 2π`.
example :
    ⟪simpleCubicOne.primitiveVector 0, simpleCubicOne.reciprocal.primitiveVector 0⟫ = 2 * π := by
  simpa using inner_primitiveVector_reciprocal simpleCubicOne 0 0

-- Duality, off-diagonal case: `a₁ ⬝ b₂ = 0`.
example : ⟪simpleCubicOne.primitiveVector 0, simpleCubicOne.reciprocal.primitiveVector 1⟫ = 0 := by
  simpa using inner_primitiveVector_reciprocal simpleCubicOne 0 1

-- The reciprocal primitive cell for side `1` has volume `(2π)³`.
example : volume (parallelepiped simpleCubicOne.reciprocal.primitiveVector) =
    ENNReal.ofReal ((2 * π) ^ 3) := by
  rw [volume_parallelepiped_reciprocal, det_simpleCubicOne, abs_one, div_one]

/-- The simple cubic lattice of side `a` has `|det B| = a³`. -/
lemma abs_det_simpleCubic (a : ℝ) (ha : 0 < a) : |(simpleCubic a ha).basisMatrix.det| = a ^ 3 := by
  simp [simpleCubic, abs_of_pos ha]

-- The Wigner–Seitz cell of the simple cubic lattice of side `a` has volume `a³`.
example (a : ℝ) (ha : 0 < a) :
    volume (simpleCubic a ha).wignerSeitzCell = ENNReal.ofReal (a ^ 3) := by
  rw [volume_wignerSeitzCell, abs_det_simpleCubic]

-- The first Brillouin zone of the simple cubic lattice of side `a` has volume `(2π / a)³`.
example (a : ℝ) (ha : 0 < a) :
    volume (simpleCubic a ha).firstBrillouinZone = ENNReal.ofReal ((2 * π / a) ^ 3) := by
  rw [volume_firstBrillouinZone, abs_det_simpleCubic, div_pow]

/-! ### Face-centered and body-centered cubic lattices -/

-- At `a = 2` the reciprocal primitive vectors of the fcc lattice are `π (-1, 1, 1)`,
-- `π (1, -1, 1)` and `π (1, 1, -1)`.
example : (faceCenteredCubic 2 two_pos).reciprocal.basisMatrix =
    π • !![-1, 1, 1; 1, -1, 1; 1, 1, -1] := by
  rw [reciprocal_faceCenteredCubic]
  simp only [bodyCenteredCubic]
  congr 1
  ring

/-- The fcc primitive cell at `a = 2` has oriented volume `a³ / 4 = 2`. -/
lemma det_faceCenteredCubic_two : (faceCenteredCubic 2 two_pos).basisMatrix.det = 2 := by
  simp [faceCenteredCubic, Matrix.det_fin_three]
  norm_num

-- The reciprocal of the fcc lattice at `a = 2` has oriented cell volume `(2π)³ / 2`.
example : (faceCenteredCubic 2 two_pos).reciprocal.basisMatrix.det = (2 * π) ^ 3 / 2 := by
  rw [det_reciprocal_basisMatrix, det_faceCenteredCubic_two]

-- Composing the fcc and bcc results returns the fcc lattice, as `reciprocal_reciprocal` predicts.
example (a : ℝ) (ha : 0 < a) :
    ((faceCenteredCubic a ha).reciprocal).reciprocal = faceCenteredCubic a ha := by
  rw [reciprocal_faceCenteredCubic, reciprocal_bodyCenteredCubic]
  apply basisMatrix_injective
  simp only [faceCenteredCubic]
  congr 2
  field_simp

/-! ### The reciprocal lattice vector `G₁₁₁` for side `1` -/

/-- `G₁₁₁ = 2π (1, 1, 1)` for the simple cubic lattice of side `1`. -/
lemma latticeVector_reciprocal_simpleCubicOne_111 :
    simpleCubicOne.reciprocal.latticeVector ![1, 1, 1] = WithLp.toLp 2 ![2 * π, 2 * π, 2 * π] := by
  rw [reciprocal_simpleCubic, latticeVector_apply]
  congr 1
  ext i
  fin_cases i <;> simp [simpleCubic, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `‖G₁₁₁‖ = 2π √3`. -/
lemma norm_G111 : ‖(WithLp.toLp 2 ![2 * π, 2 * π, 2 * π] : EuclideanSpace ℝ (Fin 3))‖ =
    2 * π * √3 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  rw [show (2 * π) ^ 2 + (2 * π) ^ 2 + (2 * π) ^ 2 = (2 * π) ^ 2 * 3 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

-- `2π / ‖G₁₁₁‖ = 1 / √3`, the `(111)` spacing `a / √3` for side `a = 1`.
example : 2 * π / ‖(WithLp.toLp 2 ![2 * π, 2 * π, 2 * π] : EuclideanSpace ℝ (Fin 3))‖ =
    1 / √3 := by
  rw [norm_G111]
  field_simp

-- `G₁₁₁ ⬝ R = 2π (n₁ + n₂ + n₃)` for the lattice vector `R` with cell index `n`.
example (n : Fin 3 → ℤ) :
    ⟪simpleCubicOne.reciprocal.latticeVector ![1, 1, 1], simpleCubicOne.latticeVector n⟫ =
      2 * π * ((n 0 + n 1 + n 2 : ℤ) : ℝ) := by
  rw [inner_reciprocal_latticeVector]
  simp [dotProduct, Fin.sum_univ_three]

/-! ### Membership in the reciprocal lattice and the first Brillouin zone -/

/-- `2π e₁` is a reciprocal lattice vector of the simple cubic lattice of side `1`. -/
lemma mem_simpleCubicOne_reciprocal : (WithLp.toLp 2 ![2 * π, 0, 0] : EuclideanSpace ℝ (Fin 3)) ∈
    simpleCubicOne.reciprocal.lattice := by
  rw [mem_lattice_iff]
  refine ⟨![1, 0, 0], ?_⟩
  rw [reciprocal_simpleCubic, latticeVector_apply]
  congr 1
  ext i
  fin_cases i <;> simp [simpleCubic, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- `π e₁` is not a reciprocal lattice vector for side `1`: `exp (i π e₁ ⬝ e₁) = -1 ≠ 1`.
example : (WithLp.toLp 2 ![π, 0, 0] : EuclideanSpace ℝ (Fin 3)) ∉
    simpleCubicOne.reciprocal.lattice := by
  rw [mem_lattice_reciprocal_iff_exp]
  intro h
  have h1 := h _ (simpleCubicOne.primitiveVector_mem_lattice 0)
  have hinner : ⟪(WithLp.toLp 2 ![π, 0, 0] : EuclideanSpace ℝ (Fin 3)),
      simpleCubicOne.primitiveVector 0⟫ = π := by
    simp [simpleCubic, BravaisLattice.primitiveVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three]
  rw [hinner, Complex.exp_pi_mul_I] at h1
  norm_num at h1

-- The first Brillouin zone for side `1` is not all of space: it does not contain `2π e₁`.
example : (WithLp.toLp 2 ![2 * π, 0, 0] : EuclideanSpace ℝ (Fin 3)) ∉
    simpleCubicOne.firstBrillouinZone := by
  intro h
  have h1 := h _ mem_simpleCubicOne_reciprocal
  rw [sub_self, norm_zero, norm_le_zero_iff] at h1
  have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h1
  simp [pi_pos.ne'] at h2

/-! ### A change of primitive vectors -/

/-- A shear of the cells: the second primitive vector becomes `e₁ + e₂`. -/
def shearCells : Matrix (Fin 3) (Fin 3) ℤ := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

/-- The shear is unimodular. -/
lemma isUnit_det_shearCells : IsUnit shearCells.det := by
  simp [shearCells, Matrix.det_fin_three]

/-- After the shear, the reciprocal primitive vectors are `2π (e₁ - e₂)`, `2π e₂` and `2π e₃`. -/
lemma reciprocal_relabel_shearCells :
    (simpleCubicOne.relabel shearCells isUnit_det_shearCells).reciprocal.basisMatrix =
      (2 * π) • !![1, 0, 0; -1, 1, 0; 0, 0, 1] := by
  rw [reciprocal_basisMatrix_eq_iff, relabel_basisMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [simpleCubic, shearCells, Matrix.mul_apply, Fin.sum_univ_three]

-- The shear changes the reciprocal primitive vectors ...
example : (simpleCubicOne.relabel shearCells isUnit_det_shearCells).reciprocal.basisMatrix ≠
    simpleCubicOne.reciprocal.basisMatrix := by
  rw [reciprocal_relabel_shearCells, reciprocal_simpleCubic]
  intro h
  have h10 := congrFun (congrFun h 1) 0
  simp [simpleCubic, pi_pos.ne'] at h10

-- ... but not the reciprocal lattice.
example : (simpleCubicOne.relabel shearCells isUnit_det_shearCells).reciprocal.lattice =
    simpleCubicOne.reciprocal.lattice :=
  lattice_reciprocal_relabel _ _ _

/-! ### Singular bases are excluded -/

-- No Bravais lattice has the coplanar primitive vectors `e₁, e₂, e₁ + e₂`: their basis matrix
-- has determinant `0`, so the reciprocal construction never meets a singular basis.
example : ¬ ∃ Λ : BravaisLattice, Λ.basisMatrix = !![1, 0, 1; 0, 1, 1; 0, 0, 0] := by
  rintro ⟨Λ, hΛ⟩
  have h := Λ.det_ne_zero
  rw [hΛ, Matrix.det_fin_three] at h
  simp at h

end PhyslibExtTest.CondensedMatter.Crystallography.ReciprocalLattice
