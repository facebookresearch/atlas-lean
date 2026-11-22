/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.UnitCells

/-!
# Tests for `PhyslibExt.CondensedMatter.Crystallography.UnitCells`

* GL(3,Z): the simple cubic lattice and an explicit sheared lattice span the same lattice,
  and the forward direction extracts a unimodular matrix.
* Volume: the left-handed cubic basis has `det = -1` but cell volume `1`, and the sheared
  lattice has the same volume as the simple cubic lattice.
* FCC/BCC: FCC has 4 and BCC has 2 lattice points per conventional cell (quotient counts), with
  explicit basis matrices and volume ratios.
* Wigner-Seitz: covering and disjoint interiors on the simple cubic lattice, and the face
  midpoint `(1/2, 0, 0)` lying in two closed cells.
* Metadata table: entry evaluation, injectivity and the three cubic entries; and a same-system
  lattice inequality between two constructors.
* Countermodel: doubling the cells (`det = 8`, not unimodular) does not preserve the lattice.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Crystallography.UnitCells

open _root_.Crystallography MeasureTheory
open scoped Matrix

/-! ### GL(3,Z) on a concrete pair -/

/-- A shear of the simple cubic cells. -/
def shearGL : Matrix (Fin 3) (Fin 3) ℤ := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

/-- The shear is unimodular. -/
lemma isUnit_det_shearGL : IsUnit shearGL.det := by
  simp [shearGL, Matrix.det_fin_three]

/-- The sheared simple cubic lattice, stated explicitly. -/
noncomputable def shearedCubic : BravaisLattice where
  basisMatrix := (BravaisLattice.simpleCubic 1 one_pos).basisMatrix
    * shearGL.map (Int.cast : ℤ → ℝ)
  det_ne_zero := by
    have h1 : (BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det = 1 := by
      show ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 1
      rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
      norm_num
    have hP : shearGL.det = 1 := by simp [shearGL, Matrix.det_fin_three]
    rw [Matrix.det_mul, ← Int.cast_det, h1, hP]
    simp

/-- The sheared lattice spans the same lattice, by GL(3,Z). -/
lemma lattice_shearedCubic : (BravaisLattice.simpleCubic 1 one_pos).lattice
    = shearedCubic.lattice :=
  (BravaisLattice.lattice_eq_iff_gl _ _).mpr ⟨shearGL, isUnit_det_shearGL, rfl⟩

-- The forward direction extracts a unimodular change-of-basis matrix.
example : ∃ P : Matrix (Fin 3) (Fin 3) ℤ, IsUnit P.det ∧
    shearedCubic.basisMatrix
      = (BravaisLattice.simpleCubic 1 one_pos).basisMatrix * P.map (Int.cast : ℤ → ℝ) :=
  (BravaisLattice.lattice_eq_iff_gl _ _).mp lattice_shearedCubic

/-! ### Volume, including a left-handed basis -/

/-- A left-handed cubic basis (two columns swapped, `det = -1`). -/
noncomputable def leftHandedCubic : BravaisLattice where
  basisMatrix := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  det_ne_zero := by
    have hdet : (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = -1 := by
      simp [Matrix.det_fin_three]
    rw [hdet]
    norm_num

-- The determinant is negative (left-handed).
example : leftHandedCubic.basisMatrix.det = -1 := by
  show (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = -1
  simp [Matrix.det_fin_three]

-- But the cell volume is still 1.
example : volume (parallelepiped leftHandedCubic.primitiveVector) = 1 := by
  rw [BravaisLattice.volume_parallelepiped_primitiveVector]
  have hdet : leftHandedCubic.basisMatrix.det = -1 := by
    show (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = -1
    simp [Matrix.det_fin_three]
  rw [hdet, show |(-1 : ℝ)| = 1 by norm_num, ENNReal.ofReal_one]

-- Volume is preserved under the shear relabeling.
example : volume (parallelepiped shearedCubic.primitiveVector)
    = volume (parallelepiped (BravaisLattice.simpleCubic 1 one_pos).primitiveVector) :=
  BravaisLattice.volume_parallelepiped_eq_of_lattice_eq _ _ lattice_shearedCubic.symm

/-! ### FCC and BCC counts -/

-- FCC has 4 lattice points per conventional cell.
example : BravaisLattice.pointsPerCell (BravaisLattice.simpleCubic 1 one_pos)
    (BravaisLattice.faceCenteredCubic 1 one_pos) = 4 :=
  (BravaisLattice.pointsPerCell_faceCenteredCubic 1 one_pos).1

-- The FCC basis matrices, stated explicitly.
example : (BravaisLattice.faceCenteredCubic 1 one_pos).basisMatrix
    = ((1 : ℝ) / 2) • !![0, 1, 1; 1, 0, 1; 1, 1, 0] := rfl

example : (BravaisLattice.simpleCubic 1 one_pos).basisMatrix
    = ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := rfl

-- BCC has 2 lattice points per conventional cell.
example : BravaisLattice.pointsPerCell (BravaisLattice.simpleCubic 1 one_pos)
    (BravaisLattice.bodyCenteredCubic 1 one_pos) = 2 :=
  (BravaisLattice.pointsPerCell_bodyCenteredCubic 1 one_pos).1

-- The volume ratios.
example : |(BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det|
    / |(BravaisLattice.faceCenteredCubic 1 one_pos).basisMatrix.det| = 4 :=
  (BravaisLattice.pointsPerCell_faceCenteredCubic 1 one_pos).2.2

example : |(BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det|
    / |(BravaisLattice.bodyCenteredCubic 1 one_pos).basisMatrix.det| = 2 :=
  (BravaisLattice.pointsPerCell_bodyCenteredCubic 1 one_pos).2.2

/-! ### Wigner-Seitz covering and disjointness -/

/-- The corner of the simple cubic cell. -/
noncomputable def cornerHalf : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1 / 2, 1 / 2, 1 / 2]

-- Covering: the corner is equivalent to a Wigner-Seitz point.
example : ∃ R ∈ (BravaisLattice.simpleCubic 1 one_pos).lattice,
    cornerHalf - R ∈ (BravaisLattice.simpleCubic 1 one_pos).wignerSeitzCell :=
  BravaisLattice.wignerSeitzCell_cover _ cornerHalf

-- Disjointness: interiors of the central cell and the e₀-translate are disjoint.
example : Disjoint
    (interior ((fun x => (0 : EuclideanSpace ℝ (Fin 3)) + x) ''
      (BravaisLattice.simpleCubic 1 one_pos).wignerSeitzCell))
    (interior ((fun x => (BravaisLattice.simpleCubic 1 one_pos).primitiveVector 0 + x) ''
      (BravaisLattice.simpleCubic 1 one_pos).wignerSeitzCell)) := by
  apply BravaisLattice.wignerSeitzCell_disjoint_interior_translate _ _ _ ?_ ?_ ?_
  · exact (BravaisLattice.simpleCubic 1 one_pos).lattice.zero_mem
  · exact BravaisLattice.primitiveVector_mem_lattice _ _
  · have hne : (BravaisLattice.simpleCubic 1 one_pos).primitiveVector 0 ≠ 0 :=
      LinearIndependent.ne_zero 0
        (BravaisLattice.simpleCubic 1 one_pos).linearIndependent_primitiveVector
    exact Ne.symm hne

-- Closed cells can overlap.
example : ∃ x R₁ R₂ : EuclideanSpace ℝ (Fin 3),
    R₁ ∈ (BravaisLattice.simpleCubic 1 one_pos).lattice ∧
    R₂ ∈ (BravaisLattice.simpleCubic 1 one_pos).lattice ∧ R₁ ≠ R₂ ∧
    x ∈ (fun y => R₁ + y) '' (BravaisLattice.simpleCubic 1 one_pos).wignerSeitzCell ∧
    x ∈ (fun y => R₂ + y) '' (BravaisLattice.simpleCubic 1 one_pos).wignerSeitzCell :=
  BravaisLattice.wignerSeitzCell_exists_overlap _

/-! ### A boundary point in two closed cells -/

/-- The face midpoint of the simple cubic cell. -/
noncomputable def faceMid : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1 / 2, 0, 0]

/-- The face midpoint has norm at most `1 / 2`. -/
lemma norm_faceMid : ‖faceMid‖ ≤ 1 / 2 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    EuclideanSpace.norm_sq_eq]
  simp [faceMid, Fin.sum_univ_three, Real.norm_eq_abs]

/-- The face midpoint lies in the central Wigner-Seitz cell. -/
lemma faceMid_mem (ha : 0 < (1 : ℝ)) :
    faceMid ∈ (BravaisLattice.simpleCubic 1 ha).wignerSeitzCell := by
  intro R hR
  obtain ⟨n, rfl⟩ := ((BravaisLattice.simpleCubic 1 ha).mem_lattice_iff R).mp hR
  have hle : ‖(faceMid - (BravaisLattice.simpleCubic 1 ha).latticeVector n).ofLp 0‖
      ≤ ‖faceMid - (BravaisLattice.simpleCubic 1 ha).latticeVector n‖ :=
    PiLp.norm_apply_le _ 0
  have hval : (faceMid - (BravaisLattice.simpleCubic 1 ha).latticeVector n).ofLp 0
      = 1 / 2 - ((n 0 : ℤ) : ℝ) := by
    simp [faceMid, BravaisLattice.latticeVector_apply, BravaisLattice.simpleCubic,
      Matrix.one_mulVec, one_smul, ← WithLp.toLp_sub, WithLp.ofLp_toLp, Pi.sub_apply,
      Matrix.vecHead, Matrix.vecTail]
  rw [hval, Real.norm_eq_abs] at hle
  have habs : (1 : ℝ) / 2 ≤ |1 / 2 - ((n 0 : ℤ) : ℝ)| := by
    have hsplit : n 0 ≤ 0 ∨ 1 ≤ n 0 := by omega
    rcases hsplit with h | h
    · have h0 : (((n 0 : ℤ)) : ℝ) ≤ 0 := by
        simpa using (Int.cast_le (R := ℝ)).mpr h
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - ((n 0 : ℤ) : ℝ))]
      linarith
    · have h1 : (1 : ℝ) ≤ ((n 0 : ℤ) : ℝ) := by exact_mod_cast h
      rw [abs_of_neg (by linarith : (1 : ℝ) / 2 - ((n 0 : ℤ) : ℝ) < 0)]
      linarith
  linarith [norm_faceMid]

/-- The face midpoint also lies in the e₀-translate of the cell. -/
lemma faceMid_mem_translate (ha : 0 < (1 : ℝ)) :
    faceMid ∈ (fun y => (BravaisLattice.simpleCubic 1 ha).primitiveVector 0 + y) ''
      (BravaisLattice.simpleCubic 1 ha).wignerSeitzCell := by
  have h0 : (BravaisLattice.simpleCubic 1 ha).primitiveVector 0 + -faceMid = faceMid := by
    have h1 : WithLp.toLp 2
          (((BravaisLattice.simpleCubic 1 ha).primitiveVector 0 + -faceMid).ofLp)
        = WithLp.toLp 2 (faceMid.ofLp) := by
      congr 1
      ext i
      fin_cases i <;>
        simp [BravaisLattice.primitiveVector, BravaisLattice.simpleCubic, faceMid,
          ← sub_eq_add_neg, ← WithLp.toLp_sub, WithLp.ofLp_toLp, Pi.sub_apply,
          Matrix.col_apply, Matrix.one_apply, one_smul, Matrix.vecHead,
          Matrix.vecTail] <;>
        norm_num
    rwa [WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h1
  exact ⟨-faceMid, (BravaisLattice.wignerSeitzCell_neg_mem _ _).mpr (faceMid_mem ha), h0⟩

/-! ### The 14-entry metadata table -/

-- Entry 0 is cubic P.
example : bravaisMetadataTable 0 = ⟨"cP", .cubic, .primitive⟩ := rfl

-- The entries are pairwise distinct.
example : Function.Injective bravaisMetadataTable := bravaisMetadataTable_injective

-- Three cubic entries.
example : (Finset.univ.filter (fun i => (bravaisMetadataTable i).system = .cubic)).card = 3 := by
  decide

-- A same-system inequality, applied.
example : (BravaisLattice.tetragonalP 1 2 one_pos (by norm_num)).lattice
    ≠ (BravaisLattice.tetragonalI 1 2 one_pos (by norm_num)).lattice :=
  BravaisLattice.lattice_ne_tP_tI 1 2 one_pos (by norm_num)

/-! ### Countermodel: a non-unimodular change of basis -/

/-- Doubling the cells: not unimodular. -/
def doubleCells : Matrix (Fin 3) (Fin 3) ℤ := 2 • 1

/-- The doubling has determinant 8. -/
lemma det_doubleCells : doubleCells.det = 8 := by
  show ((2 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ)).det = 8
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  norm_num

/-- The doubled simple cubic lattice. -/
noncomputable def doubledCubic : BravaisLattice where
  basisMatrix := (BravaisLattice.simpleCubic 1 one_pos).basisMatrix
    * doubleCells.map (Int.cast : ℤ → ℝ)
  det_ne_zero := by
    have h1 : (BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det = 1 := by
      show ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 1
      rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
      norm_num
    rw [Matrix.det_mul, ← Int.cast_det, h1, det_doubleCells]
    norm_num

-- A non-unimodular change of basis does NOT preserve the lattice.
example : (BravaisLattice.simpleCubic 1 one_pos).lattice ≠ doubledCubic.lattice := by
  intro heq
  obtain ⟨P, hP, hB⟩ := (BravaisLattice.lattice_eq_iff_gl _ _).mp heq
  have h1 : (BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det = 1 := by
    show ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 1
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    norm_num
  have h2 : doubledCubic.basisMatrix.det
      = (BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det * ((8 : ℤ) : ℝ) := by
    show ((BravaisLattice.simpleCubic 1 one_pos).basisMatrix
      * doubleCells.map (Int.cast : ℤ → ℝ)).det = _
    rw [Matrix.det_mul, ← Int.cast_det, det_doubleCells]
  have h3 : doubledCubic.basisMatrix.det
      = (BravaisLattice.simpleCubic 1 one_pos).basisMatrix.det * (P.det : ℝ) := by
    rw [hB, Matrix.det_mul, ← Int.cast_det]
  rw [h1] at h2 h3
  have hdet : ((8 : ℤ) : ℝ) = (P.det : ℝ) := by
    have hmul : (1 : ℝ) * ((8 : ℤ) : ℝ) = 1 * (P.det : ℝ) := by
      rw [← h2, ← h3]
    exact mul_left_cancel₀ one_ne_zero hmul
  have h8 : (8 : ℤ) = P.det := Int.cast_injective hdet
  rw [← h8, Int.isUnit_iff] at hP
  omega

end PhyslibExtTest.CondensedMatter.Crystallography.UnitCells
