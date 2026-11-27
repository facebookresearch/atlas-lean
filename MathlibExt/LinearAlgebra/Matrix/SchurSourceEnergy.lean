/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur source energy

For symmetric block equations with an interior source, the
quadratic form `phi^T G phi` splits into the Schur-complement
port energy plus the interior source term. Under positive
definiteness both terms are nonnegative; omitting the source
term is refuted by an explicit fixture.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy

/-- **Schur energy identity with a source offset (reconstruction form).** For a symmetric
invertible interior block `D` and interior potentials given by the reconstruction
`φI = D⁻¹ (jI - Bᵀ φP)`, the quadratic form of `G = [[A, B], [Bᵀ, D]]` splits as the Schur
complement form on the ports plus the source term `jIᵀ D⁻¹ jI`. No positivity is assumed. -/
theorem dotProduct_fromBlocks_mulVec_eq_schur_add_source {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ) (D : Matrix p p ℝ)
    [Invertible D] (hD : D.IsSymm) (φP : m → ℝ) (φI jI : p → ℝ)
    (hφI : φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
      φP ⬝ᵥ ((SchurStrictPositivity.schurComplement A B D) *ᵥ φP) + jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
  unfold SchurStrictPositivity.schurComplement
  subst hφI
  have hDinvT : D⁻¹ᵀ = D⁻¹ := by rw [Matrix.transpose_nonsing_inv, hD.eq]
  have hDD : ∀ v : p → ℝ, D *ᵥ (D⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have symm_move : ∀ s t : p → ℝ, (D⁻¹ *ᵥ s) ⬝ᵥ t = s ⬝ᵥ (D⁻¹ *ᵥ t) := fun s t => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hDinvT,
      dotProduct_comm]
  have transp_move : ∀ y : p → ℝ, φP ⬝ᵥ (B *ᵥ y) = (Bᵀ *ᵥ φP) ⬝ᵥ y := fun y => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hBeq : Bᵀ *ᵥ φP + (jI - Bᵀ *ᵥ φP) = jI := by abel
  have c1 : ((φP ⊕ᵥ (D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP))) ∘ Sum.inl) = φP := rfl
  have c2 : ((φP ⊕ᵥ (D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP))) ∘ Sum.inr) = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP) := rfl
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim, c1, c2]
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_sub, transp_move]
  rw [hDD, hBeq, dotProduct_add, symm_move, sub_dotProduct, transp_move,
    Matrix.mulVec_sub, dotProduct_sub]
  ring

/-- **Schur energy identity with a source offset (block-equation form, headline).** For a
symmetric block matrix `G = [[A, B], [Bᵀ, D]]` with invertible interior block `D`, if the
potentials satisfy the interior block equation `Bᵀ φP + D φI = jI`, then
`φᵀ G φ = φPᵀ K φP + jIᵀ D⁻¹ jI` with `K = A - B D⁻¹ Bᵀ`. The source term is retained. -/
theorem dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior {m p : Type*}
    [Fintype m] [Fintype p] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) [Invertible D] (hG : (fromBlocks A B Bᵀ D).IsSymm) (φP : m → ℝ)
    (φI jI : p → ℝ) (hI : Bᵀ *ᵥ φP + D *ᵥ φI = jI) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
      φP ⬝ᵥ ((SchurStrictPositivity.schurComplement A B D) *ᵥ φP) + jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
  unfold SchurStrictPositivity.schurComplement
  have hD : D.IsSymm := by
    show Dᵀ = D
    ext i j
    have h2 := congrArg (fun X : Matrix (m ⊕ p) (m ⊕ p) ℝ => X (Sum.inr j) (Sum.inr i)) hG.eq
    simpa [Matrix.transpose_apply, Matrix.fromBlocks_apply₂₂] using h2.symm
  have hDφ : D *ᵥ φI = jI - Bᵀ *ᵥ φP := by rw [← hI]; abel
  have h1 : D⁻¹ *ᵥ (D *ᵥ φI) = φI := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hφI : φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP) := by rw [← hDφ, h1]
  exact dotProduct_fromBlocks_mulVec_eq_schur_add_source A B D hD φP φI jI hφI

/-- **Source-free case.** With zero interior injection (`Bᵀ φP + D φI = 0`), the quadratic form
of `G` equals the Schur complement form on the ports. -/
theorem dotProduct_fromBlocks_mulVec_eq_schur_of_interior_zero {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ) (D : Matrix p p ℝ)
    [Invertible D] (hG : (fromBlocks A B Bᵀ D).IsSymm) (φP : m → ℝ) (φI : p → ℝ)
    (hI : Bᵀ *ᵥ φP + D *ᵥ φI = 0) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
      φP ⬝ᵥ ((SchurStrictPositivity.schurComplement A B D) *ᵥ φP) := by
  unfold SchurStrictPositivity.schurComplement
  have h := dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior A B D hG φP φI 0 hI
  rw [Matrix.mulVec_zero, zero_dotProduct, add_zero] at h
  exact h

/-- **Dissipation interpretation under SPD.** If `G = [[A, B], [Bᵀ, D]]` is positive definite,
both terms of the split are nonnegative: the port term `φPᵀ K φP` and the source term
`jIᵀ D⁻¹ jI`. -/
theorem schur_dotProduct_nonneg_and_source_nonneg_of_posDef {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) (hG : (fromBlocks A B Bᵀ D).PosDef) (φP : m → ℝ) (jI : p → ℝ) :
    0 ≤ φP ⬝ᵥ ((SchurStrictPositivity.schurComplement A B D) *ᵥ φP) ∧ 0 ≤ jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
  have hDpd : D.PosDef := SchurStrictPositivity.interior_posDef hG
  have hInv : Invertible D := hDpd.isUnit.invertible
  have hGsymm : (fromBlocks A B Bᵀ D).IsSymm := by
    have hH : (fromBlocks A B Bᵀ D)ᴴ = (fromBlocks A B Bᵀ D) := hG.isHermitian
    show (fromBlocks A B Bᵀ D)ᵀ = (fromBlocks A B Bᵀ D)
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hH
  have hDD : ∀ v : p → ℝ, D *ᵥ (D⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · have hI0 : Bᵀ *ᵥ φP + D *ᵥ (D⁻¹ *ᵥ (-(Bᵀ *ᵥ φP))) = 0 := by
      rw [hDD, add_neg_cancel]
    have hid := dotProduct_fromBlocks_mulVec_eq_schur_of_interior_zero A B D hGsymm φP _
      hI0
    rw [← hid]
    have h := hG.posSemidef.dotProduct_mulVec_nonneg (φP ⊕ᵥ (D⁻¹ *ᵥ (-(Bᵀ *ᵥ φP))))
    simpa using h
  · have h := (Matrix.PosDef.inv hDpd).posSemidef.dotProduct_mulVec_nonneg jI
    simpa using h

/-- **Nonzero sources refute the uncorrected identity.** If `G` is positive definite and the
interior injection `jI = Bᵀ φP + D φI` is nonzero, then `φᵀ G φ ≠ φPᵀ K φP`: the source term is
strictly positive and cannot be dropped. -/
theorem dotProduct_fromBlocks_mulVec_ne_schur_of_source_ne_zero {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) (hG : (fromBlocks A B Bᵀ D).PosDef) (φP : m → ℝ) (φI : p → ℝ)
    (hj : Bᵀ *ᵥ φP + D *ᵥ φI ≠ 0) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) ≠
      φP ⬝ᵥ ((SchurStrictPositivity.schurComplement A B D) *ᵥ φP) := by
  unfold SchurStrictPositivity.schurComplement
  have hDpd : D.PosDef := SchurStrictPositivity.interior_posDef hG
  have hInv : Invertible D := hDpd.isUnit.invertible
  have hGsymm : (fromBlocks A B Bᵀ D).IsSymm := by
    have hH : (fromBlocks A B Bᵀ D)ᴴ = (fromBlocks A B Bᵀ D) := hG.isHermitian
    show (fromBlocks A B Bᵀ D)ᵀ = (fromBlocks A B Bᵀ D)
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hH
  have hid := dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior A B D hGsymm φP φI
    (Bᵀ *ᵥ φP + D *ᵥ φI) rfl
  have hpos : 0 < (Bᵀ *ᵥ φP + D *ᵥ φI) ⬝ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ φP + D *ᵥ φI)) := by
    have h := (Matrix.PosDef.inv hDpd).dotProduct_mulVec_pos hj
    simpa using h
  rw [hid]
  exact ne_of_gt (lt_add_of_pos_right _ hpos)

end MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy
