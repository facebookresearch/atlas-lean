/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Notation

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

private theorem posDef_interior_of_fromBlocks {m p : Type*} (A : Matrix m m ℝ)
    (B : Matrix m p ℝ) (D : Matrix p p ℝ)
    (hG : (fromBlocks A B Bᵀ D).PosDef) : D.PosDef := by
  have h := hG.submatrix (e := Sum.inr) Sum.inr_injective
  rwa [show (fromBlocks A B Bᵀ D).submatrix Sum.inr Sum.inr = D from rfl] at h

private theorem mulVec_one_one (c x : ℝ) : !![c] *ᵥ ![x] = ![c * x] := by
  ext i
  fin_cases i
  simp [Matrix.mulVec]

private theorem dotProduct_one_one (x y : ℝ) : ![x] ⬝ᵥ ![y] = x * y := by
  simp [dotProduct]

/-- **Schur energy identity with a source offset (reconstruction form).** For a symmetric
invertible interior block `D` and interior potentials given by the reconstruction
`φI = D⁻¹ (jI - Bᵀ φP)`, the quadratic form of `G = [[A, B], [Bᵀ, D]]` splits as the Schur
complement form on the ports plus the source term `jIᵀ D⁻¹ jI`. No positivity is assumed. -/
theorem dotProduct_fromBlocks_mulVec_eq_schur_add_source {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ) (D : Matrix p p ℝ)
    [Invertible D] (hD : D.IsSymm) (φP : m → ℝ) (φI jI : p → ℝ)
    (hφI : φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
      φP ⬝ᵥ ((A - B * D⁻¹ * Bᵀ) *ᵥ φP) + jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
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
      φP ⬝ᵥ ((A - B * D⁻¹ * Bᵀ) *ᵥ φP) + jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
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
      φP ⬝ᵥ ((A - B * D⁻¹ * Bᵀ) *ᵥ φP) := by
  have h := dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior A B D hG φP φI 0 hI
  rw [Matrix.mulVec_zero, zero_dotProduct, add_zero] at h
  exact h

/-- **Dissipation interpretation under SPD.** If `G = [[A, B], [Bᵀ, D]]` is positive definite,
both terms of the split are nonnegative: the port term `φPᵀ K φP` and the source term
`jIᵀ D⁻¹ jI`. -/
theorem schur_dotProduct_nonneg_and_source_nonneg_of_posDef {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) (hG : (fromBlocks A B Bᵀ D).PosDef) (φP : m → ℝ) (jI : p → ℝ) :
    0 ≤ φP ⬝ᵥ ((A - B * D⁻¹ * Bᵀ) *ᵥ φP) ∧ 0 ≤ jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
  have hDpd : D.PosDef := posDef_interior_of_fromBlocks A B D hG
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
      φP ⬝ᵥ ((A - B * D⁻¹ * Bᵀ) *ᵥ φP) := by
  have hDpd : D.PosDef := posDef_interior_of_fromBlocks A B D hG
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

/-! ### Validation: singleton port and singleton interior -/

/-- **Singleton port/interior, scalar form.** For scalars `a, b, d` with `d ≠ 0` and
`b φP + d φI = j`, `a φP² + 2 b φP φI + d φI² = (a - b² / d) φP² + j² / d`. -/
theorem singleton_dotProduct_fromBlocks_mulVec (a b d φP φI j : ℝ) (hd : d ≠ 0)
    (hI : b * φP + d * φI = j) :
    (![φP] ⊕ᵥ ![φI]) ⬝ᵥ (fromBlocks !![a] !![b] !![b] !![d] *ᵥ (![φP] ⊕ᵥ ![φI])) =
      (a - b ^ 2 / d) * φP ^ 2 + j ^ 2 / d := by
  have c1 : ((![φP] ⊕ᵥ ![φI]) ∘ Sum.inl) = ![φP] := rfl
  have c2 : ((![φP] ⊕ᵥ ![φI]) ∘ Sum.inr) = ![φI] := rfl
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim, c1, c2]
  simp only [dotProduct_add, mulVec_one_one, dotProduct_one_one]
  subst hI
  field_simp
  ring

/-- **Concrete singleton fixture with a nonzero source.** `A = 2`, `B = -1`, `D = 2`, `φP = 1`,
`jI = 1`, so the interior equation gives `φI = 1`. Then `φᵀ G φ = 2`, the Schur term is `3 / 2`
and the source term is `1 / 2`: the corrected identity holds and the uncorrected one fails. -/
theorem singleton_fixture_values :
    (!![(-1 : ℝ)])ᵀ *ᵥ ![1] + !![(2 : ℝ)] *ᵥ ![1] = ![1] ∧
      (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
          (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) = 2 ∧
      ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)] - !![(-1 : ℝ)] * (!![(2 : ℝ)])⁻¹ * (!![(-1 : ℝ)])ᵀ) *ᵥ
          ![1]) = 3 / 2 ∧
      ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) = 1 / 2 ∧
      (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
          (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) ≠
        ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)] - !![(-1 : ℝ)] * (!![(2 : ℝ)])⁻¹ * (!![(-1 : ℝ)])ᵀ) *ᵥ
          ![1]) := by
  have hT : (!![(-1 : ℝ)])ᵀ = !![-1] := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hinv : (!![(2 : ℝ)])⁻¹ = !![(2⁻¹ : ℝ)] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply]
  have hS : !![(2 : ℝ)] - !![(-1 : ℝ)] * (!![(2 : ℝ)])⁻¹ * (!![(-1 : ℝ)])ᵀ =
      !![(3 / 2 : ℝ)] := by
    rw [hT, hinv]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.sub_apply]
    norm_num
  have h1 : (!![(-1 : ℝ)])ᵀ *ᵥ ![1] + !![(2 : ℝ)] *ᵥ ![1] = ![1] := by
    rw [hT, mulVec_one_one, mulVec_one_one]
    ext i
    fin_cases i
    simp
    norm_num
  have h2 : (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
      (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) = 2 := by
    have c1 : (((![(1 : ℝ)] ⊕ᵥ ![1])) ∘ Sum.inl) = ![1] := rfl
    have c2 : (((![(1 : ℝ)] ⊕ᵥ ![1])) ∘ Sum.inr) = ![1] := rfl
    rw [hT, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim, c1, c2]
    simp only [dotProduct_add, mulVec_one_one, dotProduct_one_one]
    norm_num
  have h3 : ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)] - !![(-1 : ℝ)] * (!![(2 : ℝ)])⁻¹ * (!![(-1 : ℝ)])ᵀ) *ᵥ
      ![1]) = 3 / 2 := by
    rw [hS, mulVec_one_one, dotProduct_one_one]
    norm_num
  have h4 : ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) = 1 / 2 := by
    rw [hinv, mulVec_one_one, dotProduct_one_one]
    norm_num
  exact ⟨h1, h2, h3, h4, by rw [h2, h3]; norm_num⟩

end MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy
