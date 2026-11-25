/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

namespace MetaMathlibExt

@[expose] public section

open Matrix

private theorem hadamard_sign_matrix_bound (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hcard : 0 < Fintype.card ι)
    (M : Matrix ι ι ℝ)
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    |M.det| ≤ Real.rpow (Fintype.card ι) ((Fintype.card ι : ℝ) / 2) := by
  have hcardR : (0 : ℝ) < (Fintype.card ι : ℕ) := by exact_mod_cast hcard
  have hneR : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := ne_of_gt hcardR
  have hneN : Fintype.card ι ≠ 0 := ne_of_gt hcard
  set G : Matrix ι ι ℝ := M.conjTranspose * M with hG
  have hPSD : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hH : G.IsHermitian := hPSD.isHermitian
  have hev_nn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hPSD.eigenvalues_nonneg i
  have hprod_nn : 0 ≤ ∏ i, hH.eigenvalues i :=
    Finset.prod_nonneg (fun i _ => hev_nn i)
  have hdetG : G.det = ∏ i, hH.eigenvalues i := by
    have h := hH.det_eq_prod_eigenvalues
    simpa using h
  have htrG : G.trace = ∑ i, hH.eigenvalues i := by
    have h := hH.trace_eq_sum_eigenvalues
    simpa using h
  have hdetG2 : G.det = M.det ^ 2 := by
    rw [hG, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, pow_two]
  have htrG2 : G.trace = ((Fintype.card ι : ℕ) : ℝ) * Fintype.card ι := by
    have h1 : ∀ i j : ι, M.conjTranspose i j * M j i = 1 := by
      intro i j
      simp only [Matrix.conjTranspose_apply, star_trivial]
      rcases hM j i with h | h <;> rw [h] <;> norm_num
    simp only [Matrix.trace, Matrix.diag_apply, hG, Matrix.mul_apply, h1,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hAMGM := Real.geom_mean_le_arith_mean_weighted (Finset.univ)
    (fun _ => (((Fintype.card ι : ℕ) : ℝ))⁻¹) (fun i => hH.eigenvalues i)
    (fun i _ => le_of_lt (inv_pos.mpr hcardR))
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hneR])
    (fun i _ => hev_nn i)
  rw [Real.finsetProd_rpow Finset.univ (fun i => hH.eigenvalues i)
    (fun i _ => hev_nn i)] at hAMGM
  have hRHS : (∑ i ∈ (Finset.univ : Finset ι),
      (((Fintype.card ι : ℕ) : ℝ))⁻¹ * hH.eigenvalues i)
      = ((Fintype.card ι : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, ← htrG, htrG2, ← mul_assoc, inv_mul_cancel₀ hneR, one_mul]
  rw [hRHS] at hAMGM
  have hprod_le : (∏ i, hH.eigenvalues i)
      ≤ (((Fintype.card ι : ℕ) : ℝ)) ^ Fintype.card ι := by
    have h1 : (((∏ i, hH.eigenvalues i) ^ ((((Fintype.card ι : ℕ) : ℝ)))⁻¹))
        ^ Fintype.card ι
        ≤ ((((Fintype.card ι : ℕ) : ℝ))) ^ Fintype.card ι :=
      pow_le_pow_left₀ (Real.rpow_nonneg hprod_nn _) hAMGM _
    rwa [Real.rpow_inv_natCast_pow hprod_nn hneN] at h1
  have hsq : (Real.rpow (((Fintype.card ι : ℕ) : ℝ))
      ((((Fintype.card ι : ℕ) : ℝ)) / 2)) ^ 2
      = Real.rpow (((Fintype.card ι : ℕ) : ℝ)) (((Fintype.card ι : ℕ) : ℝ)) := by
    show (((((Fintype.card ι : ℕ) : ℝ)) ^ ((((Fintype.card ι : ℕ) : ℝ)) / 2) : ℝ)) ^ 2
      = (((Fintype.card ι : ℕ) : ℝ)) ^ (((Fintype.card ι : ℕ) : ℝ))
    rw [pow_two, ← Real.rpow_add hcardR]
    congr 1
    ring
  have h1 : ((((Fintype.card ι : ℕ) : ℝ))) ^ Fintype.card ι
      = Real.rpow (((Fintype.card ι : ℕ) : ℝ)) (((Fintype.card ι : ℕ) : ℝ)) :=
    (Real.rpow_natCast _ _).symm
  have hfin : M.det ^ 2
      ≤ (Real.rpow (((Fintype.card ι : ℕ) : ℝ))
        ((((Fintype.card ι : ℕ) : ℝ)) / 2)) ^ 2 := by
    rw [hsq, ← h1, ← hdetG2, hdetG]
    exact hprod_le
  exact abs_le_of_sq_le_sq hfin (Real.rpow_nonneg (le_of_lt hcardR) _)

/-- **Hadamard bound for zero-one determinants.** Let $n \ge 1$ and let $B$ be an $n \times n$
real matrix each of whose entries is $0$ or $1$. Then
$$|\det B| \le 2^{-n} (n+1)^{(n+1)/2}.$$

The bound comes from bordering and signing $2B$ to obtain an $(n+1) \times (n+1)$ matrix with
entries $\pm 1$ whose determinant is $2^n \det B$, and applying Hadamard's determinant inequality.

Proves `Wanted` entry `hadamard_zero_one_determinant_bound`.

Source: Richard P. Brent and Adam B. Yedidia, "Computation of Maximal
Determinants of Binary Circulant Matrices," Journal of Integer Sequences 21
(2018), Article 18.5.6.
Stable source URL: https://cs.uwaterloo.ca/journals/JIS/VOL21/Brent/brent11.tex
Exact statement lines 226–238.
Verified source-file SHA-256:
`c32c1f2e37c9fdaf1f56ccdbc9e257183500bf6ea6f64b819d8245d99cd676fd`.
Verified span SHA-256:
`92528b378d9b23e03d82114f91e804bb0774e4ed36aaa26e51b5f7fc501a5aaa`.
Concept ID: `jis_grounded_381bade9817989f697266d6e`.
-/
theorem hadamard_zero_one_determinant_bound (n : ℕ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hB : ∀ i j, B i j = 0 ∨ B i j = 1) :
    |B.det| ≤ ((2 : ℝ)⁻¹) ^ n *
      Real.rpow ((n : ℝ) + 1) (((n : ℝ) + 1) / 2) := by
  have _ : 0 < n := hn
  set u : Matrix (Fin 1) (Fin n) ℝ := fun _ _ => 1 with hu
  set v : Matrix (Fin n) (Fin 1) ℝ := fun _ _ => -1 with hv
  set C : Matrix (Fin n) (Fin n) ℝ := fun i j => 2 * B i j - 1 with hC
  set M : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) u v C with hMdef
  have hcard : 0 < Fintype.card (Fin 1 ⊕ Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hM1 : ∀ i j, M i j = 1 ∨ M i j = -1 := by
    intro i j
    rcases i with x | i <;> rcases j with y | j
    · left
      rw [hMdef]
      show (1 : Matrix (Fin 1) (Fin 1) ℝ) x y = 1
      simp [Matrix.one_apply, Subsingleton.elim x y]
    · left
      rw [hMdef]
      show u x j = 1
      simp only [hu]
    · right
      rw [hMdef]
      show v i y = -1
      simp only [hv]
    · rcases hB i j with h | h
      · right
        have e : C i j = -1 := by
          rw [hC]
          show 2 * B i j - 1 = -1
          rw [h]
          norm_num
        rw [hMdef]
        show C i j = -1
        exact e
      · left
        have e : C i j = 1 := by
          rw [hC]
          show 2 * B i j - 1 = 1
          rw [h]
          norm_num
        rw [hMdef]
        show C i j = 1
        exact e
  have hvu : ∀ i j, (v * u) i j = -1 := by
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp only [hv, hu, mul_one]
  have hCvu : C - v * u = (2 : ℝ) • B := by
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hvu]
    have hCij : C i j = 2 * B i j - 1 := rfl
    rw [hCij]
    ring
  have hdetM : M.det = (2 : ℝ) ^ n * B.det := by
    have hschur : M.det = (C - v * u).det := by
      rw [hMdef]
      exact Matrix.det_fromBlocks_one₁₁ u v C
    rw [hschur, hCvu, Matrix.det_smul, Fintype.card_fin]
  have hbound := hadamard_sign_matrix_bound (Fin 1 ⊕ Fin n) hcard M hM1
  simp only [Fintype.card_sum, Fintype.card_fin] at hbound
  have hNC : ((((1 + n : ℕ)) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hNC] at hbound
  rw [hdetM, abs_mul] at hbound
  have habs2 : |(2 : ℝ) ^ n| = (2 : ℝ) ^ n := abs_of_nonneg (by positivity)
  rw [habs2] at hbound
  have h2ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [inv_pow]
  calc |B.det| = (((2 : ℝ) ^ n))⁻¹ * (((2 : ℝ) ^ n) * |B.det|) := by
        rw [← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]
    _ ≤ (((2 : ℝ) ^ n))⁻¹ * (Real.rpow ((n : ℝ) + 1) (((n : ℝ) + 1) / 2)) :=
        mul_le_mul_of_nonneg_left hbound
          (le_of_lt (inv_pos.mpr (pow_pos (by norm_num) n)))
end

end MetaMathlibExt
