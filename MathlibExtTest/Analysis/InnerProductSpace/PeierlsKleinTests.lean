/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.PeierlsKlein

public import Mathlib.Analysis.Matrix.Hermitian

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Peierls and Klein inequalities

* Peierls for the zero operator (equality, both sides `0`).
* Peierls for `T` with matrix `!![2, 1; 1, 2]` in the standard basis,
  `f x = x ^ 2`: `2 ^ 2 + 2 ^ 2 = 8 ≤ 10 = 3 ^ 2 + 1 ^ 2`.
* Klein for `f x = x ^ 2`, `S` with matrix `!![2, 1; 1, 2]` and
  `T = 2 • 1`: `6 ≤ 8`.
* Klein for `f x = x * Real.log x`, `S` diagonal `![3 / 4, 1 / 4]` and
  `T = (1 / 2) • 1`: the quantum relative-entropy form.
* `#print axioms` for the main theorems: standard triple only.
-/

noncomputable section

@[expose]
public section

namespace MathlibExtTest.Analysis.InnerProductSpace.PeierlsKleinTests

open MathlibExt.Analysis.InnerProductSpace.PeierlsKlein

/-- The ambient space for the tests. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- The finrank of `E2`. -/
theorem finrank_E2 : Module.finrank ℂ E2 = 2 := finrank_euclideanSpace_fin

/-- The test operator with matrix `!![2, 1; 1, 2]`. -/
def T2 : E2 →ₗ[ℂ] E2 := (Matrix.toEuclideanLin !![2, 1; 1, 2] : E2 →ₗ[ℂ] E2)

/-- The test operator is symmetric. -/
theorem isSymmetric_T2 : T2.IsSymmetric := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff).mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

/-- Applying a `2 × 2` matrix operator, coordinatewise. -/
theorem toEuclideanLin_apply_coord (A : Matrix (Fin 2) (Fin 2) ℂ) (x : E2) (i : Fin 2) :
    (A.toEuclideanLin x) i = A i 0 * x 0 + A i 1 * x 1 := by
  fin_cases i <;>
    simp [Matrix.toLpLin_apply, Matrix.mulVec]

/-- The diagonal of `T2` in the standard basis is constantly `2`. -/
theorem diag_T2 (i : Fin 2) :
    RCLike.re (inner (𝕜 := ℂ) (EuclideanSpace.basisFun (Fin 2) ℂ i)
      (T2 (EuclideanSpace.basisFun (Fin 2) ℂ i))) = 2 := by
  rw [EuclideanSpace.basisFun_inner]
  fin_cases i <;>
    simp [T2, toEuclideanLin_apply_coord, EuclideanSpace.basisFun_apply]

/-- The eigenvector of `T2` for the eigenvalue `3`. -/
def v3 : E2 := WithLp.toLp 2 ![1, 1]

/-- The eigenvector of `T2` for the eigenvalue `1`. -/
def v1 : E2 := WithLp.toLp 2 ![1, -1]

/-- The `3`-eigenspace of `T2` is spanned by `v3`. -/
theorem eigenspace_T2_3 : Module.End.eigenspace T2 ((3 : ℝ) : ℂ) =
    Submodule.span ℂ {v3} := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have h0 := congrArg (fun y : E2 => y 0) hx
    have h1 := congrArg (fun y : E2 => y 1) hx
    simp [T2, toEuclideanLin_apply_coord] at h0 h1
    -- `h0 : 2 * x 0 + x 1 = 3 * x 0`, `h1 : x 0 + 2 * x 1 = 3 * x 1`, so `x 1 = x 0`.
    have hx1 : x 1 = x 0 := by linear_combination h0
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp [v3, hx1, PiLp.smul_apply, smul_eq_mul]
  · rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
    ext i
    fin_cases i <;> simp [T2, v3] <;> norm_num

/-- The `1`-eigenspace of `T2` is spanned by `v1`. -/
theorem eigenspace_T2_1 : Module.End.eigenspace T2 ((1 : ℝ) : ℂ) =
    Submodule.span ℂ {v1} := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have h0 := congrArg (fun y : E2 => y 0) hx
    have h1 := congrArg (fun y : E2 => y 1) hx
    simp [T2, toEuclideanLin_apply_coord] at h0 h1
    -- `h0 : 2 * x 0 + x 1 = x 0`, `h1 : x 0 + 2 * x 1 = x 1`, so `x 1 = -x 0`.
    have hx1 : x 1 = -x 0 := by linear_combination h0
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp [v1, hx1, PiLp.smul_apply, smul_eq_mul]
  · rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
    ext i
    fin_cases i <;> simp [T2, v1] <;> norm_num

/-- If a symmetric operator on `E2` has one-dimensional eigenspaces at
two distinct scalars, its eigenvalues are those scalars in decreasing
order. -/
theorem eigenvalues_eq_of_eigenspaces {T : E2 →ₗ[ℂ] E2} (hT : T.IsSymmetric)
    {a b : ℝ} (hab : b < a)
    (ha : Module.finrank ℂ (Module.End.eigenspace T (a : ℂ)) = 1)
    (hb : Module.finrank ℂ (Module.End.eigenspace T (b : ℂ)) = 1) :
    hT.eigenvalues finrank_E2 = ![a, b] := by
  have hc_a := hT.card_filter_eigenvalues_eq finrank_E2 (a : ℂ)
  have hc_b := hT.card_filter_eigenvalues_eq finrank_E2 (b : ℂ)
  rw [ha] at hc_a
  rw [hb] at hc_b
  obtain ⟨i₁, hi₁⟩ := Finset.card_eq_one.mp hc_a
  obtain ⟨i₂, hi₂⟩ := Finset.card_eq_one.mp hc_b
  have hl1 : hT.eigenvalues finrank_E2 i₁ = a := by
    have hmem : ((hT.eigenvalues finrank_E2 i₁ : ℂ)) = (a : ℂ) := by
      have h := Finset.mem_singleton_self i₁
      rw [← hi₁] at h
      exact (Finset.mem_filter.mp h).2
    exact Complex.ofReal_inj.mp hmem
  have hl2 : hT.eigenvalues finrank_E2 i₂ = b := by
    have hmem : ((hT.eigenvalues finrank_E2 i₂ : ℂ)) = (b : ℂ) := by
      have h := Finset.mem_singleton_self i₂
      rw [← hi₂] at h
      exact (Finset.mem_filter.mp h).2
    exact Complex.ofReal_inj.mp hmem
  have hne : i₁ ≠ i₂ := by
    intro h
    rw [h] at hl1
    exact (ne_of_lt hab).symm (hl1.symm.trans hl2)
  have hant : Antitone (hT.eigenvalues finrank_E2) :=
    hT.eigenvalues_antitone finrank_E2
  fin_cases i₁ <;> fin_cases i₂ <;>
    simp only [Fin.mk_zero, Fin.mk_one] at hl1 hl2 hne
  · exact absurd rfl hne
  · funext i
    fin_cases i <;> simp [hl1, hl2, Fin.mk_one]
  · exfalso
    have hle : a ≤ b := by
      have h01 : (0 : Fin 2) ≤ 1 := by simp
      have hle' := hant h01
      rw [hl1, hl2] at hle'
      exact hle'
    exact absurd hle (not_le_of_gt hab)
  · exact absurd rfl hne

/-- The eigenvalues of `T2` are `3` and `1`. -/
theorem eigenvalues_T2 : isSymmetric_T2.eigenvalues finrank_E2 = ![3, 1] := by
  apply eigenvalues_eq_of_eigenspaces isSymmetric_T2 (by norm_num)
  · rw [eigenspace_T2_3, finrank_span_singleton]
    intro h
    have h0 := congrArg (fun y : E2 => y 0) h
    simp [v3] at h0
  · rw [eigenspace_T2_1, finrank_span_singleton]
    intro h
    have h0 := congrArg (fun y : E2 => y 0) h
    simp [v1] at h0

/-- Peierls for the zero operator: both sides are `0`. -/
theorem peierls_zero :
    ∑ i, (RCLike.re (inner (𝕜 := ℂ) (EuclideanSpace.basisFun (Fin 2) ℂ i)
        ((0 : E2 →ₗ[ℂ] E2) (EuclideanSpace.basisFun (Fin 2) ℂ i)))) ^ 2 = 0 := by
  simp

/-- Peierls for `T2` with `f x = x ^ 2`: `8 ≤ 10`. -/
theorem peierls_T2_sq : (8 : ℝ) ≤ 10 := by
  have h := peierls_inequality finrank_E2 isSymmetric_T2
    (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from even_two.convexOn_pow)
    (fun _ => Set.mem_univ _) (EuclideanSpace.basisFun (Fin 2) ℂ)
  have hdiag : ∀ i, (RCLike.re (inner (𝕜 := ℂ) (EuclideanSpace.basisFun (Fin 2) ℂ i)
      (T2 (EuclideanSpace.basisFun (Fin 2) ℂ i)))) ^ 2 = 4 := by
    intro i
    rw [diag_T2 i]
    norm_num
  have h' : (4 : ℝ) + 4 ≤ 3 ^ 2 + 1 ^ 2 := by
    simpa only [Fin.sum_univ_two, hdiag, eigenvalues_T2, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using h
  linarith [h']

/-- A scalar operator is symmetric (for a real scalar). -/
theorem isSymmetric_smul_id (c : ℝ) :
    (((c : ℂ) • LinearMap.id : E2 →ₗ[ℂ] E2)).IsSymmetric := by
  intro x y
  simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left, inner_smul_right]
  simp

/-- The eigenvalues of a scalar operator are all equal to the scalar. -/
theorem eigenvalues_smul_id (c : ℝ) :
    (isSymmetric_smul_id c).eigenvalues finrank_E2 = fun _ => c := by
  funext j
  have he := (isSymmetric_smul_id c).apply_eigenvectorBasis finrank_E2 j
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at he
  have hne : (isSymmetric_smul_id c).eigenvectorBasis finrank_E2 j ≠ 0 := by
    intro h0
    have hnorm := (isSymmetric_smul_id c).eigenvectorBasis finrank_E2 |>.orthonormal.norm_eq_one j
    rw [h0, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have hsub : ((c : ℂ) - ((isSymmetric_smul_id c).eigenvalues finrank_E2 j : ℂ)) •
      (isSymmetric_smul_id c).eigenvectorBasis finrank_E2 j = 0 := by
    simp [sub_smul, he]
  rcases smul_eq_zero.mp hsub with h | h
  · have h2 : (c : ℂ) = ((isSymmetric_smul_id c).eigenvalues finrank_E2 j : ℂ) :=
      sub_eq_zero.mp h
    exact Complex.ofReal_inj.mp h2.symm
  · exact absurd h hne

/-- Klein for `f x = x ^ 2`, `S = T2` and `T = 2 • 1`: `6 ≤ 8`. -/
theorem klein_sq_T2 : (6 : ℝ) ≤ 8 := by
  have h := klein_sq finrank_E2 (isSymmetric_smul_id 2) isSymmetric_T2
    (EuclideanSpace.basisFun (Fin 2) ℂ)
  have hdiag : ∀ i, RCLike.re (inner (𝕜 := ℂ) (EuclideanSpace.basisFun (Fin 2) ℂ i)
      ((((2 : ℝ) : ℂ) • LinearMap.id : E2 →ₗ[ℂ] E2)
        (EuclideanSpace.basisFun (Fin 2) ℂ i))) = 2 := by
    intro i
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K,
      (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal.norm_eq_one i]
    simp
  have h' : (3 : ℝ) ^ 2 + 2 * 3 * (2 - 3) + ((1 : ℝ) ^ 2 + 2 * 1 * (2 - 1))
      ≤ 2 ^ 2 + 2 ^ 2 := by
    simpa only [Fin.sum_univ_two, eigenvalues_T2, eigenvalues_smul_id 2, hdiag,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  linarith [h']

/-- The diagonal test operator `S` with diagonal `![3 / 4, 1 / 4]`. -/
def Sdiag : E2 →ₗ[ℂ] E2 :=
  (Matrix.toEuclideanLin (Matrix.diagonal ![3 / 4, 1 / 4]) : E2 →ₗ[ℂ] E2)

/-- The diagonal test operator is symmetric. -/
theorem isSymmetric_Sdiag : Sdiag.IsSymmetric := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff).mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

/-- The eigenvalues of `Sdiag` are `3 / 4` and `1 / 4`. -/
theorem eigenvalues_Sdiag :
    isSymmetric_Sdiag.eigenvalues finrank_E2 = ![3 / 4, 1 / 4] := by
  apply eigenvalues_eq_of_eigenspaces isSymmetric_Sdiag (by norm_num)
  · rw [show Module.End.eigenspace Sdiag ((3 / 4 : ℝ) : ℂ) =
        Submodule.span ℂ {EuclideanSpace.single (0 : Fin 2) (1 : ℂ)} from ?_]
    · rw [finrank_span_singleton]
      intro h
      have h0 := congrArg (fun y : E2 => y 0) h
      simp at h0
    · apply le_antisymm
      · intro x hx
        rw [Module.End.mem_eigenspace_iff] at hx
        have h1 := congrArg (fun y : E2 => y 1) hx
        have hL : (Sdiag x) 1 = (1 / 4 : ℂ) * x 1 := by
          simp [Sdiag, toEuclideanLin_apply_coord]
        have hR : (((3 / 4 : ℝ) : ℂ) • x) 1 = ((3 / 4 : ℝ) : ℂ) * x 1 := by
          simp [PiLp.smul_apply, smul_eq_mul]
        rw [hL, hR] at h1
        have hcast : ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) := by norm_num
        rw [hcast] at h1
        have hx1 : x 1 = 0 := by
          have hhalf : (1 / 2 : ℂ) * x 1 = 0 := by linear_combination -h1
          rcases mul_eq_zero.mp hhalf with h | h
          · norm_num at h
          · exact h
        rw [Submodule.mem_span_singleton]
        refine ⟨x 0, ?_⟩
        ext i
        fin_cases i <;> simp [hx1, PiLp.smul_apply, smul_eq_mul]
      · rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
        ext i
        fin_cases i <;>
          simp [Sdiag, toEuclideanLin_apply_coord, PiLp.smul_apply, smul_eq_mul]
  · rw [show Module.End.eigenspace Sdiag ((1 / 4 : ℝ) : ℂ) =
        Submodule.span ℂ {EuclideanSpace.single (1 : Fin 2) (1 : ℂ)} from ?_]
    · rw [finrank_span_singleton]
      intro h
      have h1 := congrArg (fun y : E2 => y 1) h
      simp at h1
    · apply le_antisymm
      · intro x hx
        rw [Module.End.mem_eigenspace_iff] at hx
        have h0 := congrArg (fun y : E2 => y 0) hx
        have hL : (Sdiag x) 0 = (3 / 4 : ℂ) * x 0 := by
          simp [Sdiag, toEuclideanLin_apply_coord]
        have hR : (((1 / 4 : ℝ) : ℂ) • x) 0 = ((1 / 4 : ℝ) : ℂ) * x 0 := by
          simp [PiLp.smul_apply, smul_eq_mul]
        rw [hL, hR] at h0
        have hcast : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
        rw [hcast] at h0
        have hx0 : x 0 = 0 := by
          have hhalf : (1 / 2 : ℂ) * x 0 = 0 := by linear_combination h0
          rcases mul_eq_zero.mp hhalf with h | h
          · norm_num at h
          · exact h
        rw [Submodule.mem_span_singleton]
        refine ⟨x 1, ?_⟩
        ext i
        fin_cases i <;> simp [hx0, PiLp.smul_apply, smul_eq_mul]
      · rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
        ext i
        fin_cases i <;>
          simp [Sdiag, toEuclideanLin_apply_coord, PiLp.smul_apply, smul_eq_mul]

/-- `Sdiag` is positive definite. -/
theorem pos_Sdiag : ∀ x : E2, x ≠ 0 →
    0 < RCLike.re (inner (𝕜 := ℂ) x (Sdiag x)) := by
  intro x hx
  have hcoord : ∀ i : Fin 2, (Sdiag x) i =
      ((![3 / 4, 1 / 4] : Fin 2 → ℂ) i) * x i := by
    intro i
    fin_cases i <;> simp [Sdiag, toEuclideanLin_apply_coord]
  have key : RCLike.re (inner (𝕜 := ℂ) x (Sdiag x))
      = (3 / 4 : ℝ) * ‖x 0‖ ^ 2 + (1 / 4 : ℝ) * ‖x 1‖ ^ 2 := by
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_two, hcoord, Matrix.cons_val_zero, Matrix.cons_val_one]
    show Complex.re (inner ℂ (x 0) ((3 / 4 : ℂ) * x 0) +
      inner ℂ (x 1) ((1 / 4 : ℂ) * x 1)) = _
    rw [Complex.add_re]
    congr 1
    · rw [RCLike.inner_apply', mul_left_comm, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      have hc : (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) := by norm_num
      rw [hc, ← Complex.ofReal_mul, Complex.ofReal_re]
    · rw [RCLike.inner_apply', mul_left_comm, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      have hc : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
      rw [hc, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [key]
  by_contra hle
  have hle : (3 / 4 : ℝ) * ‖x 0‖ ^ 2 + (1 / 4 : ℝ) * ‖x 1‖ ^ 2 ≤ 0 := le_of_not_gt hle
  have hx0 : x 0 = 0 := by
    by_contra hne
    have hpos : (0 : ℝ) < (3 / 4 : ℝ) * ‖x 0‖ ^ 2 :=
      mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hne) 2)
    have hnn : (0 : ℝ) ≤ (1 / 4 : ℝ) * ‖x 1‖ ^ 2 := by positivity
    linarith
  have hx1 : x 1 = 0 := by
    by_contra hne
    have hpos : (0 : ℝ) < (1 / 4 : ℝ) * ‖x 1‖ ^ 2 :=
      mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hne) 2)
    have hnn : (0 : ℝ) ≤ (3 / 4 : ℝ) * ‖x 0‖ ^ 2 := by positivity
    linarith
  exact hx (by ext i; fin_cases i <;> simp [hx0, hx1])

/-- `T = (1 / 2) • 1` is positive semidefinite. -/
theorem nonneg_smul_half_id : ∀ x : E2,
    0 ≤ RCLike.re (inner (𝕜 := ℂ) x
      ((((1 / 2 : ℝ) : ℂ) • LinearMap.id : E2 →ₗ[ℂ] E2) x)) := by
  intro x
  have key : RCLike.re (inner (𝕜 := ℂ) x
      ((((1 / 2 : ℝ) : ℂ) • LinearMap.id : E2 →ₗ[ℂ] E2) x))
      = (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    rw [show ((((1 / 2 : ℝ) : ℂ) • LinearMap.id : E2 →ₗ[ℂ] E2) x)
        = ((1 / 2 : ℝ) : ℂ) • x by simp,
      inner_smul_right, inner_self_eq_norm_sq_to_K]
    show Complex.re (↑(1 / 2 : ℝ) * (↑‖x‖) ^ 2)
      = (1 / 2 : ℝ) * ‖x‖ ^ 2
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [key]
  positivity

/-- Klein's entropy form for `S`, `T` diagonal/scalar: a concrete
quantum relative-entropy inequality. -/
theorem klein_entropy_diag :
    (3 / 4 : ℝ) * Real.log (3 / 4) + (Real.log (3 / 4) + 1) * (1 / 2 - 3 / 4)
      + ((1 / 4 : ℝ) * Real.log (1 / 4) + (Real.log (1 / 4) + 1) * (1 / 2 - 1 / 4))
      ≤ (1 / 2 : ℝ) * Real.log (1 / 2) + (1 / 2 : ℝ) * Real.log (1 / 2) := by
  have h := klein_entropy finrank_E2 (isSymmetric_smul_id (1 / 2)) isSymmetric_Sdiag
    nonneg_smul_half_id pos_Sdiag (EuclideanSpace.basisFun (Fin 2) ℂ)
  have hdiag : ∀ i, RCLike.re (inner (𝕜 := ℂ) (EuclideanSpace.basisFun (Fin 2) ℂ i)
      ((((1 / 2 : ℝ) : ℂ) • LinearMap.id : E2 →ₗ[ℂ] E2)
        (EuclideanSpace.basisFun (Fin 2) ℂ i))) = 1 / 2 := by
    intro i
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K,
      (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal.norm_eq_one i]
    simp
  simpa only [Fin.sum_univ_two, eigenvalues_Sdiag, eigenvalues_smul_id (1 / 2), hdiag,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

#print axioms peierls_inequality
#print axioms klein_inequality
#print axioms peierls_exp
#print axioms klein_sq
#print axioms klein_entropy

end MathlibExtTest.Analysis.InnerProductSpace.PeierlsKleinTests
