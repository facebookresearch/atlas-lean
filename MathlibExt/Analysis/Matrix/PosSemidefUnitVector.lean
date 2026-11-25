/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.InnerProductSpace.Complex.UnitVector
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Negative unit-vector witnesses for Hermitian matrices

Let `M` be a complex Hermitian matrix on any finite index type `n`. It is
not positive semidefinite exactly when there exists a unit coordinate vector
`ψ` with `ψ* M ψ < 0`. Unit means `sum_i conjugate(ψᵢ) ψᵢ = 1`, the
ordinary Euclidean normalization. The Hermitian quadratic form is real, and
the displayed complex-order comparison is therefore strict real negativity.

No nonempty-index assumption is added. For the empty type there is no unit
vector and the unique matrix is positive semidefinite, so both sides of the
negated characterization are false.
-/

@[expose] public section

open scoped ComplexOrder BigOperators
open Complex Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A finite complex Hermitian matrix fails positive semidefiniteness exactly when its quadratic
form is a negative real value on some Euclidean unit vector. The unit normalization is the
coordinate sum of squared absolute values equal to one.

```lean
public theorem not_posSemidef_iff_exists_unitVector_neg {M : Matrix n n ℂ}
    (hM : M.IsHermitian) :
    ¬ M.PosSemidef ↔ ∃ ψ : Complex.UnitVector n, star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) < 0
``` -/
public theorem not_posSemidef_iff_exists_unitVector_neg {M : Matrix n n ℂ}
    (hM : M.IsHermitian) :
    ¬ M.PosSemidef ↔ ∃ ψ : Complex.UnitVector n, star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) < 0 := by
  constructor
  · intro hNot
    have h_not_forall : ¬ ∀ x : n → ℂ, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
      intro hAll
      exact hNot (posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, hAll⟩)
    classical
    have h_exists : ∃ x : n → ℂ, ¬ 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
      by_contra h
      have h_all : ∀ x : n → ℂ, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
        intro x
        by_contra hx
        exact h ⟨x, hx⟩
      exact h_not_forall h_all
    obtain ⟨x, hx⟩ := h_exists
    have h_im : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := hM.im_star_dotProduct_mulVec_self x
    have h_re_not_nonneg : ¬ 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
      intro hle
      have : 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
        rw [Complex.nonneg_iff]
        exact ⟨hle, h_im.symm⟩
      exact hx this
    have h_re_neg : (star x ⬝ᵥ (M *ᵥ x)).re < 0 :=
      lt_of_not_ge h_re_not_nonneg
    have h_q_neg : star x ⬝ᵥ (M *ᵥ x) < 0 := by
      rw [Complex.neg_iff]
      exact ⟨h_re_neg, h_im⟩
    have hx_ne : x ≠ 0 := by
      intro hx0
      have : star x ⬝ᵥ (M *ᵥ x) = 0 := by simp [hx0]
      rw [this] at h_q_neg
      exact lt_irrefl _ h_q_neg
    have h_exists_coord : ∃ i : n, x i ≠ 0 := by
      by_contra h
      have h_all : ∀ i, x i = 0 := by
        intro i
        by_contra hi
        exact h ⟨i, hi⟩
      have : x = 0 := funext h_all
      exact hx_ne this
    let S : ℝ := ∑ i : n, Complex.normSq (x i)
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hS_pos : 0 < S := by
      have h_nonneg : ∀ i ∈ Finset.univ (α := n), 0 ≤ Complex.normSq (x i) :=
        fun i _ => Complex.normSq_nonneg _
      have h_pos : ∃ i ∈ Finset.univ (α := n), 0 < Complex.normSq (x i) := by
        obtain ⟨i0, hi0⟩ := h_exists_coord
        exact ⟨i0, Finset.mem_univ _, (Complex.normSq_pos).mpr hi0⟩
      exact Finset.sum_pos' h_nonneg h_pos
    let r : ℝ := Real.sqrt S
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hS_pos
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have hr_sq : r * r = S := Real.mul_self_sqrt hS_nonneg
    let t : ℝ := r⁻¹
    have ht_pos : 0 < t := inv_pos.mpr hr_pos
    have htr : t * r = 1 := inv_mul_cancel₀ hr_ne
    have ht_sq_mul_S : t * t * S = 1 := by
      calc t * t * S = t * t * (r * r) := by rw [hr_sq]
        _ = (t * r) * (t * r) := by ring
        _ = 1 := by rw [htr, one_mul]
    let c : ℂ := (t : ℂ)
    have hc_star : star c = c := by
      simp [c]
    let y : n → ℂ := fun i => c * x i
    have hy_star : ∀ i, star (y i) = c * star (x i) := by
      intro i
      simp only [y]
      rw [star_mul, hc_star, mul_comm]
    have h_star_y_eq : star y = c • star x := by
      funext i
      simp only [Pi.star_apply, y, Pi.smul_apply, smul_eq_mul]
      rw [star_mul, hc_star, mul_comm]
    have h_mulVec_y : M *ᵥ y = c • (M *ᵥ x) := by
      have : y = c • x := by
        funext i
        simp [y, smul_eq_mul]
      rw [this, Matrix.mulVec_smul]
    have h_eq_star_mul_self : ∀ i, star (x i) * x i = (Complex.normSq (x i) : ℂ) := by
      intro i
      simp only [Complex.star_def]
      rw [← Complex.normSq_eq_conj_mul_self]
    have h_sum_star_x : ∑ i : n, star (x i) * x i = (S : ℂ) := by
      have h1 : ∑ i : n, star (x i) * x i = ∑ i : n, (Complex.normSq (x i) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_eq_star_mul_self i
      rw [h1, Complex.ofReal_sum]
    have h_unit_sum : ∑ i : n, star (y i) * y i = 1 := by
      have h1 : ∀ i, star (y i) * y i = (c * c) * (star (x i) * x i) := by
        intro i
        calc star (y i) * y i = (c * star (x i)) * (c * x i) := by rw [hy_star]
          _ = (c * c) * (star (x i) * x i) := by ring
      have h2 : ∑ i : n, star (y i) * y i = (c * c) * ∑ i : n, star (x i) * x i := by
        calc ∑ i : n, star (y i) * y i
            = ∑ i : n, (c * c) * (star (x i) * x i) := Finset.sum_congr rfl fun i _ => h1 i
          _ = (c * c) * ∑ i : n, star (x i) * x i := by rw [Finset.mul_sum]
      rw [h2, h_sum_star_x]
      have hc2 : c * c = ((t * t : ℝ) : ℂ) := by simp [c, Complex.ofReal_mul]
      rw [hc2, ← Complex.ofReal_mul, ht_sq_mul_S]
      simp
    let ψ : Complex.UnitVector n := ⟨y, h_unit_sum⟩
    have h_q_y : star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) = ((t * t : ℝ) : ℂ) * (star x ⬝ᵥ (M *ᵥ x)) := by
      have h_dot : star y ⬝ᵥ (M *ᵥ y) = (c • star x) ⬝ᵥ (c • (M *ᵥ x)) := by
        rw [h_star_y_eq, h_mulVec_y]
      calc star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) = star y ⬝ᵥ (M *ᵥ y) := rfl
        _ = (c • star x) ⬝ᵥ (c • (M *ᵥ x)) := h_dot
        _ = c • ((star x) ⬝ᵥ (c • (M *ᵥ x))) := by rw [smul_dotProduct]
        _ = c • (c • (star x ⬝ᵥ (M *ᵥ x))) := by rw [dotProduct_smul]
        _ = (c * c) • (star x ⬝ᵥ (M *ᵥ x)) := by rw [smul_smul]
        _ = ((t * t : ℝ) : ℂ) * (star x ⬝ᵥ (M *ᵥ x)) := by
            have hc2 : c * c = ((t * t : ℝ) : ℂ) := by simp [c, Complex.ofReal_mul]
            rw [hc2, smul_eq_mul]
    have h_q_y_neg : star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) < 0 := by
      rw [h_q_y]
      have ht2_pos : 0 < t * t := mul_pos ht_pos ht_pos
      let q := star x ⬝ᵥ (M *ᵥ x)
      have h_re : (((t * t : ℝ) : ℂ) * q).re = (t * t) * q.re := by simp [q]
      have h_im_eq : (((t * t : ℝ) : ℂ) * q).im = (t * t) * q.im := by simp [q]
      rw [Complex.neg_iff]
      refine ⟨?_, ?_⟩
      · rw [h_re]
        exact mul_neg_of_pos_of_neg ht2_pos h_re_neg
      · rw [h_im_eq, h_im, mul_zero]
    exact ⟨ψ, h_q_y_neg⟩
  · intro hExists hPSD
    obtain ⟨ψ, hψ⟩ := hExists
    have h_nonneg := hPSD.dotProduct_mulVec_nonneg ψ.coord
    have h_not_nonneg : ¬ 0 ≤ star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) := by
      intro hle
      rw [Complex.nonneg_iff] at hle
      rw [Complex.neg_iff] at hψ
      exact lt_irrefl _ (lt_of_lt_of_le hψ.1 hle.1)
    exact h_not_nonneg h_nonneg

end Matrix
