/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Power iteration and the Rayleigh quotient

Let `T` be a linear operator on a finite-dimensional real inner product space with an
orthonormal eigenbasis `b` (`T b_j = λ_j b_j`; by the spectral theorem this is the case of a
symmetric matrix). Suppose `λ_{i₀}` is strictly dominant: `|λ_j| ≤ μ < |λ_{i₀}|` for `j ≠ i₀`,
and the starting vector `v₀` has a nonzero component `c = ⟪q, v₀⟫` along `q = b_{i₀}`.
Power iteration computes `v_k = T^k v₀ / ‖T^k v₀‖` and the Rayleigh quotient
`r(v_k) = ⟪v_k, T v_k⟫`. With `ρ = μ / |λ_{i₀}|` (Trefethen and Bau, *Numerical Linear Algebra*,
Lecture 27, convergence of power iteration):

* `norm_smul_pow_apply_sub_le`: `‖(c λ_{i₀}^k)⁻¹ T^k v₀ - q‖ ≤ ρ^k ‖v₀‖ / |c|`;
* `exists_sign_norm_normalize_sub_le`: `‖v_k - (±q)‖ ≤ 2 ρ^k ‖v₀‖ / |c|`, for a sign depending
  on `k`; the iterates converge linearly, at rate `ρ`, up to sign;
* `abs_rayleigh_pow_apply_sub_le`: if `|λ_j - λ_{i₀}| ≤ D` for all `j`, then
  `|r(T^k v₀) - λ_{i₀}| ≤ D ρ^{2k} (‖v₀‖ / |c|)^2`: the eigenvalue estimate converges twice as
  fast, because the Rayleigh quotient is a quadratically accurate eigenvalue estimate
  (`inner_apply_sub_eq_of_eigen`, Trefethen–Bau, Lecture 27).

All statements are in exact arithmetic. The rates of the shifted and inverse variants
(inverse iteration, Rayleigh quotient iteration, the QR algorithm as simultaneous iteration)
follow the same pattern and are not formalized here.

## References

* L. N. Trefethen, D. Bau III, *Numerical Linear Algebra*, SIAM, 1997, Lecture 27
  (convergence of power iteration and the quadratic accuracy of the Rayleigh quotient).
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., Johns Hopkins, 2013,
  Section 7.3.1 (the power method).
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.PowerIteration

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Powers of an operator act on an eigenvector by powers of the eigenvalue. -/
lemma pow_apply_of_eigen {T : E →ₗ[ℝ] E} {v : E} {lam : ℝ} (h : T v = lam • v) (k : ℕ) :
    (T ^ k) v = lam ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

/-- Coordinates of `T^k v` in an orthonormal eigenbasis: `⟪b_j, T^k v⟫ = λ_j^k ⟪b_j, v⟫`. -/
lemma inner_pow_apply {T : E →ₗ[ℝ] E} (b : OrthonormalBasis ι ℝ E) {lam : ι → ℝ}
    (hT : ∀ j, T (b j) = lam j • b j) (k : ℕ) (j : ι) (v : E) :
    ⟪b j, (T ^ k) v⟫ = lam j ^ k * ⟪b j, v⟫ := by
  classical
  conv_lhs => rw [← b.sum_repr' v]
  simp only [map_sum, map_smul, pow_apply_of_eigen (hT _), smul_smul, inner_sum,
    inner_smul_right, orthonormal_iff_ite.1 b.orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **Power iteration, unnormalized form** (Trefethen–Bau, Lecture 27): with
`c = ⟪q, v₀⟫ ≠ 0` and `ρ = μ / |λ_{i₀}|`, `‖(c λ_{i₀}^k)⁻¹ T^k v₀ - q‖ ≤ ρ^k ‖v₀‖ / |c|`. -/
theorem norm_smul_pow_apply_sub_le {T : E →ₗ[ℝ] E} (b : OrthonormalBasis ι ℝ E) {lam : ι → ℝ}
    (hT : ∀ j, T (b j) = lam j • b j) {i₀ : ι} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ j, j ≠ i₀ → |lam j| ≤ μ) (hlam : lam i₀ ≠ 0) {v₀ : E} (hc : ⟪b i₀, v₀⟫ ≠ 0)
    (k : ℕ) :
    ‖(⟪b i₀, v₀⟫ * lam i₀ ^ k)⁻¹ • (T ^ k) v₀ - b i₀‖ ≤
      (μ / |lam i₀|) ^ k * (‖v₀‖ / |⟪b i₀, v₀⟫|) := by
  classical
  set c := ⟪b i₀, v₀⟫
  set w := (c * lam i₀ ^ k)⁻¹ • (T ^ k) v₀ - b i₀
  have hl : 0 < |lam i₀| := abs_pos.2 hlam
  have hck : c * lam i₀ ^ k ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hlam)
  have hcoord : ∀ j, ⟪b j, w⟫ ^ 2 ≤ ((μ / |lam i₀|) ^ k) ^ 2 * (⟪b j, v₀⟫ / c) ^ 2 := by
    intro j
    have : ⟪b j, w⟫ = (c * lam i₀ ^ k)⁻¹ * (lam j ^ k * ⟪b j, v₀⟫) - (if j = i₀ then 1 else 0) := by
      simp only [w, inner_sub_right, inner_smul_right, inner_pow_apply b hT,
        orthonormal_iff_ite.1 b.orthonormal]
    rw [this]
    by_cases hj : j = i₀
    · subst hj
      simp only [ite_true]
      rw [show (c * lam j ^ k)⁻¹ * (lam j ^ k * c) - 1 = 0 by field_simp; ring]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · simp only [hj, ite_false, sub_zero]
      have e : (c * lam i₀ ^ k)⁻¹ * (lam j ^ k * ⟪b j, v₀⟫) =
          (lam j / lam i₀) ^ k * (⟪b j, v₀⟫ / c) := by
        rw [div_pow]; field_simp
      rw [e, mul_pow]
      gcongr ?_ * _
      rw [← sq_abs ((lam j / lam i₀) ^ k), abs_pow, abs_div]
      gcongr
      exact hμ j hj
  have hsum : ‖w‖ ^ 2 ≤ ((μ / |lam i₀|) ^ k * (‖v₀‖ / |c|)) ^ 2 := by
    rw [← b.sum_sq_inner_right w]
    calc ∑ j, ⟪b j, w⟫ ^ 2 ≤ ∑ j, ((μ / |lam i₀|) ^ k) ^ 2 * (⟪b j, v₀⟫ / c) ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = ((μ / |lam i₀|) ^ k) ^ 2 * ((∑ j, ⟪b j, v₀⟫ ^ 2) / c ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_div]
          exact congrArg _ (Finset.sum_congr rfl fun j _ => div_pow _ _ _)
      _ = ((μ / |lam i₀|) ^ k * (‖v₀‖ / |c|)) ^ 2 := by
          rw [b.sum_sq_inner_right, mul_pow (_ ^ k), div_pow ‖v₀‖, sq_abs]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsum

/-- Normalizing a vector close to a unit vector at most doubles the distance. -/
lemma norm_normalize_sub_le {q y : E} (hq : ‖q‖ = 1) : ‖‖y‖⁻¹ • y - q‖ ≤ 2 * ‖y - q‖ := by
  by_cases hy : y = 0
  · subst hy; simp [hq]
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h1 : ‖‖y‖⁻¹ • y - y‖ = |1 - ‖y‖| := by
    rw [show ‖y‖⁻¹ • y - y = (‖y‖⁻¹ - 1) • y by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, show ‖y‖⁻¹ - 1 = (1 - ‖y‖) / ‖y‖ by field_simp, abs_div,
      abs_of_pos hy', div_mul_cancel₀ _ hy'.ne']
  have h2 : |1 - ‖y‖| ≤ ‖y - q‖ := by
    rw [← hq, abs_sub_comm]; exact abs_norm_sub_norm_le y q
  calc ‖‖y‖⁻¹ • y - q‖ = ‖(‖y‖⁻¹ • y - y) + (y - q)‖ := by abel_nf
    _ ≤ ‖‖y‖⁻¹ • y - y‖ + ‖y - q‖ := norm_add_le _ _
    _ ≤ 2 * ‖y - q‖ := by rw [h1]; linarith

/-- **Power iteration** (Trefethen–Bau, Lecture 27): the normalized iterate
`v_k = T^k v₀ / ‖T^k v₀‖` satisfies `‖v_k - s q‖ ≤ 2 ρ^k ‖v₀‖ / |c|` for a sign `s = ±1`. -/
theorem exists_sign_norm_normalize_sub_le {T : E →ₗ[ℝ] E} (b : OrthonormalBasis ι ℝ E)
    {lam : ι → ℝ} (hT : ∀ j, T (b j) = lam j • b j) {i₀ : ι} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ j, j ≠ i₀ → |lam j| ≤ μ) (hlam : lam i₀ ≠ 0) {v₀ : E} (hc : ⟪b i₀, v₀⟫ ≠ 0)
    (k : ℕ) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖‖(T ^ k) v₀‖⁻¹ • (T ^ k) v₀ - s • b i₀‖ ≤
        2 * ((μ / |lam i₀|) ^ k * (‖v₀‖ / |⟪b i₀, v₀⟫|)) := by
  set a := ⟪b i₀, v₀⟫ * lam i₀ ^ k
  have ha : a ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hlam)
  obtain ⟨y, hy⟩ : ∃ y, y = a⁻¹ • (T ^ k) v₀ := ⟨_, rfl⟩
  have hx : (T ^ k) v₀ = a • y := by rw [hy, smul_inv_smul₀ ha]
  have hbound : ‖y - b i₀‖ ≤ (μ / |lam i₀|) ^ k * (‖v₀‖ / |⟪b i₀, v₀⟫|) := by
    rw [hy]; exact norm_smul_pow_apply_sub_le b hT hμ0 hμ hlam hc k
  have hq : ‖b i₀‖ = 1 := b.orthonormal.1 i₀
  refine ⟨a / |a|, ?_, ?_⟩
  · rcases lt_or_gt_of_ne ha with h | h
    · right; rw [abs_of_neg h, div_neg, div_self ha]
    · left; rw [abs_of_pos h, div_self ha]
  · rw [hx, norm_smul, Real.norm_eq_abs, mul_inv, smul_smul,
      show |a|⁻¹ * ‖y‖⁻¹ * a = a / |a| * ‖y‖⁻¹ by ring, ← smul_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_div, abs_abs, div_self (abs_ne_zero.2 ha), one_mul]
    exact (norm_normalize_sub_le hq).trans (by gcongr)

/-- **Quadratic accuracy of the Rayleigh quotient** (Trefethen–Bau, Lecture 27): for a symmetric
`T` and an eigenvector `T q = λ q`, `⟪v, T v⟫ - λ ‖v‖² = ⟪v - q, T (v - q) - λ (v - q)⟫`; the error
of the Rayleigh quotient as an eigenvalue estimate is quadratic in the error of the vector. -/
theorem inner_apply_sub_eq_of_eigen {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {q : E} {lam : ℝ}
    (hq : T q = lam • q) (v : E) :
    ⟪v, T v⟫ - lam * ‖v‖ ^ 2 = ⟪v - q, T (v - q) - lam • (v - q)⟫ := by
  have hsym : ⟪q, T v⟫ = lam * ⟪q, v⟫ := by rw [← hT, hq, real_inner_smul_left]
  simp only [map_sub, inner_sub_left, inner_sub_right, real_inner_smul_right, hsym,
    hq, real_inner_smul_right, ← real_inner_self_eq_norm_sq, real_inner_comm q v]
  ring

/-- **Convergence of the power-iteration eigenvalue estimate** (Trefethen–Bau, Lecture 27): if
`|λ_j - λ_{i₀}| ≤ D` for every `j`, the Rayleigh quotient of `T^k v₀` satisfies
`|⟪x, T x⟫ / ‖x‖² - λ_{i₀}| ≤ D ρ^{2k} (‖v₀‖ / |c|)²`, `x = T^k v₀`. -/
theorem abs_rayleigh_pow_apply_sub_le {T : E →ₗ[ℝ] E} (b : OrthonormalBasis ι ℝ E)
    {lam : ι → ℝ} (hT : ∀ j, T (b j) = lam j • b j) {i₀ : ι} {μ D : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ j, j ≠ i₀ → |lam j| ≤ μ) (hlam : lam i₀ ≠ 0)
    (hD : ∀ j, |lam j - lam i₀| ≤ D) {v₀ : E} (hc : ⟪b i₀, v₀⟫ ≠ 0) (k : ℕ) :
    |⟪(T ^ k) v₀, T ((T ^ k) v₀)⟫ / ‖(T ^ k) v₀‖ ^ 2 - lam i₀| ≤
      D * ((μ / |lam i₀|) ^ k * (‖v₀‖ / |⟪b i₀, v₀⟫|)) ^ 2 := by
  classical
  set a := ⟪b i₀, v₀⟫ * lam i₀ ^ k
  have ha : a ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hlam)
  set y := a⁻¹ • (T ^ k) v₀
  set w := y - b i₀
  have hx : (T ^ k) v₀ = a • y := by rw [smul_inv_smul₀ ha]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i₀)
  -- coordinates of `y`: `y_{i₀} = 1`, `y_j = w_j` otherwise
  have hTb : ∀ j x, ⟪b j, T x⟫ = lam j * ⟪b j, x⟫ := fun j x => by
    simpa using inner_pow_apply b hT 1 j x
  have hquad : ∀ x : E, ⟪x, T x⟫ - lam i₀ * ‖x‖ ^ 2 = ∑ j, (lam j - lam i₀) * ⟪b j, x⟫ ^ 2 := by
    intro x
    rw [← b.sum_inner_mul_inner x (T x), ← b.sum_sq_inner_right x, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hTb, real_inner_comm]
    ring
  have hwj : ∀ j, (lam j - lam i₀) * ⟪b j, y⟫ ^ 2 = (lam j - lam i₀) * ⟪b j, w⟫ ^ 2 := by
    intro j
    by_cases hj : j = i₀
    · subst hj; simp
    · congr 2
      simp only [w, inner_sub_right, orthonormal_iff_ite.1 b.orthonormal, hj, ite_false,
        sub_zero]
  have hy1 : 1 ≤ ‖y‖ := by
    have : ⟪b i₀, y⟫ = 1 := by
      simp only [y, a, inner_smul_right, inner_pow_apply b hT]
      field_simp
    have := abs_real_inner_le_norm (b i₀) y
    rw [‹⟪b i₀, y⟫ = 1›, abs_one, b.orthonormal.1 i₀, one_mul] at this
    exact this
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le one_pos hy1
  have hscale : ⟪(T ^ k) v₀, T ((T ^ k) v₀)⟫ / ‖(T ^ k) v₀‖ ^ 2 = ⟪y, T y⟫ / ‖y‖ ^ 2 := by
    rw [hx, map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    field_simp
  rw [hscale, show ⟪y, T y⟫ / ‖y‖ ^ 2 - lam i₀ = (⟪y, T y⟫ - lam i₀ * ‖y‖ ^ 2) / ‖y‖ ^ 2 by
    field_simp, hquad, abs_div, abs_of_pos (pow_pos hypos 2)]
  have hnum : |∑ j, (lam j - lam i₀) * ⟪b j, y⟫ ^ 2| ≤ D * ‖w‖ ^ 2 := by
    simp_rw [hwj]
    rw [← b.sum_sq_inner_right w, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg ⟪b j, w⟫)]
    exact mul_le_mul_of_nonneg_right (hD j) (sq_nonneg _)
  have hw := norm_smul_pow_apply_sub_le b hT hμ0 hμ hlam hc k
  calc |∑ j, (lam j - lam i₀) * ⟪b j, y⟫ ^ 2| / ‖y‖ ^ 2
      ≤ |∑ j, (lam j - lam i₀) * ⟪b j, y⟫ ^ 2| :=
        div_le_self (abs_nonneg _) (one_le_pow₀ hy1)
    _ ≤ D * ‖w‖ ^ 2 := hnum
    _ ≤ D * ((μ / |lam i₀|) ^ k * (‖v₀‖ / |⟪b i₀, v₀⟫|)) ^ 2 := by
        gcongr

end MathlibExt.Analysis.InnerProductSpace.PowerIteration
