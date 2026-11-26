/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# The Bauer–Fike theorem for diagonalizable matrices

Bauer and Fike (*Norms and exclusion theorems*, Numer. Math. 2 (1960), 137–141) localise the
eigenvalues of a perturbed matrix `A + E`. The general exclusion statement is: if `μ` is an
eigenvalue of `A + E` but not of `A`, then `1 ≤ ‖(μ I - A)⁻¹‖ ‖E‖` for every submultiplicative
norm. For a diagonalizable `A = V Λ V⁻¹` with `Λ = diag(λ₁, …, λₙ)` and the spectral norm, in
which the norm of a diagonal matrix is its largest entry in absolute value, this gives the
Bauer–Fike theorem as it is usually taught: every eigenvalue `μ` of `A + E` satisfies
`|μ - λᵢ| ≤ ‖V‖ ‖V⁻¹‖ ‖E‖` for some `i`, the factor `κ(V) = ‖V‖ ‖V⁻¹‖` being the condition number
of the eigenvector matrix (Encyclopedia of Mathematics, *Bauer–Fike theorem*, equations (a1) and
(a2), https://encyclopediaofmath.org/wiki/Bauer%E2%80%93Fike_theorem).

`MathlibExt.Analysis.InnerProductSpace.BauerFike` proves the case of a normal operator on a
Hilbert space, where `V` can be taken unitary and `κ(V) = 1`.

## Main results

* `one_le_norm_inverse_mul_of_mem_spectrum_add` and
  `one_le_norm_inverse_mul_norm_of_mem_spectrum_add`: the exclusion statement (a2),
  `1 ≤ ‖(μ - A)⁻¹ E‖ ≤ ‖(μ - A)⁻¹‖ ‖E‖`, in any complete normed algebra.
* `exists_norm_sub_le_of_mem_spectrum_add`: the Bauer–Fike theorem (a1) for complex square
  matrices with the spectral (`L²` operator) norm.
-/

@[expose] public section

namespace MathlibExt.Analysis.Matrix.BauerFikeDiagonalizable

open MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation

/-- **Bauer–Fike exclusion theorem.** In a complete normed algebra over a field `𝕜`, if `μ` is
in the spectrum of `A + E` and `μ - A` is invertible, then `1 ≤ ‖(μ - A)⁻¹ E‖`
(Encyclopedia of Mathematics, *Bauer–Fike theorem*, the left-hand inequality of (a2)). -/
theorem one_le_norm_inverse_mul_of_mem_spectrum_add {𝕜 R : Type*} [Field 𝕜]
    [NormedRing R] [CompleteSpace R] [Algebra 𝕜 R] {A E : R} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 (A + E)) (hA : IsUnit (algebraMap 𝕜 R μ - A)) :
    1 ≤ ‖Ring.inverse (algebraMap 𝕜 R μ - A) * E‖ := by
  obtain ⟨U, hU⟩ := hA
  by_contra hlt
  push Not at hlt
  apply hμ
  rw [← hU, Ring.inverse_unit] at hlt
  have h1 : IsUnit (1 - (↑U⁻¹ : R) * E) := (Units.oneSub _ hlt).isUnit
  have h2 : algebraMap 𝕜 R μ - (A + E) = (U : R) * (1 - (↑U⁻¹ : R) * E) := by
    rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hU]
    abel
  change IsUnit (algebraMap 𝕜 R μ - (A + E))
  rw [h2]
  exact U.isUnit.mul h1

/-- **Bauer–Fike exclusion theorem, product form.** Under the same hypotheses,
`1 ≤ ‖(μ - A)⁻¹‖ ‖E‖` (Encyclopedia of Mathematics, *Bauer–Fike theorem*, the outer inequality of
the chain (a2)). This weaker form is the one that gives the Bauer–Fike theorem for diagonalizable
matrices. -/
theorem one_le_norm_inverse_mul_norm_of_mem_spectrum_add {𝕜 R : Type*} [Field 𝕜]
    [NormedRing R] [CompleteSpace R] [Algebra 𝕜 R] {A E : R} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 (A + E)) (hA : IsUnit (algebraMap 𝕜 R μ - A)) :
    1 ≤ ‖Ring.inverse (algebraMap 𝕜 R μ - A)‖ * ‖E‖ :=
  (one_le_norm_inverse_mul_of_mem_spectrum_add hμ hA).trans (norm_mul_le _ _)

open scoped Matrix.Norms.L2Operator

/-- **Bauer–Fike theorem for diagonalizable matrices.** Let `A = V diag(λ) V⁻¹` be a
diagonalizable complex square matrix and `E` any complex matrix of the same size. Every
eigenvalue `μ` of `A + E` lies within `‖V‖ ‖V⁻¹‖ ‖E‖` of some eigenvalue `λᵢ` of `A`, in the
spectral norm (Encyclopedia of Mathematics, *Bauer–Fike theorem*, inequality (a1); F. L. Bauer
and C. T. Fike, Numer. Math. 2 (1960)). -/
theorem exists_norm_sub_le_of_mem_spectrum_add {n : Type*} [Fintype n] [DecidableEq n]
    (V : (Matrix n n ℂ)ˣ) (lam : n → ℂ) (E : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((V : Matrix n n ℂ) * Matrix.diagonal lam * (↑V⁻¹ : Matrix n n ℂ) + E)) :
    ∃ i, ‖μ - lam i‖ ≤ ‖(V : Matrix n n ℂ)‖ * ‖(↑V⁻¹ : Matrix n n ℂ)‖ * ‖E‖ := by
  have : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ (Matrix n n ℂ)
  set K := ‖(V : Matrix n n ℂ)‖ * ‖(↑V⁻¹ : Matrix n n ℂ)‖ * ‖E‖
  rcases isEmpty_or_nonempty n with hn | hn
  · -- `0 × 0` matrices: every element is a unit, so the spectrum is empty.
    exfalso
    apply hμ
    exact isUnit_of_subsingleton _
  by_contra hcon
  push Not at hcon
  -- `μ - λᵢ ≠ 0` for every `i`
  have hne : ∀ i, μ - lam i ≠ 0 := fun i h => by
    have := hcon i
    rw [h, norm_zero] at this
    exact absurd this (not_lt.2 (by positivity))
  set w : n → ℂ := fun i => (μ - lam i)⁻¹
  -- `μ - A = V diag(μ - λ) V⁻¹`, invertible with inverse `V diag(w) V⁻¹`
  set D : Matrix n n ℂ := Matrix.diagonal fun i => μ - lam i
  have hDw : D * Matrix.diagonal w = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hne i)
  have hwD : Matrix.diagonal w * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hne i)
  have hshift : algebraMap ℂ (Matrix n n ℂ) μ -
      (V : Matrix n n ℂ) * Matrix.diagonal lam * (↑V⁻¹ : Matrix n n ℂ) =
      (V : Matrix n n ℂ) * D * (↑V⁻¹ : Matrix n n ℂ) := by
    have h1 : algebraMap ℂ (Matrix n n ℂ) μ =
        (V : Matrix n n ℂ) * Matrix.diagonal (fun _ => μ) * (↑V⁻¹ : Matrix n n ℂ) := by
      rw [Matrix.algebraMap_eq_diagonal, ← Matrix.scalar_apply, Matrix.scalar_apply,
        Matrix.mul_assoc]
      rw [show (Matrix.diagonal fun _ : n => μ) * (↑V⁻¹ : Matrix n n ℂ) =
          (↑V⁻¹ : Matrix n n ℂ) * Matrix.diagonal (fun _ : n => μ) by
        rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one]]
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rfl
    rw [h1, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  set U : (Matrix n n ℂ)ˣ :=
    { val := (V : Matrix n n ℂ) * D * (↑V⁻¹ : Matrix n n ℂ)
      inv := (V : Matrix n n ℂ) * Matrix.diagonal w * (↑V⁻¹ : Matrix n n ℂ)
      val_inv := by
        calc (V : Matrix n n ℂ) * D * (↑V⁻¹ : Matrix n n ℂ) *
              ((V : Matrix n n ℂ) * Matrix.diagonal w * (↑V⁻¹ : Matrix n n ℂ))
            = (V : Matrix n n ℂ) * D * ((↑V⁻¹ : Matrix n n ℂ) * (V : Matrix n n ℂ)) *
                Matrix.diagonal w * (↑V⁻¹ : Matrix n n ℂ) := by noncomm_ring
          _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, Matrix.mul_assoc _ D, hDw,
                Matrix.mul_one, Units.mul_inv]
      inv_val := by
        calc (V : Matrix n n ℂ) * Matrix.diagonal w * (↑V⁻¹ : Matrix n n ℂ) *
              ((V : Matrix n n ℂ) * D * (↑V⁻¹ : Matrix n n ℂ))
            = (V : Matrix n n ℂ) * Matrix.diagonal w * ((↑V⁻¹ : Matrix n n ℂ) *
                (V : Matrix n n ℂ)) * D * (↑V⁻¹ : Matrix n n ℂ) := by noncomm_ring
          _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, Matrix.mul_assoc _ (Matrix.diagonal w),
                hwD, Matrix.mul_one, Units.mul_inv] }
  have hunit : IsUnit (algebraMap ℂ (Matrix n n ℂ) μ -
      (V : Matrix n n ℂ) * Matrix.diagonal lam * (↑V⁻¹ : Matrix n n ℂ)) :=
    hshift ▸ U.isUnit
  have hexcl := one_le_norm_inverse_mul_norm_of_mem_spectrum_add hμ hunit
  rw [hshift, show (V : Matrix n n ℂ) * D * (↑V⁻¹ : Matrix n n ℂ) = (U : Matrix n n ℂ) from rfl,
    Ring.inverse_unit] at hexcl
  -- a largest entry of `w`
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖w i‖
  have hw : ‖w‖ ≤ ‖w i₀‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi₀
  have hUinv : ‖(↑U⁻¹ : Matrix n n ℂ)‖ ≤
      ‖(V : Matrix n n ℂ)‖ * ‖w i₀‖ * ‖(↑V⁻¹ : Matrix n n ℂ)‖ := by
    change ‖(V : Matrix n n ℂ) * Matrix.diagonal w * (↑V⁻¹ : Matrix n n ℂ)‖ ≤ _
    calc _ ≤ ‖(V : Matrix n n ℂ) * Matrix.diagonal w‖ * ‖(↑V⁻¹ : Matrix n n ℂ)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(V : Matrix n n ℂ)‖ * ‖Matrix.diagonal w‖ * ‖(↑V⁻¹ : Matrix n n ℂ)‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ _ := by rw [Matrix.l2_opNorm_diagonal]; gcongr
  have hpos : 0 < ‖μ - lam i₀‖ := norm_pos_iff.2 (hne i₀)
  have hwi : ‖w i₀‖ = ‖μ - lam i₀‖⁻¹ := norm_inv _
  have : 1 ≤ K * ‖μ - lam i₀‖⁻¹ := by
    calc (1 : ℝ) ≤ ‖(↑U⁻¹ : Matrix n n ℂ)‖ * ‖E‖ := hexcl
      _ ≤ ‖(V : Matrix n n ℂ)‖ * ‖w i₀‖ * ‖(↑V⁻¹ : Matrix n n ℂ)‖ * ‖E‖ := by gcongr
      _ = K * ‖μ - lam i₀‖⁻¹ := by rw [hwi]; ring
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul] at this
  exact absurd (hcon i₀) (not_lt.2 this)

end MathlibExt.Analysis.Matrix.BauerFikeDiagonalizable
