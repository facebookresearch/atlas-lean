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

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Diagonal unitary phase matrices

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. Negating angles gives D(-θ)=D(θ)ᴴ
and zero angles give I. For finite I, D(θ) is unitary and D(θ+η)=D(θ)D(η). The phase
convention is exp(iθ).
-/

@[expose] public section

open Matrix Complex ComplexConjugate

namespace Matrix

variable {n : Type*} [DecidableEq n]

/-- **Diagonal phase matrix.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. This defines diagonalPhase θ for
any index type I.
-/
noncomputable def diagonalPhase (θ : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I))

private theorem star_exp_eq (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  calc star (Complex.exp z) = conj (Complex.exp z) := rfl
    _ = Complex.exp (conj z) := by rw [← Complex.exp_conj]
    _ = Complex.exp (star z) := rfl

private theorem star_mul_I_ofReal (r : ℝ) :
    star ((r : ℂ) * Complex.I) = -((r : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [mul_re, ofReal_re, ofReal_im, I_re, I_im]
  · simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]

omit [DecidableEq n] in
private theorem diagonalPhase_star_entry (θ : n → ℝ) (i : n) :
    star (Complex.exp ((θ i : ℂ) * Complex.I)) =
      Complex.exp (-((θ i : ℂ) * Complex.I)) := by
  rw [star_exp_eq, star_mul_I_ofReal]

private theorem diagonalPhase_mul_conjTranspose [Fintype n] (θ : n → ℝ) :
    diagonalPhase θ * (diagonalPhase θ)ᴴ = 1 := by
  unfold diagonalPhase
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, one_apply_eq]
    have h_mul : Complex.exp ((θ i : ℂ) * Complex.I) *
        star (Complex.exp ((θ i : ℂ) * Complex.I)) = 1 := by
      rw [diagonalPhase_star_entry, ← Complex.exp_add]
      have : ((θ i : ℂ) * Complex.I) + -((θ i : ℂ) * Complex.I) = 0 := by ring
      rw [this, Complex.exp_zero]
    exact h_mul
  · simp only [diagonal_apply_ne _ hij, one_apply_ne hij]

private theorem diagonalPhase_conjTranspose_mul [Fintype n] (θ : n → ℝ) :
    (diagonalPhase θ)ᴴ * diagonalPhase θ = 1 := by
  unfold diagonalPhase
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, one_apply_eq]
    have h_mul : star (Complex.exp ((θ i : ℂ) * Complex.I)) *
        Complex.exp ((θ i : ℂ) * Complex.I) = 1 := by
      rw [diagonalPhase_star_entry, ← Complex.exp_add]
      have : -((θ i : ℂ) * Complex.I) + ((θ i : ℂ) * Complex.I) = 0 := by ring
      rw [this, Complex.exp_zero]
    exact h_mul
  · simp only [diagonal_apply_ne _ hij, one_apply_ne hij]

/-- **Entry formula for a diagonal phase matrix.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. For i,j∈I, diagonalPhase θ i j is
exp(iθ_i) when i=j and zero otherwise.
-/
theorem diagonalPhase_apply (θ : n → ℝ) (i j : n) :
    diagonalPhase θ i j =
      if i = j then Complex.exp ((θ i : ℂ) * Complex.I) else 0 := by
  unfold diagonalPhase
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- **Zero angles give the identity.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. The equality diagonalPhase(θ≡0)=I
holds on any index type.
-/
theorem diagonalPhase_zero :
    diagonalPhase (n := n) (fun _ => (0 : ℝ)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diagonalPhase]
  · simp [diagonalPhase, hij]

/-- **Addition of angles gives multiplication of phase matrices.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. For finite I and θ,η:I→ℝ,
D(θ+η)=D(θ)*D(η).
-/
theorem diagonalPhase_add [Fintype n] (θ₁ θ₂ : n → ℝ) :
    diagonalPhase (fun i => θ₁ i + θ₂ i) =
      diagonalPhase θ₁ * diagonalPhase θ₂ := by
  unfold diagonalPhase
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  have h : ((θ₁ i + θ₂ i : ℝ) : ℂ) * Complex.I =
      ((θ₁ i : ℂ) * Complex.I) + ((θ₂ i : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add]

/-- **Negated phase angles give the conjugate transpose.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. For any I, D(-θ)=D(θ)ᴴ.
-/
theorem diagonalPhase_neg (θ : n → ℝ) :
    diagonalPhase (fun i => -θ i) = (diagonalPhase θ)ᴴ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonalPhase, diagonal_apply_eq, diagonal_conjTranspose,
      diagonal_apply_eq, Pi.star_apply]
    have h1 : ((-θ i : ℝ) : ℂ) * Complex.I =
        -((θ i : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h1, ← diagonalPhase_star_entry]
  · have hij' : j ≠ i := Ne.symm hij
    simp [diagonalPhase_apply, hij, hij', conjTranspose_apply]

/-- **Conjugate transpose of a phase matrix.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. For any I, D(θ)ᴴ=D(-θ).
-/
theorem diagonalPhase_conjTranspose_eq_neg (θ : n → ℝ) :
    (diagonalPhase θ)ᴴ = diagonalPhase (fun i => -θ i) :=
  (diagonalPhase_neg θ).symm

/-- **Unitarity of finite phase matrices.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. When I is finite, D(θ) belongs to
the unitary group U(I,ℂ).
-/
theorem diagonalPhase_mem_unitary [Fintype n] (θ : n → ℝ) :
    diagonalPhase θ ∈ unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact diagonalPhase_mul_conjTranspose θ

/-- **Phase angles as a unitary-group element.**

For an index type I and real angles θ:I→ℝ, let D(θ)=diagonalPhase θ be the complex diagonal
matrix with D(θ)_(i,i)=exp(iθ_i) and zero off the diagonal. For finite I, diagonalPhaseU
θ∈U(I,ℂ) is the unitary with underlying matrix D(θ).
-/
noncomputable def diagonalPhaseU [Fintype n] (θ : n → ℝ) : unitaryGroup n ℂ :=
  ⟨diagonalPhase θ, diagonalPhase_mem_unitary θ⟩

@[simp]
theorem diagonalPhaseU_val [Fintype n] (θ : n → ℝ) :
    (diagonalPhaseU θ : Matrix n n ℂ) = diagonalPhase θ :=
  rfl

theorem diagonalPhaseU_mul [Fintype n] (θ₁ θ₂ : n → ℝ) :
    diagonalPhaseU (fun i => θ₁ i + θ₂ i) =
      diagonalPhaseU θ₁ * diagonalPhaseU θ₂ := by
  apply Subtype.ext
  exact diagonalPhase_add θ₁ θ₂

theorem diagonalPhaseU_zero [Fintype n] :
    diagonalPhaseU (n := n) (fun _ => (0 : ℝ)) = 1 := by
  apply Subtype.ext
  exact diagonalPhase_zero

theorem diagonalPhaseU_inv [Fintype n] (θ : n → ℝ) :
    (diagonalPhaseU θ)⁻¹ = diagonalPhaseU (fun i => -θ i) := by
  apply Subtype.ext
  calc (↑(diagonalPhaseU θ)⁻¹ : Matrix n n ℂ) = star (diagonalPhase θ) := rfl
    _ = (diagonalPhase θ)ᴴ := rfl
    _ = diagonalPhase (fun i => -θ i) := (diagonalPhase_neg θ).symm

end Matrix
