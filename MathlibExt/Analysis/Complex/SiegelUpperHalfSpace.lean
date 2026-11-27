/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# The Siegel upper half space and Siegel's fundamental domain

For an integer `g ≥ 1`, the Siegel upper half space `𝔖_g` is the set of symmetric `g × g` complex
matrices `τ = X + iY` whose imaginary part `Y = Im τ` is positive definite. The group
`Sp_{2g}(ℤ)` of integral `2g × 2g` matrices `γ` with `ᵗγ J γ = J`, `J = (0 1; -1 0)`, acts by
`γ · τ = (α τ + β)(λ τ + μ)⁻¹`, with `α, β, λ, μ` the `g × g` blocks of `γ`. Siegel's fundamental
domain `𝔉_g` is the set of `τ ∈ 𝔖_g` satisfying the conditions S. 1–S. 3 of
F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), §2.1.

## Main definitions

* `Siegel.upperHalfSpace g`: `𝔖_g`, as a set of matrices `Matrix (Fin g) (Fin g) ℂ`.
* `Siegel.Sp g`: the carrier of Mathlib's `Matrix.symplecticGroup (Fin g) ℤ`;
  `Siegel.mem_Sp_iff`: these are the integral matrices `γ` with `ᵗγ J γ = J` for
  `J = (0 1; -1 0)` (Mathlib's `J` is `(0 -1; 1 0) = -J`).
* `Siegel.smul γ τ`: the matrix `(α τ + β)(λ τ + μ)⁻¹`, with Mathlib's matrix inverse.
* `Siegel.fundamentalDomain g`: `𝔉_g`.

## Main results

* `Siegel.mem_upperHalfSpace_one_iff`: for `g = 1`, `𝔖_1` is the upper half-plane.
* `Siegel.siegelS3_of_eq_one`: for `g = 1`, condition S. 3 holds for every `τ`.
-/

@[expose] public section

open Matrix

namespace Siegel

variable (g : ℕ)

/-- **The Siegel upper half space** `𝔖_g`: the symmetric `g × g` complex matrices `τ` whose
imaginary part `Im τ` (entrywise) is positive definite. -/
def upperHalfSpace : Set (Matrix (Fin g) (Fin g) ℂ) :=
  {τ | τ.IsSymm ∧ (τ.map Complex.im).PosDef}

/-- The matrix `J = (0 1; -1 0)` of size `2g`, with blocks indexed by `Fin g ⊕ Fin g`. -/
def J : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks 0 1 (-1) 0

/-- **The integral symplectic group** `Sp_{2g}(ℤ)`, as a set of integral `2g × 2g` matrices: the
carrier of Mathlib's `Matrix.symplecticGroup (Fin g) ℤ`. By `Siegel.mem_Sp_iff`, these are the
matrices `γ` with `ᵗγ J γ = J`, `J = (0 1; -1 0)`. -/
def Sp : Set (Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :=
  Matrix.symplecticGroup (Fin g) ℤ

theorem J_eq_neg : J g = -Matrix.J (Fin g) ℤ := by
  simp [J, Matrix.J, fromBlocks_neg]

/-- `Sp_{2g}(ℤ)` is the set of integral `2g × 2g` matrices `γ` with `ᵗγ J γ = J`,
`J = (0 1; -1 0)`. (Mathlib's `Matrix.symplecticGroup` is defined with `(0 -1; 1 0) = -J`.) -/
theorem mem_Sp_iff (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    γ ∈ Sp g ↔ γᵀ * J g * γ = J g := by
  rw [Sp, SetLike.mem_coe, SymplecticGroup.mem_iff', J_eq_neg, Matrix.mul_neg, Matrix.neg_mul,
    neg_inj]

/-- `Sp_{2g}(ℤ)` is Mathlib's `Matrix.symplecticGroup (Fin g) ℤ`. -/
theorem mem_Sp_iff_mem_symplecticGroup (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    γ ∈ Sp g ↔ γ ∈ Matrix.symplecticGroup (Fin g) ℤ :=
  Iff.rfl

variable {g}

/-- The matrix `γ · τ = (α τ + β)(λ τ + μ)⁻¹`, for an integral `2g × 2g` matrix `γ` with blocks
`α, β, λ, μ` and a `g × g` complex matrix `τ`. For `γ ∈ Sp_{2g}(ℤ)` and `τ ∈ 𝔖_g` this is the
action of `Sp_{2g}(ℤ)` on `𝔖_g` (Pazuki, §2.1); the definition is the formula for all `γ` and
`τ`, with Mathlib's `Matrix.inv` (zero for a singular matrix). -/
noncomputable def smul (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  ((γ.toBlocks₁₁.map (Int.cast : ℤ → ℂ)) * τ + γ.toBlocks₁₂.map (Int.cast : ℤ → ℂ)) *
    ((γ.toBlocks₂₁.map (Int.cast : ℤ → ℂ)) * τ + γ.toBlocks₂₂.map (Int.cast : ℤ → ℂ))⁻¹

/-- **Condition S. 1** of Siegel's fundamental domain: `det(Im(γ · τ)) ≤ det(Im τ)` for every
`γ ∈ Sp_{2g}(ℤ)`. -/
def SiegelS1 (τ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ γ ∈ Sp g, ((smul γ τ).map Complex.im).det ≤ (τ.map Complex.im).det

/-- **Condition S. 2** of Siegel's fundamental domain: `|Re(τ_{i,j})| ≤ 1/2` for all `i, j`. -/
def SiegelS2 (τ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ i j, |(τ i j).re| ≤ 1 / 2

/-- **Condition S. 3** of Siegel's fundamental domain, with zero-based indices
`Fin g = {0, …, g - 1}`: for every `k < g` and every `ξ ∈ ℤ^g` with `gcd(ξ_j : k ≤ j < g) = 1`,
`ᵗξ (Im τ) ξ ≥ Im(τ_{k,k})`; and `Im(τ_{k,k+1}) ≥ 0` for every `k` with `k + 1 < g`. In Pazuki's
one-based indices these read `gcd(ξ_k, …, ξ_g) = 1` for `1 ≤ k ≤ g`, and `Im(τ_{k,k+1}) ≥ 0` for
`1 ≤ k ≤ g - 1`. -/
def SiegelS3 (τ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  (∀ (k : Fin g) (ξ : Fin g → ℤ), (Finset.univ.filter (k ≤ ·)).gcd ξ = 1 →
      (τ k k).im ≤ ∑ i, ∑ j, (ξ i : ℝ) * (τ i j).im * ξ j) ∧
    ∀ (k l : Fin g), l.val = k.val + 1 → 0 ≤ (τ k l).im

variable (g) in
/-- **Siegel's fundamental domain** `𝔉_g`: the `τ ∈ 𝔖_g` satisfying conditions S. 1, S. 2 and
S. 3.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012),
19–49, §2.1, read in arXiv:0907.1458v2 (the Siegel upper half space, the action and the
properties S. 1–S. 3); Pazuki cites J.-I. Igusa, *Theta functions*, Springer, 1972, Chapter V,
§4, for the fundamental domain. -/
def fundamentalDomain : Set (Matrix (Fin g) (Fin g) ℂ) :=
  {τ | τ ∈ upperHalfSpace g ∧ SiegelS1 τ ∧ SiegelS2 τ ∧ SiegelS3 τ}

/-- **For `g = 1`, the Siegel upper half space is the upper half-plane**: a `1 × 1` matrix `τ`
lies in `𝔖_1` if and only if `Im(τ_{0,0}) > 0`. -/
theorem mem_upperHalfSpace_one_iff (τ : Matrix (Fin 1) (Fin 1) ℂ) :
    τ ∈ upperHalfSpace 1 ↔ 0 < (τ 0 0).im := by
  constructor
  · rintro ⟨-, h⟩
    simpa using h.diag_pos (i := 0)
  · intro h
    refine ⟨Matrix.IsSymm.ext fun i j ↦ by fin_cases i; fin_cases j; rfl, ?_⟩
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx ↦ ?_⟩
    · exact Matrix.IsHermitian.ext fun i j ↦ by fin_cases i; fin_cases j; simp
    · have hx0 : x 0 ≠ 0 := fun h0 ↦ hx (funext fun i ↦ by fin_cases i; exact h0)
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply, star_trivial,
        Matrix.map_apply]
      nlinarith [mul_pos (mul_self_pos.mpr hx0) h]

/-- **For `g = 1`, condition S. 3 holds for every `τ`**: the only `ξ ∈ ℤ¹` with `gcd(ξ_0) = 1`
are `ξ = ±1`, for which `ᵗξ (Im τ) ξ = Im(τ_{0,0})`; the second part of S. 3 is vacuous, as no
`k` has `k + 1 < 1`. -/
theorem siegelS3_of_eq_one (τ : Matrix (Fin 1) (Fin 1) ℂ) : SiegelS3 τ := by
  refine ⟨fun k ξ hξ ↦ ?_, fun k l hkl ↦ absurd hkl (by omega)⟩
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  have hfilter : (Finset.univ.filter ((0 : Fin 1) ≤ ·)) = {0} := by decide
  rw [hfilter, Finset.gcd_singleton] at hξ
  have hsq : (ξ 0 : ℝ) * ξ 0 = 1 := by
    have : |ξ 0| = 1 := by rw [Int.abs_eq_normalize]; exact hξ
    rcases abs_eq (zero_le_one' ℤ) |>.mp this with h | h <;> simp [h]
  simp only [Fin.sum_univ_one]
  have : (ξ 0 : ℝ) * (τ 0 0).im * ξ 0 = (τ 0 0).im := by
    rw [mul_right_comm, hsq, one_mul]
  rw [this]

end Siegel
