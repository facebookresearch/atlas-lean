/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.CubicHarmonicStability

open MvPolynomial

/-- Exact-source consumer: the original let-bound operator form. -/
theorem exactSource (τ τ₃ : ℝ) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ →
        Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) →
        MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) →
        MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) *
          (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) →
        MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) *
          (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₂ p) ∈ S₀ ∧ same₂ (Ξ ν₁₂ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₂ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ S₁) ∧
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₃ p) ∈ S₀ ∧ same₂ (Ξ ν₁₃ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 :
        MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₃ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ S₁) :=
  cubicBottom_mem_of_transitionStable_degree_le_two τ τ₃

/-- Boundary example: for `S₀ = S₂ = ⊥` the stability hypotheses of the first
component hold (every operator sends `0` into `⊥`), the conclusion
`1 ∈ S₀` is false, and the theorem therefore forces precisely the
nontriviality antecedent `S₀ ≠ ⊥ ∨ S₂ ≠ ⊥` to fail. -/
example (τ τ₃ : ℝ) :
    ¬ ((⊥ : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) ≠ ⊥ ∨
      (⊥ : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) ≠ ⊥) := by
  have hstab : ∀ p ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin 3) ℂ)),
      cubicLowerTwo (cubicXi (cubicNu12 τ τ₃) p) ∈
        (⊥ : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) ∧
      cubicSameTwo (cubicXi (cubicNu12 τ τ₃) p) ∈
        (⊥ : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) := by
    intro p hp
    rw [Submodule.mem_bot] at hp
    subst hp
    simp [cubicXi, cubicLowerTwo, cubicSameTwo]
  have h := (cubicBottom_mem_of_transitionStable_degree_le_two τ τ₃).1
    ⊥ ⊥ bot_le bot_le hstab
  intro hn
  have h1 := h hn
  simp at h1

/-- The scalar factor in the `X_0 X_1` lowering is nonzero at `cubicNu12`,
so the `X_2` conclusion is not vacuous. -/
example (τ τ₃ : ℝ) : cubicNu12 τ τ₃ 0 - cubicNu12 τ τ₃ 1 - 1 ≠ 0 := by
  have h : (cubicNu12 τ τ₃ 0 - cubicNu12 τ τ₃ 1 - 1).re ≠ 0 := by
    simp [cubicNu12]; norm_num
  exact fun hz => h (by simp [hz])
