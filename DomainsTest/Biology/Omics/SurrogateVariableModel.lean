/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.SurrogateVariableModel
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Matrix Domains.Biology.Omics.SurrogateVariableModel

namespace DomainsTest.Biology.Omics.SurrogateVariableModel

/-! ### The expression matrix, from the definition

Two genes and two arrays, a numerical primary variable `y = (1, -1)` with linear effects
`f i t = β i * t`, `β = (3, 0)`, baselines `μ = (1, 2)`, one unmodeled factor with effect
`g 0 = (1, 0)` across the arrays and coefficients `γ 0 = (2, 5)`, and no noise. -/

example :
    expression ![1, 2] (fun i (t : ℝ) => ![3, 0] i * t) ![1, -1] ![![2, 5]] ![![1, 0]] 0 =
      !![6, -2; 7, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [expression]

/-- With no unmodeled factors (`L = 0`) the model is the primary-variable model
`x i j = μ i + f i (y j) + e i j`, here linear in the primary variable. -/
example {m n : ℕ} (μ β : Fin m → ℝ) (y : Fin n → ℝ) (γ : Fin 0 → Fin m → ℝ)
    (g : Fin 0 → Fin n → ℝ) (e : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    expression μ (fun i t => β i * t) y γ g e i j = μ i + β i * y j + e i j := by
  simp

/-! ### Two factors with the same effect give one surrogate variable

Two genes, two arrays and `L = 2` factors with the same effect `(1, 0)` across the arrays, both
affecting only gene `0`: the heterogeneity matrix is `diag(2, 0) = 1 * diag(2, 0) * 1ᵀ`, a
singular value decomposition with `σ = (2, 0)`. One singular value is nonzero, so one surrogate
variable represents both factors. -/

section Collapse

def γ₂ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![1, 0]]

def g₂ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![1, 0]]

def σ₂ : Fin 2 → ℝ := ![2, 0]

theorem σ₂_eq_zero : ∀ j : Fin 2, 2 ≤ j.val → σ₂ j = 0 := by
  intro j hj
  fin_cases j <;> simp at hj

theorem heterogeneity₂_eq :
    of (fun i j => ∑ ℓ, γ₂ ℓ i * g₂ ℓ j) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * of (fun i j => if i.val = j.val then σ₂ j else 0) *
        (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [γ₂, g₂, σ₂, Fin.sum_univ_two]

theorem card_σ₂ : Fintype.card {k // σ₂ k ≠ 0} = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simp [σ₂]⟩, fun ⟨k, hk⟩ => ?_⟩
  fin_cases k
  · rfl
  · simp [σ₂] at hk

-- The theorem's bound `K ≤ L = 2` holds, and the count of surrogate variables is `1 < 2`.
example : Fintype.card {k // σ₂ k ≠ 0} ≤ 2 ∧ Fintype.card {k // σ₂ k ≠ 0} < 2 :=
  ⟨(surrogateVariables_of_svd γ₂ g₂ 1 1 σ₂ (one_mem _) (one_mem _) σ₂_eq_zero
    heterogeneity₂_eq).1, by rw [card_σ₂]; norm_num⟩

end Collapse

/-! ### A right singular vector that is not a coordinate axis

One gene, two arrays and one factor with effect `(0, 3)` and coefficient `1`: the heterogeneity
matrix `(0  3)` is `1 * (3  0) * Vᵀ` with `V` the swap of the two coordinates, a singular value
decomposition with `σ = (3, 0)`. The surrogate variable is the first column `(0, 1)` of `V`. -/

section Swap

def γ₁ : Fin 1 → Fin 1 → ℝ := ![![1]]

def g₁ : Fin 1 → Fin 2 → ℝ := ![![0, 3]]

def σ₁ : Fin 2 → ℝ := ![3, 0]

def V₁ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem V₁_mem : V₁ ∈ orthogonalGroup (Fin 2) ℝ := by
  rw [mem_orthogonalGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [V₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₁_eq_zero : ∀ j : Fin 2, 1 ≤ j.val → σ₁ j = 0 := by
  intro j hj
  fin_cases j
  · simp at hj
  · simp [σ₁]

theorem heterogeneity₁_eq :
    of (fun i j => ∑ ℓ, γ₁ ℓ i * g₁ ℓ j) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * of (fun i j => if i.val = j.val then σ₁ j else 0) *
        V₁ᵀ := by
  ext i j
  fin_cases i
  fin_cases j <;> norm_num [γ₁, g₁, σ₁, V₁, Matrix.mul_apply, Fin.sum_univ_two]

-- The theorem applies: at most one surrogate variable, a unit vector.
example : Fintype.card {k // σ₁ k ≠ 0} ≤ 1 ∧
    ∀ k : {k // σ₁ k ≠ 0}, ∑ j, V₁ j k * V₁ j k = 1 := by
  obtain ⟨hcard, horth, -⟩ :=
    surrogateVariables_of_svd γ₁ g₁ 1 V₁ σ₁ (one_mem _) V₁_mem σ₁_eq_zero heterogeneity₁_eq
  exact ⟨hcard, fun k => by simpa using horth k k⟩

-- The right singular vector with the nonzero singular value is `(0, 1)`, and with the coefficient
-- `(U Σ) 0 0 = 3` it gives back the heterogeneity `(0, 3)`.
example : (fun j => V₁ j 0) = ![0, 1] ∧
    ∀ j, ∑ ℓ, γ₁ ℓ 0 * g₁ ℓ j =
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *
        of (fun (i : Fin 1) (j : Fin 2) => if i.val = j.val then σ₁ j else 0)) 0 0 * V₁ j 0 := by
  refine ⟨?_, ?_⟩
  · ext j
    fin_cases j <;> simp [V₁]
  · intro j
    fin_cases j <;> norm_num [γ₁, g₁, σ₁, V₁, Matrix.mul_apply]

end Swap

/-! ### Boundary cases of the surrogate variable lemma -/

-- With no unmodeled factors there are no surrogate variables.
example {m n : ℕ} (γ : Fin 0 → Fin m → ℝ) (g : Fin 0 → Fin n → ℝ) :
    ∃ (h : Fin 0 → Fin n → ℝ) (lam : Fin 0 → Fin m → ℝ),
      ∀ i j, ∑ ℓ, γ ℓ i * g ℓ j = ∑ k, lam k i * h k j := by
  obtain ⟨K, h, lam, hKL, -, -, hrep⟩ := exists_surrogateVariables γ g
  obtain rfl : K = 0 := Nat.le_zero.mp hKL
  exact ⟨h, lam, hrep⟩

-- Three factors on two arrays: at most two orthonormal surrogate variables represent them, in
-- the model as in the heterogeneity.
example {m : ℕ} {Y : Type*} (μ : Fin m → ℝ) (f : Fin m → Y → ℝ) (y : Fin 2 → Y)
    (γ : Fin 3 → Fin m → ℝ) (g : Fin 3 → Fin 2 → ℝ) (e : Fin m → Fin 2 → ℝ) :
    ∃ K ≤ 2, ∃ (h : Fin K → Fin 2 → ℝ) (lam : Fin K → Fin m → ℝ),
      (∀ k k', ∑ j, h k j * h k' j = if k = k' then 1 else 0) ∧
        expression μ f y γ g e = expression μ f y lam h e := by
  obtain ⟨K, h, lam, -, hKn, horth, heq⟩ := exists_expression_eq μ f y γ g e
  exact ⟨K, hKn, h, lam, horth, heq⟩

end DomainsTest.Biology.Omics.SurrogateVariableModel
