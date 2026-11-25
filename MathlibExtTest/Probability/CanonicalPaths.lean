/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CanonicalPaths

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for canonical paths and the spectral gap

The two-state chain that stays with probability `3/4` and switches with probability `1/4` is
reversible for the uniform distribution and has eigenvalues `1` and `1/2` (eigenvector `(1, -1)`).
With the direct paths `γ x y = [y]` every edge load is `1/4 = 2 · Q(0, 1)`, so `B = 2`, and
Sinclair's Theorem 5 gives `μ ≤ 1 - 1/2 = 1/2`: the bound is attained, which shows the hypotheses
are jointly satisfiable and the conclusion is sharp.
-/

set_option autoImplicit false

open Matrix
open MathlibExt.Probability.CanonicalPaths

namespace MathlibExtTest.Probability.CanonicalPaths

/-- Stay with probability `3/4`, switch with probability `1/4`. -/
noncomputable def P₂ : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 3 / 4 else 1 / 4

/-- The uniform distribution on two states. -/
noncomputable def unif : Fin 2 → ℝ := fun _ => 1 / 2

/-- Direct canonical paths: from `x` go straight to `y`. -/
def direct : Fin 2 → Fin 2 → List (Fin 2) := fun _ y => [y]

theorem unif_pos : ∀ x, 0 < unif x := fun _ => by norm_num [unif]

theorem unif_sum : ∑ x, unif x = 1 := by norm_num [unif, Fin.sum_univ_two]

theorem P₂_row : ∀ x, ∑ y, P₂ x y = 1 := by
  intro x; fin_cases x <;> norm_num [P₂, Fin.sum_univ_two]

theorem P₂_rev : ∀ x y, unif x * P₂ x y = unif y * P₂ y x := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [P₂, unif]

theorem direct_end : ∀ x y, x ≠ y → pathEnd x (direct x y) = y := by
  intro x y _; rfl

theorem direct_load : ∀ u v, pathLoad unif direct u v ≤ 2 * (unif u * P₂ u v) := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    norm_num [pathLoad, direct, pathEdges, unif, P₂, Fin.sum_univ_two]

theorem direct_elongatedLoad :
    ∀ u v, elongatedPathLoad unif direct u v ≤ 2 * (unif u * P₂ u v) := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    norm_num [elongatedPathLoad, direct, pathEdges, unif, P₂, Fin.sum_univ_two]

/-- The eigenvector `(1, -1)` with eigenvalue `1/2`. -/
noncomputable def f₂ : Fin 2 → ℝ := ![1, -1]

theorem f₂_ne : f₂ ≠ 0 := by
  intro h; have := congrFun h 0; norm_num [f₂] at this

theorem f₂_eig : P₂ *ᵥ f₂ = (1 / 2 : ℝ) • f₂ := by
  ext i; fin_cases i <;> norm_num [P₂, f₂, mulVec, dotProduct, Fin.sum_univ_two]

/-- Theorem 5 on the example: `1 ≤ 2 (1 - 1/2)`, an equality. -/
example : (1 : ℝ) ≤ 2 * (1 - 1 / 2) :=
  one_le_mul_one_sub_of_eigenvector unif_pos unif_sum P₂_row P₂_rev direct direct_end
    direct_elongatedLoad f₂_ne f₂_eig (by norm_num)

/-- Theorem 5 in the form `μ ≤ 1 - 1/ρ̄`: `1/2 ≤ 1 - 1/2`. -/
example : (1 / 2 : ℝ) ≤ 1 - 1 / 2 :=
  le_one_sub_inv_of_eigenvector unif_pos unif_sum P₂_row P₂_rev direct direct_end
    (by norm_num) direct_elongatedLoad f₂_ne f₂_eig (by norm_num)

/-- Corollary 6 with `ℓ = 1`, `ρ = 2`. -/
example : (1 / 2 : ℝ) ≤ 1 - 1 / (2 * (1 : ℕ)) :=
  le_one_sub_inv_mul_of_eigenvector unif_pos unif_sum P₂_row P₂_rev direct direct_end
    (fun _ _ _ => le_rfl) (by norm_num) direct_load f₂_ne f₂_eig (by norm_num)

/-- The cut bound (13) on `A = {0}`: `π(A) π(Aᶜ) = 1/4 ≤ 2 · Q(A, Aᶜ) = 1/4`. -/
example : (∑ x ∈ ({0} : Finset (Fin 2)), unif x) * (∑ y ∈ ({0} : Finset (Fin 2))ᶜ, unif y) ≤
    2 * ∑ u ∈ ({0} : Finset (Fin 2)), ∑ v ∈ ({0} : Finset (Fin 2))ᶜ, unif u * P₂ u v :=
  mul_sum_compl_le_of_pathLoad_le (fun x => (unif_pos x).le) P₂ direct direct_end direct_load _

/-- Theorem 3 on `A = {0}`: `π(A) = 1/2 ≤ 2 · 2 · Q(A, Aᶜ) = 1/2`. -/
example : ∑ x ∈ ({0} : Finset (Fin 2)), unif x ≤
    2 * (2 * ∑ u ∈ ({0} : Finset (Fin 2)), ∑ v ∈ ({0} : Finset (Fin 2))ᶜ, unif u * P₂ u v) :=
  sum_le_two_mul_of_pathLoad_le (fun x => (unif_pos x).le) unif_sum P₂ direct direct_end
    direct_load _ (by norm_num [unif])

/-- Telescoping along a three-edge path. -/
example (ψ : Fin 3 → ℝ) :
    ((pathEdges 0 [1, 2, 0]).map fun e => ψ e.2 - ψ e.1).sum = 0 := by
  rw [sum_pathEdges_sub]; simp [pathEnd]

/-- The Poincaré inequality with an arbitrary test function on the example. -/
example (ψ : Fin 2 → ℝ) :
    ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (unif x * unif y) ≤
      2 * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (unif x * P₂ x y) :=
  sum_sq_sub_mul_le_of_elongatedPathLoad_le (fun x => (unif_pos x).le) P₂ direct direct_end
    direct_elongatedLoad ψ

end MathlibExtTest.Probability.CanonicalPaths
