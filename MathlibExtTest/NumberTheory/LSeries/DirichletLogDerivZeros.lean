/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DirichletLogDerivZeros
import MathlibExt.NumberTheory.LSeries.RiemannXiZeros

/-!
# Tests for `L'/L` and the zeros of `ξ(s, χ)`

The enumeration hypothesis `∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w` is
satisfiable both for primitive `χ ≠ 1` and, through `analyticOrderAt_xi_modOne_eq`, for the
character mod `1` (where `xi χ = Λ` is not entire); the uniform zero-counting bounds can be
instantiated at such families.
-/

@[expose] public section

open DirichletCharacter RiemannXi

namespace DirichletLogDerivZerosTest

/-- For the character mod `1` the orders of `ξ(s, χ) = Λ(s)` are those of the Riemann `ξ`; in
particular `0` and `1` (poles of `Λ`) have order `0`. -/
example (χ : DirichletCharacter ℂ 1) :
    analyticOrderAt (xi χ) 0 = 0 ∧ analyticOrderAt (xi χ) 1 = 0 := by
  rw [analyticOrderAt_xi_modOne_eq, analyticOrderAt_xi_modOne_eq]
  constructor <;>
    exact (differentiable_riemannXi.analyticAt _).analyticOrderAt_eq_zero.mpr
      (by simp [riemannXi_zero, riemannXi_one])

/-- An enumeration for the character mod `1`. -/
example (χ : DirichletCharacter ℂ 1) :
    ∃ (ι : Type) (z : ι → ℂ), ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  exact ⟨ι, z, fun w => by rw [hz, analyticOrderAt_xi_modOne_eq]⟩

/-- An enumeration for primitive `χ ≠ 1`, and it lists exactly the nontrivial zeros. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∃ (ι : Type) (z : ι → ℂ), (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) ∧
      Set.range z = χ.nontrivialZeros := by
  have hz := Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1)
  refine ⟨_, _, hz, Set.Subset.antisymm ?_ fun ρ hρ =>
    exists_eq_of_card_eq_analyticOrderAt hχ hχ1 hz hρ⟩
  rintro _ ⟨n, rfl⟩
  exact mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz n

/-- A primitive trivial character has modulus `1`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (h : χ = 1) :
    q = 1 :=
  eq_one_of_isPrimitive_of_eq_one hχ h

/-- The uniform local zero count, instantiated at the character mod `1`. -/
example : ∃ C : ℝ, ∃ (ι : Type) (z : ι → ℂ), ∀ t : ℝ, ∀ F : Finset ι,
    (∀ n ∈ F, |t - (z n).im| < 1) → (F.card : ℝ) ≤ C * Real.log (1 * (|t| + 2)) := by
  obtain ⟨C, hC⟩ := exists_card_le_log_of_abs_sub_im_lt.{0}
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  refine ⟨C, ι, z, ?_⟩
  have := hC (1 : DirichletCharacter ℂ 1) isPrimitive_one_level_one z
    (fun w => by rw [hz, analyticOrderAt_xi_modOne_eq])
  simpa using this

/-- Finitely many nontrivial zeros below any height. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (T : ℝ) : {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T}.Finite :=
  finite_setOf_mem_nontrivialZeros_abs_im_lt hχ hχ1 T

end DirichletLogDerivZerosTest
