/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DirichletPartialSum

/-!
# Tests for partial sums of Dirichlet `L`-functions

The averages `∑_{χ ≠ 1} L(σ, χ)` at the boundary moduli `q = 1, 2` (where the sum is empty),
additivity of `ZMod.LFunction`, and the short-sum approximation of `L(1, χ)`.
-/

@[expose] public section

open Finset

namespace DirichletPartialSumTest

open scoped Classical in
/-- `q = 1`: the sum over nontrivial characters is empty and `φ(1) = 1`. -/
example : (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ 1), DirichletCharacter.LFunction χ 1) =
    0 := by
  rw [Finset.sum_eq_zero]
  intro χ hχ
  exact absurd (DirichletCharacter.level_one χ) (Finset.ne_of_mem_erase hχ)

open scoped Classical in
example : ‖(∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ 1), DirichletCharacter.LFunction χ 1) -
    (Nat.totient 1 : ℂ)‖ ≤ 5 + Real.log ((1 : ℕ) : ℝ) :=
  DirichletCharacter.norm_sum_LFunction_one_sub_totient_le (q := 1)

open scoped Classical in
example {q : ℕ} [NeZero q] : ‖(∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
    DirichletCharacter.LFunction χ (1 / 2 : ℝ)) - (q.totient : ℂ)‖ ≤ 7 * (q : ℝ) :=  by
  have h := DirichletCharacter.norm_sum_LFunction_sub_totient_le (q := q) (σ := 1 / 2)
    (by norm_num) (by norm_num)
  rwa [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, Real.rpow_one] at h

/-- `ZMod.LFunction` is additive. -/
example {q : ℕ} [NeZero q] (Φ Ψ : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j ↦ Φ j + Ψ j) s = ZMod.LFunction Φ s + ZMod.LFunction Ψ s := by
  have h := ZMod.LFunction_sum {0, 1} (fun i : Fin 2 => if i = 0 then Φ else Ψ) s
  simpa [Finset.sum_pair] using h

/-- `L(1, χ)` from a short sum, at `x = 1`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1 - χ 1‖ ≤ 4 * Real.sqrt q * (1 + Real.log q) := by
  have h := DirichletCharacter.norm_LFunction_one_sub_sum_Icc_le hχ (x := 1) le_rfl
  simpa using h

/-- The consecutive-power bound at `w = 1`, `n = 1`: `‖1 - 1/2‖ ≤ 1 · 1^{-2}`. -/
example : ‖((1 : ℕ) : ℂ) ^ (-(1 : ℂ)) - ((1 + 1 : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
    ‖(1 : ℂ)‖ * ((1 : ℕ) : ℝ) ^ (-(1 : ℂ).re - 1) :=
  Complex.norm_natCast_cpow_neg_sub_succ_le' (by norm_num) le_rfl

end DirichletPartialSumTest
