/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.CyclicSBI

/-!
# Cyclic cochains, Connes' operators and the SBI sequence

Focused checks of the ported cyclic-cohomology API on concrete cochains of `ℚ`:

* the cyclic operator `λ` rotates the arguments with the sign `(-1)ⁿ`, and on the
  multiplication 1-cochain it is `-1`, so its order `n + 1 = 2` is attained;
* the multiplication 1-cochain is symmetric, hence not cyclic, while the zero-degree
  cochains are all cyclic;
* the degree-zero Hochschild coboundary of a commutative algebra vanishes, and the
  relations `b² = 0`, `B² = 0` and `bB + Bb = 0` hold;
* the SBI exactness statements are available over `ℚ` without extra hypotheses.
-/

noncomputable section

namespace MathlibExtTest.RingTheory.CyclicCohomology

open TauCeti

/-- The multiplication `(a₀, a₁) ↦ a₀ a₁` as a `ℚ`-valued 1-cochain of `ℚ`. -/
abbrev mul₁ : MultilinearMap (RingHom.id ℚ) (fun _ : Fin 2 ↦ ℚ) ℚ :=
  MultilinearMap.mkPiAlgebra ℚ (Fin 2) ℚ

/-- The identity `a₀ ↦ a₀` as a `ℚ`-valued 0-cochain of `ℚ`. -/
abbrev id₀ : MultilinearMap (RingHom.id ℚ) (fun _ : Fin 1 ↦ ℚ) ℚ :=
  MultilinearMap.mkPiAlgebra ℚ (Fin 1) ℚ

theorem mul₁_apply (a : Fin 2 → ℚ) : mul₁ a = a 0 * a 1 := by
  simp [mul₁, Fin.prod_univ_two]

theorem mul₁_comp_perm (a : Fin 2 → ℚ) (σ : Equiv.Perm (Fin 2)) : mul₁ (a ∘ σ) = mul₁ a := by
  simp only [mul₁, MultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
  exact Equiv.prod_comp σ a

/-- On the (symmetric) multiplication cochain, `λ = -1`. -/
theorem cyclicOperator_mul₁ : cyclicOperator ℚ ℚ ℚ 1 mul₁ = -mul₁ := by
  refine MultilinearMap.ext fun a ↦ ?_
  rw [cyclicOperator_apply, mul₁_comp_perm]
  simp

/-- `λ` multiplies by `(-1)¹` after rotating the two arguments. -/
example : cyclicOperator ℚ ℚ ℚ 1 mul₁ ![2, 3] = -6 := by
  rw [cyclicOperator_mul₁]
  norm_num

/-- The order of `λ` on 1-cochains is exactly two: `λ² = 1` but `λ ≠ 1`. -/
example : cyclicOperator ℚ ℚ ℚ 1 ^ 2 = 1 := cyclicOperator_pow_eq_one 1

example : cyclicOperator ℚ ℚ ℚ 1 ≠ 1 := by
  intro h
  have h₁ := congrArg (fun f ↦ f mul₁ ![1, 1]) h
  simp only [cyclicOperator_mul₁, Module.End.one_apply] at h₁
  norm_num at h₁

/-- A 1-cochain is cyclic only if it is antisymmetric; multiplication is not. -/
example : mul₁ ∉ cyclicCochains ℚ ℚ ℚ 1 := by
  rw [mem_cyclicCochains_one_iff]
  intro h
  have h₁ := h 1 1
  simp only [mul₁_apply] at h₁
  norm_num at h₁

/-- Every 0-cochain is cyclic. -/
example : id₀ ∈ cyclicCochains ℚ ℚ ℚ 0 := by
  rw [cyclicCochains_zero]
  trivial

/-- For a commutative algebra, `(bφ)(a₀, a₁) = φ(a₀a₁) - φ(a₁a₀)` vanishes. -/
example (a : Fin 2 → ℚ) : hochschildCoboundary ℚ ℚ ℚ 0 id₀ a = 0 := by
  rw [hochschildCoboundary_zero_apply]
  simp [id₀, mul_comm]

example : hochschildCoboundary ℚ ℚ ℚ 1 ∘ₗ hochschildCoboundary ℚ ℚ ℚ 0 = 0 :=
  hochschildCoboundary_comp_hochschildCoboundary ℚ ℚ ℚ

example : connesB ℚ ℚ ℚ 0 ∘ₗ connesB ℚ ℚ ℚ 1 = 0 :=
  connesB_comp_connesB ℚ ℚ ℚ 0

/-- Connes' operator lands in cyclic cochains and kills cyclic cochains. -/
example (φ : MultilinearMap (RingHom.id ℚ) (fun _ : Fin 2 ↦ ℚ) ℚ) :
    connesB ℚ ℚ ℚ 0 φ ∈ cyclicCochains ℚ ℚ ℚ 0 :=
  connesB_mem_cyclicCochains φ

/-- `HH^(m+1) →B HC^m →S HC^(m+2)` is exact over `ℚ`. -/
example (m : ℕ) :
    Function.Exact (hochschildCohomology.connesB ℚ ℚ ℚ m)
      (cyclicCohomology.periodicity ℚ ℚ ℚ m) :=
  cyclicCohomology.exact_connesB_periodicity m

/-- `HC^(m+1) →I HH^(m+1) →B HC^m` is exact once the needed integers are units. -/
example (m : ℕ) :
    Function.Exact (cyclicCohomology.toHochschild ℚ ℚ ℚ (m + 1))
      (hochschildCohomology.connesB ℚ ℚ ℚ m) :=
  cyclicCohomology.exact_toHochschild_connesB m fun q _ ↦
    (Nat.cast_add_one_ne_zero q).isUnit

end MathlibExtTest.RingTheory.CyclicCohomology
