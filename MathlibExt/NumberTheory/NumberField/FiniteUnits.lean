/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

set_option autoImplicit false

/-!
# Finiteness of the unit group of an imaginary quadratic field

The unit group of the ring of integers of an imaginary quadratic field is finite
(`NumberField.Units.finite_of_finrank_eq_two`), by Dirichlet's unit theorem.
-/

namespace NumberField.Units

open scoped NumberField
open NumberField.InfinitePlace

variable {F : Type*} [Field F] [NumberField F]

/-- **The unit group of an imaginary quadratic field is finite.** Let $F$ be a number field with
$[F : \mathbb{Q}] = 2$ and no real places (`NumberField.IsTotallyComplex F`). Then the unit group
of its ring of integers is finite.

By Dirichlet's unit theorem the unit rank is the number of infinite places minus one, here
$1 - 1 = 0$, so every unit is a root of unity.

Source: K. Conrad, *Dirichlet's unit theorem*, Theorem 1.1 (p. 1) and Example 2.2 (p. 2). -/
theorem finite_of_finrank_eq_two (hF : Module.finrank ℚ F = 2) [IsTotallyComplex F] :
    Finite (𝓞 F)ˣ := by
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    have h1 := IsTotallyComplex.nrRealPlaces_eq_zero F
    have h2 := card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := card_add_two_mul_card_eq_rank F
    rw [hF] at h3
    omega
  have hrank : rank F = 0 := by
    simp [rank, hcard]
  apply Finite.of_surjective (fun ζ : torsion F => (ζ : (𝓞 F)ˣ))
  intro x
  obtain ⟨ζe, h, -⟩ := exist_unique_eq_mul_prod F x
  refine ⟨ζe.1, ?_⟩
  change (ζe.1 : (𝓞 F)ˣ) = x
  rw [h]
  have huniv : (Finset.univ : Finset (Fin (rank F))) = ∅ := by
    rw [hrank]
    exact Finset.univ_eq_empty
  rw [huniv, Finset.prod_empty, mul_one]

end NumberField.Units
