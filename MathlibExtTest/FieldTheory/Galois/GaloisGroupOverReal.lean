/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.GaloisGroupOverReal
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Examples for Galois groups of finite Galois extensions of `ℝ`

Exercises `RealGalois.finrank_eq_one_or_two`,
`RealGalois.gal_card_eq_one_or_two`, and `RealGalois.gal_card_pow_two`
on the two finite Galois extensions of `ℝ` itself: `ℝ` (Galois group of
order `1 = 2 ^ 0`) and `ℂ` (Galois group of order `2 = 2 ^ 1`, generated
by complex conjugation). The `ℂ` case also pins the sharp value
`Nat.card Gal(ℂ/ℝ) = 2` via the Galois degree formula.
-/

/-- `ℂ / ℝ` is Galois: separability holds since `ℝ` is a perfect field,
and normality holds since every complex polynomial splits. -/
private instance isGalois_real_complex : IsGalois ℝ ℂ := by
  rw [isGalois_iff]
  refine ⟨inferInstance, ?_⟩
  rw [normal_iff]
  intro x
  exact ⟨IsIntegral.of_finite ℝ x, IsAlgClosed.splits _⟩

/-- The degree of `ℂ` over `ℝ` is `2`, via the finrank form of the
classification. -/
example : Module.finrank ℝ ℂ = 1 ∨ Module.finrank ℝ ℂ = 2 :=
  RealGalois.finrank_eq_one_or_two

/-- The degree of `ℝ` over itself is `1`, via the finrank form of the
classification. -/
example : Module.finrank ℝ ℝ = 1 ∨ Module.finrank ℝ ℝ = 2 :=
  RealGalois.finrank_eq_one_or_two

/-- The `ℂ / ℝ` Galois group has order `1` or `2`. -/
example : Nat.card Gal(ℂ/ℝ) = 1 ∨ Nat.card Gal(ℂ/ℝ) = 2 :=
  RealGalois.gal_card_eq_one_or_two

/-- The `ℝ / ℝ` Galois group has order `1` or `2`. -/
example : Nat.card Gal(ℝ/ℝ) = 1 ∨ Nat.card Gal(ℝ/ℝ) = 2 :=
  RealGalois.gal_card_eq_one_or_two

/-- The `ℂ / ℝ` Galois group has order a power of `2`. -/
example : ∃ n : ℕ, Nat.card Gal(ℂ/ℝ) = 2 ^ n :=
  RealGalois.gal_card_pow_two

/-- The `ℝ / ℝ` Galois group has order a power of `2`. -/
example : ∃ n : ℕ, Nat.card Gal(ℝ/ℝ) = 2 ^ n :=
  RealGalois.gal_card_pow_two

/-- Sharp value: the `ℂ / ℝ` Galois group has order exactly `2`. -/
example : Nat.card Gal(ℂ/ℝ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact Complex.finrank_real_complex

/-- Sharp value: the `ℝ / ℝ` Galois group is trivial. -/
example : Nat.card Gal(ℝ/ℝ) = 1 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact Module.finrank_self ℝ
