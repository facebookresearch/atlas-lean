/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.WeightedProjectiveCharts

/-!
# Weighted projective charts

Focused checks of the weighted rescaling action and the cyclic chart data:

* the diagonal action scales a monomial by the total weight and is multiplicative;
* a remaining coordinate is a character vector of its own weight;
* the weight of a single-coordinate monomial is weight times exponent;
* the stabilizer of the chart origin is the whole cyclic group, while a point whose only
  nonzero coordinate has weight one has trivial stabilizer.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.WeightedProjectiveCharts

open MathlibExt.AlgebraicGeometry.WeightedProjectiveCharts

/-- Weights `(1, 2)` on two variables: `x₀x₁ ↦ a³ x₀x₁`. -/
example (k : Type) [Field k] (a : kˣ) :
    diagonalHom k (![1, 2] : Fin 2 → ℕ) a (MvPolynomial.X 0 * MvPolynomial.X 1) =
      MvPolynomial.C ((a : k) ^ 3) * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [map_mul, diagonalHom_X, diagonalHom_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (a : k) ^ 3 = (a : k) ^ 1 * (a : k) ^ 2 by ring, MvPolynomial.C_mul]
  ring

example (k : Type) [Field k] (w : Fin 3 → ℕ) (a b : kˣ) (p : MvPolynomial (Fin 3) k) :
    diagonalHom k w (a * b) p = diagonalHom k w a (diagonalHom k w b p) := by
  rw [diagonalHom_mul]
  rfl

example (k : Type) [Field k] (w : Fin 3 → ℕ) : diagonalHom k w 1 = AlgHom.id k _ :=
  diagonalHom_one k w

variable (k : Type) [Field k] (n : ℕ) (w : Fin (n + 1) → ℕ) (i : Fin (n + 1))

/-- A remaining coordinate transforms by the character of its own weight. -/
example (j : OtherCoordinate n i) :
    (MvPolynomial.X j : cyclicPolynomialRing k n i) ∈ characterSpace k n w i (w j.1) := by
  intro a
  rw [diagonalHom_X]
  simp

/-- The weight of `x_j^e` is `w_j * e`. -/
example (j : OtherCoordinate n i) (e : ℕ) :
    monomialWeight n w i (Finsupp.single j e) = w j.1 * e := by
  simp [monomialWeight]

/-- The chart origin has the whole cyclic group as stabilizer. -/
example : geometricStabilizer k n w i 0 = ⊤ := by
  rw [geometricStabilizer]
  refine iInf_eq_top.2 fun j ↦ absurd rfl j.2

/-- A point whose nonzero coordinate has weight one has trivial stabilizer. -/
example (j : OtherCoordinate n i) (hj : w j.1 = 1) (z : OtherCoordinate n i → k) (hz : z j ≠ 0) :
    geometricStabilizer k n w i z = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hker := (Subgroup.mem_iInf.1 ha) ⟨j, hz⟩
  rw [MonoidHom.mem_ker] at hker
  change a.1 ^ w j.1 = 1 at hker
  rw [hj, pow_one] at hker
  exact Subgroup.mem_bot.2 (Subtype.ext hker)

end MathlibExtTest.AlgebraicGeometry.WeightedProjectiveCharts
