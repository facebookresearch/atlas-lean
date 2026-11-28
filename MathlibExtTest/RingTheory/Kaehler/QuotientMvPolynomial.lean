/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Kaehler.QuotientMvPolynomial

open MvPolynomial

-- The presentation in any finite number of variables.
example (R : Type) [CommRing R] (σ : Type) [Fintype σ] (g : MvPolynomial σ R) :
    Function.Surjective (kaehlerCoordinates R g) ∧
      LinearMap.ker (kaehlerCoordinates R g) =
        Submodule.span (MvPolynomial σ R ⧸ Ideal.span {g})
          {fun i ↦ Ideal.Quotient.mk (Ideal.span {g}) (pderiv i g)} :=
  ⟨quotientSpanSingleton_kaehler_surjective R g, quotientSpanSingleton_kaehler_ker R g⟩

-- The parabola `y = x²` over `ℚ`, `g = x² - y`: the relation is `2x̄ dx̄ - dȳ = 0`.
example :
    LinearMap.ker (kaehlerCoordinates ℚ (X 0 ^ 2 - X 1 : MvPolynomial (Fin 2) ℚ)) =
      Submodule.span (MvPolynomial (Fin 2) ℚ ⧸ Ideal.span {X 0 ^ 2 - X 1})
        {![Ideal.Quotient.mk _ (2 * X 0), Ideal.Quotient.mk _ (-1)]} := by
  rw [(kaehlerDifferential_planeCurve ℚ _).2]
  congr 3
  · simp [pderiv_X, mul_comm]
  · simp [pderiv_X]

-- A Weierstrass cubic `y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆` over any commutative ring: the
-- differentials `dx̄`, `dȳ` generate.
example (R : Type) [CommRing R] (a₁ a₂ a₃ a₄ a₆ : R) :
    Function.Surjective (kaehlerCoordinates R
      (X 1 ^ 2 + C a₁ * X 0 * X 1 + C a₃ * X 1 - X 0 ^ 3 - C a₂ * X 0 ^ 2 - C a₄ * X 0 - C a₆ :
        MvPolynomial (Fin 2) R)) :=
  (kaehlerDifferential_planeCurve R _).1
