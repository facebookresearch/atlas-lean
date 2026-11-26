/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial

@[expose] public section

universe u v

namespace AlgebraicCurve

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

-- Consumer with the source binders plus the three explicit hypotheses:
-- the Riemann-Roch formula, a finite degree-zero Picard group, and a divisor
-- of degree one.
example [Finite k] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : ConstantsAreBase k F)
    (hRR : ∃ W : Divisor k F, ∀ D : Divisor k F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF k F : ℤ))
    (hPic : Finite (Pic0 k F)) (hD₁ : ∃ D : Divisor k F, Divisor.degree D = 1) :
    ∃ L : Polynomial ℤ,
      L.natDegree ≤ 2 * genusFF k F ∧
      L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * genusFF k F,
        L.coeff (2 * genusFF k F - i) * (Nat.card k : ℤ) ^ i =
          (Nat.card k : ℤ) ^ genusFF k F * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : Divisor k F //
                0 ≤ D ∧ Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ) :=
  exists_LPolynomial_of_finite_of_riemannRoch k F hC hRR hPic hD₁

-- Higher-universe consumer.
example {k' F' : Type (max u v)} [Field k'] [Finite k'] [Field F'] [Algebra k' F']
    [IsCurveOver k' F'] [Algebra.EssFiniteType k' F']
    (hC : ConstantsAreBase k' F')
    (hRR : ∃ W : Divisor k' F', ∀ D : Divisor k' F',
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF k' F' : ℤ))
    (hPic : Finite (Pic0 k' F')) (hD₁ : ∃ D : Divisor k' F', Divisor.degree D = 1) :
    ∃ L : Polynomial ℤ,
      L.natDegree ≤ 2 * genusFF k' F' ∧
      L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * genusFF k' F',
        L.coeff (2 * genusFF k' F' - i) * (Nat.card k' : ℤ) ^ i =
          (Nat.card k' : ℤ) ^ genusFF k' F' * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k' : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : Divisor k' F' //
                0 ≤ D ∧ Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ) :=
  exists_LPolynomial_of_finite_of_riemannRoch k' F' hC hRR hPic hD₁

-- Boundary: with no places contributing, the zero divisor has degree zero,
-- and a principal divisor has degree zero on a curve.
example [IsCurveOver k F] : Divisor.degree (0 : Divisor k F) = 0 := map_zero _

example [IsCurveOver k F] {D : Divisor k F} (hD : Divisor.IsPrincipal D) :
    Divisor.degree D = 0 := by
  obtain ⟨z, hz, hP⟩ := hD
  obtain ⟨E, hE, hdeg⟩ := IsCurveOver.exists_divisor (K := k) (F := F) z hz
  have hED : E = D := Finsupp.ext fun v => by rw [hE v, hP v]
  rwa [hED] at hdeg

-- The curve predicate carries the source's rank-one Kähler differentials.
example [IsCurveOver k F] : Module.finrank F Ω[F⁄k] = 1 :=
  IsCurveOver.kaehler_free_rank_one.2

-- The zero function and the constants lie in the Riemann-Roch space of `0`.
example : (0 : F) ∈ LSpace (0 : Divisor k F) := (LSpace _).zero_mem

example (c : k) : algebraMap k F c ∈ LSpace (0 : Divisor k F) := by
  intro v
  simpa using v.adicValuation_algebraMap_le_one c

end AlgebraicCurve
