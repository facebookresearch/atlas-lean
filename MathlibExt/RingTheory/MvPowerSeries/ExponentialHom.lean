/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/Exp.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
port the finite exponential homomorphism and degree-filtration law through the
lawful zero-constant exponential.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.Exponential

/-!
# Homomorphisms preserving multivariate formal exponentials

Ring homomorphisms between commutative rational algebras preserve finite
exponential truncations. An endomorphism whose output coefficients respect the
total-degree filtration therefore preserves the lawful formal exponential.
-/

@[expose] public section

namespace MvPowerSeries

open Finset

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

/-- A ring homomorphism between multivariate power-series rings commutes with
finite exponential truncations. -/
theorem map_expTrunc {τ S : Type*} [CommRing S] [Algebra ℚ S]
    (Φ : MvPowerSeries σ R →+* MvPowerSeries τ S) (N : ℕ) (w : MvPowerSeries σ R) :
    Φ (expTrunc N w) = expTrunc N (Φ w) := by
  unfold expTrunc
  rw [map_sum]
  exact sum_congr rfl fun n _ => by rw [map_rat_smul, map_pow]

/-- A ring endomorphism preserving the total-degree coefficient filtration
commutes with the formal exponential. The filtration premise itself implies
that the image of a zero-constant series again has zero constant coefficient. -/
theorem hom_expOfConstantCoeffZero
    (Φ : MvPowerSeries σ R →+* MvPowerSeries σ R)
    (hΦ : ∀ (d : σ →₀ ℕ) (f g : MvPowerSeries σ R),
      (∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e f = coeff e g) →
        coeff d (Φ f) = coeff d (Φ g))
    {w : MvPowerSeries σ R} (hw : constantCoeff w = 0) :
    Φ (expOfConstantCoeffZero w hw) =
      expOfConstantCoeffZero (Φ w) (by
        calc
          constantCoeff (Φ w) = coeff 0 (Φ w) :=
            (coeff_zero_eq_constantCoeff_apply _).symm
          _ = coeff 0 (Φ 0) := hΦ 0 w 0 (by
            intro e he
            have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp
              (Nat.eq_zero_of_le_zero (by simpa using he))
            subst e
            simp [coeff_zero_eq_constantCoeff_apply, hw])
          _ = 0 := by rw [map_zero, coeff_zero]) := by
  ext d
  rw [hΦ d (expOfConstantCoeffZero w hw) (expTrunc (d.degree + 1) w)
    (fun e he => coeff_expOfConstantCoeffZero w hw e (by omega)),
    map_expTrunc, coeff_expOfConstantCoeffZero_degree]

end MvPowerSeries
