/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
import MathlibExt.AlgebraicGeometry.EllipticCurve.SemistableModel

namespace WeierstrassCurve

theorem exactSource (W : WeierstrassCurve ℤ) (hW : W.IsSemistableModel) :
    W.c₄ ≠ 0 ∧ W.c₆ ≠ 0 :=
  c4_ne_zero_and_c6_ne_zero_of_isSemistableModel W hW

/-- `IsSemistableModel` is the predicate from `FreyCurve`, so the theorem applies to
the Frey curve's semistability result. -/
example (P : FreyPackage) : P.freyCurveInt.c₄ ≠ 0 ∧ P.freyCurveInt.c₆ ≠ 0 :=
  c4_ne_zero_and_c6_ne_zero_of_isSemistableModel _ P.frey_isSemistableModel

/-- The good primes of `ResidualModularity` are the primes not dividing the
conductor level. -/
example (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {q : ℕ} (hq : q.Prime) :
    W.IsGoodPrimeFor q ↔ ¬ q ∣ W.conductorLevel :=
  (prime_dvd_conductorLevel_iff W hΔ hq).not.symm

/-- The curve `y² = x³ + 1` unfolds the new definitions concretely. -/
example : (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).conductorLevel = 6 := by
  have hΔ : (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).Δ.natAbs = 432 := by
    decide
  rw [conductorLevel, hΔ, Nat.radical_eq_prod_primeFactors]
  have h432 : (432 : ℕ) = 2 ^ 4 * 3 ^ 3 := by decide
  rw [h432, Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_prime_pow (by decide) Nat.prime_two,
    Nat.primeFactors_prime_pow (by decide) Nat.prime_three,
    Finset.prod_union (by decide), Finset.prod_singleton,
    Finset.prod_singleton]
  rfl

example : (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).c₄ = 0 := by
  decide

/-- That curve is not semistable: `2` divides both `Δ` and `c₄`, so the
semistability hypothesis in the main theorem cannot be dropped. -/
example : ¬ (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).IsSemistableModel := by
  intro h
  exact h 2 Nat.prime_two (by decide) (by decide)

example (W : WeierstrassCurve ℤ) : 0 < W.conductorLevel :=
  conductorLevel_pos W

example (W : WeierstrassCurve ℤ) : Squarefree W.conductorLevel :=
  squarefree_conductorLevel W

example (W : WeierstrassCurve ℤ) (E : WeierstrassCurve ℚ)
    (h : W.IsIntegralModelOf E) :
    ∃ C : VariableChange ℚ, C • E = W.map (Int.castRingHom ℚ) :=
  h

end WeierstrassCurve
