/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FreyCurve

@[expose] public section

open WeierstrassCurve

-- Consumer with the original binders.
example (P : FreyPackage) : P.freyCurveInt.IsSemistableModel :=
  P.frey_isSemistableModel

-- The semistability conclusion unfolds to the prime-wise `c₄` condition.
example (P : FreyPackage) :
    ∀ q : ℕ, q.Prime → (q : ℤ) ∣ P.freyCurveInt.Δ → ¬ (q : ℤ) ∣ P.freyCurveInt.c₄ :=
  P.frey_isSemistableModel

-- Boundary: without a prime hypothesis the `c₄` conclusion can fail; for
-- `q = 1` every integer divides `c₄`, so primality is essential.
example (P : FreyPackage) : (1 : ℤ) ∣ P.freyCurveInt.c₄ := one_dvd _

open FreyPackage in
private theorem exactSource (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) : P.freyCurve.IsPeuRamifieeAt P.p q :=
  FreyCurve.isPeuRamifieeAt_odd_of_integralForm P hq2

-- The peu-ramifiée predicate unfolds to divisibility of the discriminant
-- valuation.
example (W : WeierstrassCurve ℚ) (p ℓ : ℕ) :
    W.IsPeuRamifieeAt p ℓ ↔ (p : ℤ) ∣ padicValRat ℓ W.Δ :=
  Iff.rfl

-- Boundary: the excluded prime `2` is prime, and the discriminant
-- valuation computation at `2` for a concrete curve gives `4`, which
-- `5` does not divide. This is the arithmetic that the `q ≠ 2`
-- hypothesis avoids in the Frey-curve valuation formula.
example : Nat.Prime 2 ∧ ¬ (5 : ℤ) ∣ 4 := ⟨Nat.prime_two, by norm_num⟩

example : (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℚ).Δ = -432 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
