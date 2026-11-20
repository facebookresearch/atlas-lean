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
