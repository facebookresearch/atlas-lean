/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules

/-!
# Tests for natural-pullback multiplier modules

The ideal divisor is only formed for a nonzero ideal, whose order `idealCoefficient` computes, and
the limiting relative canonical divisor at index one is `K_Y - f^♮(K_X)`.
-/

open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (C : CanonicalData V)
  [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]

/-- The zero ideal has no ideal divisor: `sInf ∅ = 0` would not be its order. -/
example (M : CanonicalModel V C) : ¬ IdealSupport V C M ⊥ :=
  fun h ↦ h.nonzero rfl

/-- At index one the limiting relative canonical divisor is `K_Y - f^♮(K_X)`. -/
example (M : CanonicalModel V C)
    (h : NaturalSupport V C M ((((1 : ℕ+) : ℕ) : ℤ) • canonicalDivisor C)) :
    limitingRelativeCanonical V C M 1 h = realCast (canonicalDivisor M.canonical) -
      realCast (naturalDivisor V C M ((((1 : ℕ+) : ℕ) : ℤ) • canonicalDivisor C) h) := by
  simp [limitingRelativeCanonical]
