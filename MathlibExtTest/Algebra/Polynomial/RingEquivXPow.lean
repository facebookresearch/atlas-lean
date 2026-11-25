/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RingEquivXPow

/-! # Consumers for `RingEquiv.false_of_apply_eq_X_pow_of_apply_eq_X` -/

namespace RingEquivXPowTest

universe u v

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource (p : ℕ) (hp : 2 ≤ p) (k : Type v)
    [CommRing k] [Nontrivial k] (R : Type u) [CommRing R]
    (e₀ e₁ : R ≃+* Polynomial k) (a b : R)
    (h₀a : e₀ a = Polynomial.X) (h₀b : e₀ b = Polynomial.X ^ p)
    (h₁b : e₁ b = Polynomial.X) (h₁a : e₁ a = Polynomial.X ^ p) : False :=
  RingEquiv.false_of_apply_eq_X_pow_of_apply_eq_X p hp k R e₀ e₁ a b
    h₀a h₀b h₁b h₁a

/-- The `p = 1` analogue is not contradictory: the identity
identification sends `X` to `X ^ 1`. This checks that `2 ≤ p` is
load-bearing in the statement above. -/
public example (k : Type) [CommRing k] :
    (RingEquiv.refl (Polynomial k)) Polynomial.X = Polynomial.X ^ 1 := by
  simp

end RingEquivXPowTest
