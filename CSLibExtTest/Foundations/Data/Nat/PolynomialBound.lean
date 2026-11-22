/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Data.Nat.PolynomialBound

/-!
# Polynomial-bound closure tests

These importing-client checks cover the source-equivalent one-constant witness, constants,
identity, sums, products, powers, composition, and the explicit monotone bound. The predicate
expresses only numeric growth; these tests make no computability or running-time claim.
-/

namespace Cslib

example {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ c : ℕ, ∀ n, f n ≤ c * (n + 1) ^ c :=
  polynomiallyBounded_iff_le_mul_pow_self.1 hf

example : PolynomiallyBounded (fun _ => 7) := PolynomiallyBounded.const 7

example : PolynomiallyBounded (fun n => n) := PolynomiallyBounded.id

example : PolynomiallyBounded (fun n => n + n * n) :=
  PolynomiallyBounded.id.add (PolynomiallyBounded.id.mul PolynomiallyBounded.id)

example : PolynomiallyBounded (fun n => n ^ 3) := PolynomiallyBounded.id.pow 3

example : PolynomiallyBounded (fun n => n * n + 2) :=
  (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2)).comp
    (PolynomiallyBounded.id.mul PolynomiallyBounded.id)

/-- The normalized witness permits `c = 0`, exactly covering the zero function at `n = 0`. -/
example : PolynomiallyBounded (fun _ => 0) :=
  (polynomiallyBounded_iff_le_mul_pow_self (f := fun _ => 0)).2 ⟨0, by simp⟩

example : PolynomiallyBounded (fun n => 3 * (n + 1) ^ 3) :=
  (PolynomiallyBounded.mono_bound 3).1

example : Monotone (fun n => 3 * (n + 1) ^ 3) :=
  (PolynomiallyBounded.mono_bound 3).2

#print axioms polynomiallyBounded_iff_le_mul_pow_self
#print axioms PolynomiallyBounded.const
#print axioms PolynomiallyBounded.id
#print axioms PolynomiallyBounded.add
#print axioms PolynomiallyBounded.mul
#print axioms PolynomiallyBounded.pow
#print axioms PolynomiallyBounded.comp
#print axioms PolynomiallyBounded.mono_bound

end Cslib
