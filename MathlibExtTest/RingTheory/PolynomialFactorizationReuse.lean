/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.SumTwoSquares

/-!
Canonical primitive-polynomial, UFD, GCD and sum-of-squares APIs. Gaussian classification is
checked only for rational primes.
-/

set_option autoImplicit false
noncomputable section

example (F : Type*) [Field F] {p q r : Polynomial F}
    (hp : Irreducible p) (h : p ∣ q * r) : p ∣ q ∨ p ∣ r := hp.prime.dvd_or_dvd h

example (R : Type*) [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {p q : Polynomial R} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := hp.mul hq

example (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid (Polynomial R) := inferInstance

example (R : Type*) [CommRing R] [IsDomain R] [h : Nonempty (NormalizedGCDMonoid R)]
    {p q : Polynomial R} (hp : p.IsPrimitive) :
    p ∣ q ↔ p.map (algebraMap R (FractionRing R)) ∣ q.map (algebraMap R (FractionRing R)) := by
  letI : NormalizedGCDMonoid R := Classical.choice h
  exact hp.dvd_iff_fraction_map_dvd_fraction_map (FractionRing R)

example (p : Polynomial ℤ) : p.IsPrimitive ↔ p.content = 1 :=
  Polynomial.isPrimitive_iff_content_eq_one

example (n : ℕ) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) :=
  Nat.eq_sq_add_sq_iff

example (p : ℕ) [Fact p.Prime] : Prime (p : GaussianInt) ↔ p % 4 = 3 :=
  GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p

example (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    GCDMonoid R := UniqueFactorizationMonoid.toGCDMonoid R

example (M : Type*) [Monoid M] (a b : M) :
    Associated a b ↔ ∃ u : Mˣ, b * u = a := Associated.comm

#print axioms Irreducible.prime
#print axioms Prime.dvd_or_dvd
#print axioms Polynomial.IsPrimitive.mul
#print axioms Polynomial.uniqueFactorizationMonoid
#print axioms Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map
#print axioms Polynomial.isPrimitive_iff_content_eq_one
#print axioms Nat.eq_sq_add_sq_iff
#print axioms GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime
#print axioms UniqueFactorizationMonoid.toGCDMonoid
#print axioms Associated.comm

end
