/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.FiniteRamification

@[expose] public section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open IsDedekindDomain

namespace MathlibExtTest.RingTheory.DedekindDomain.FiniteRamification

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- Generic application of the "primes of `B`" half of Corollary 12.20. -/
example : {P : HeightOneSpectrum B | ¬ Algebra.IsUnramifiedAt A P.asIdeal}.Finite :=
  Ideal.finite_ramified_primes

/-- Generic application of the "primes of `A`" half of Corollary 12.20. -/
example : {p : HeightOneSpectrum A | ¬ Algebra.IsUnramifiedIn B p.asIdeal}.Finite :=
  Ideal.finite_ramified_primes_below

/-- Concrete instance: only finitely many primes of `ℤ` are ramified over `ℤ`. -/
example : {P : HeightOneSpectrum ℤ | ¬ Algebra.IsUnramifiedAt ℤ P.asIdeal}.Finite :=
  Ideal.finite_ramified_primes

/-- Concrete instance: only finitely many primes of `ℤ` below are ramified in `ℤ`. -/
example : {p : HeightOneSpectrum ℤ | ¬ Algebra.IsUnramifiedIn ℤ p.asIdeal}.Finite :=
  Ideal.finite_ramified_primes_below

end MathlibExtTest.RingTheory.DedekindDomain.FiniteRamification
