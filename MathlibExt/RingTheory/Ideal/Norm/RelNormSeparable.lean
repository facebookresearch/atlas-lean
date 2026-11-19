/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm

attribute [local instance] FractionRing.liftAlgebra

/-!
# Relative norm of a prime ideal in the separable case

For `R ⊆ S` Dedekind domains with `S` finite and torsion-free over `R`, and a
maximal ideal `P` of `S` lying over a maximal ideal `p` of `R`, this file states
`Ideal.relNorm R P = p ^ P.inertiaDeg R` under the single assumption that the
fraction-field extension is separable.

This is Theorem 6.10 of ATLAS `NumberTheoryI` (Section 6.2), stated there in the
`AKLB` setting (`B` the integral closure of `A` in a finite separable extension).
Mathlib proves the same statement, under the same separability assumption, as
`Ideal.relNorm_eq_pow_of_isMaximal`, so `Ideal.relNorm_eq_pow_inertiaDeg_of_isSeparable`
is deprecated in its favour.
-/

@[expose] public section

namespace Ideal

set_option linter.overlappingInstances false in
/-- Theorem 6.10 of ATLAS `NumberTheoryI`, in the separable form: the relative norm of a
maximal ideal lying over a maximal ideal is the base prime raised to the inertia degree. -/
@[deprecated Ideal.relNorm_eq_pow_of_isMaximal +typeChanged (since := "2026-11-12")]
theorem relNorm_eq_pow_inertiaDeg_of_isSeparable
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ P.inertiaDeg R :=
  relNorm_eq_pow_of_isMaximal P p

end Ideal
