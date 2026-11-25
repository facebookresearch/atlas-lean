/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.QuasiFinite.OfFlatFiniteType

@[expose] public section

open scoped TensorProduct

universe u v w

/-- Consumer with the original binders. -/
private theorem exactSource
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type w) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] :
    Algebra.QuasiFinite R S :=
  Algebra.QuasiFinite.of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing R K S

/-- Higher-universe consumer: the algebra may live in `Type 2` while the
base ring and its fraction field live in lower universes. -/
private theorem exactSourceHigherUniverse
    (R : Type 1) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type 1) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type 2) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] :
    Algebra.QuasiFinite R S :=
  Algebra.QuasiFinite.of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing R K S

/-- Concrete application: a field, viewed as an algebra over itself with
itself as fraction field, is quasi-finite. -/
example : Algebra.QuasiFinite ℚ ℚ :=
  Algebra.QuasiFinite.of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing
    ℚ ℚ ℚ
