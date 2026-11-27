/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.RatLocalizedAt

/-! # Consumers for the DVR rational-range theorem -/

namespace RatLocalizedAtTest

/-- The exact source statement, with the original `Type` binder. -/
public theorem exactSource
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = Rat.localizedAt p :=
  IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible p hp

/-- The generalized statement in a higher universe. -/
public theorem higherUniverse
    (R : Type 1) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = Rat.localizedAt p :=
  IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible p hp

/-- Boundary: a rational whose denominator is not coprime to `p` is not in
the subring; the coprimality condition in `Rat.mem_localizedAt` matters. -/
public example {p : ℕ} {q : ℚ} (h : ¬ q.den.Coprime p) :
    q ∉ Rat.localizedAt p :=
  fun hq => h (Rat.mem_localizedAt.mp hq)

/-- Conversely, coprimality of the denominator is sufficient. -/
public example {p : ℕ} {q : ℚ} (h : q.den.Coprime p) :
    q ∈ Rat.localizedAt p :=
  Rat.mem_localizedAt.mpr h

end RatLocalizedAtTest
