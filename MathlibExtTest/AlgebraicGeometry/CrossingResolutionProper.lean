/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CrossingResolutionProper

/-! # Consumers for `MvPolynomial.CrossingQuotient.Resolution.isProper_toCrossing` -/

namespace CrossingResolutionProperTest

open AlgebraicGeometry MvPolynomial.CrossingQuotient

universe u

/-- The exact source statement, with the original binders. -/
public theorem exactSource {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) :=
  Resolution.isProper_toCrossing t e

/-- The statement applies over a base ring in a higher universe. -/
public example {W : Type (u + 1)} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) :=
  Resolution.isProper_toCrossing t e

/-- With a single chart, the resolution of the crossing of `t` over itself is proper. -/
public example (t : ℤ) : IsProper (Resolution.toCrossing t 1) :=
  Resolution.isProper_toCrossing t 1

/-- Properness gives universal closedness of the resolution morphism. -/
public example {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    UniversallyClosed (Resolution.toCrossing t e) :=
  have := Resolution.isProper_toCrossing t e
  inferInstance

end CrossingResolutionProperTest
