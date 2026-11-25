/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjective

/-!
# Component-map surjectivity consumer tests

Focused downstream checks for the public `SSet.piZeroToZerothHomotopy_surjective`
API: surjectivity for an arbitrary `SSet.{u}` and its elimination at an arbitrary
realized component. Uses only public declarations; adds no helpers.

Nonclaims: no injectivity, no equivalence, no `π₀ K ≃ K₀`, no additivity, no spectra.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjectiveTests

universe u

/-- Canonical map is surjective for an arbitrary simplicial set. Catches signature drift. -/
example (X : SSet.{u}) :
    Function.Surjective (SSet.piZeroToZerothHomotopy X) :=
  SSet.piZeroToZerothHomotopy_surjective X

/-- Every realized component has a simplicial preimage. Catches elimination drift. -/
example (X : SSet.{u}) (q : ZerothHomotopy ↑(SSet.toTop.obj X)) :
    ∃ c : SSet.π₀ X, SSet.piZeroToZerothHomotopy X c = q :=
  (SSet.piZeroToZerothHomotopy_surjective X) q

end MathlibExtTest.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjectiveTests
