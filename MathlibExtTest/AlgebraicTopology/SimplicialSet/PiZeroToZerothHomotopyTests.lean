/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopy

/-!
# Simplicial π₀ to realized components consumer tests

Focused downstream checks for the public `SSet.piZeroToZerothHomotopy` API:
vertex computation via the `SSet.realizedVertex` orientation, naturality under a
simplicial map, and the `TopCat.zerothHomotopyMap (SSet.toTop.map f)` type. Uses only public
declarations; adds no surjectivity/injectivity claim and no helpers.

Nonclaims: no surjectivity, no injectivity, no `π₀ K ≃ K₀`, no additivity, no spectrum claim.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopyTests

universe u

variable {X Y : SSet.{u}}

/-- Canonical map sends a vertex class to its realized vertex. Catches orientation drift. -/
example (x : X _⦋0⦌) :
    SSet.piZeroToZerothHomotopy X (SSet.π₀.mk x) =
      ZerothHomotopy.mk (SSet.realizedVertex x) :=
  SSet.piZeroToZerothHomotopy_mk X x

/-- Canonical map is natural under a simplicial map. Catches naturality drift. -/
example (f : X ⟶ Y) :
    TopCat.zerothHomotopyMap (SSet.toTop.map f) ∘ SSet.piZeroToZerothHomotopy X =
      SSet.piZeroToZerothHomotopy Y ∘ SSet.mapπ₀ f :=
  SSet.piZeroToZerothHomotopy_naturality f

/-- Topological component map has the inferred type. Catches inference drift. -/
noncomputable example (f : X ⟶ Y) (p : ZerothHomotopy ↑(SSet.toTop.obj X)) :
    ZerothHomotopy ↑(SSet.toTop.obj Y) :=
  TopCat.zerothHomotopyMap (SSet.toTop.map f) p

end MathlibExtTest.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopyTests
