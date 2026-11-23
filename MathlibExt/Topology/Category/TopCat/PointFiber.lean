/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Literal point fibers of topological morphisms

The point fiber is the original inverse-image subtype of a chosen point.
Pullback support supplies its ordinary topological comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace TopCat

/-- The literal point fiber of a TopCat morphism. -/
abbrev pointFiber {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :=
  {x : E // p x = b}

end TopCat
