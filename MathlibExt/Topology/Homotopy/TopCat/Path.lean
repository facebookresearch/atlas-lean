/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# Endpoint casts for categorical paths

This file provides endpoint transport for `TopCat.Path` while retaining the
underlying map, together with its compatibility with the ordinary path
equivalence `TopCat.pathEquiv`.
-/

@[expose] public section

universe u

namespace TopCat.Path

/-- Cast the endpoints of a categorical path while retaining its underlying map. -/
def cast {X : TopCat.{u}} {x y x' y' : X} (p : X.Path x y)
    (hx : x' = x) (hy : y' = y) : X.Path x' y' where
  hom := p.hom
  hom₀ := p.hom₀.trans hx.symm
  hom₁ := p.hom₁.trans hy.symm

/-- `TopCat.pathEquiv` sends endpoint casts to endpoint casts. -/
@[simp]
theorem pathEquiv_cast {X : TopCat.{u}} {x y x' y' : X} (p : X.Path x y)
    (hx : x' = x) (hy : y' = y) :
    TopCat.pathEquiv (p.cast hx hy) = (TopCat.pathEquiv p).cast hx hy := by
  apply _root_.Path.ext
  rfl

end TopCat.Path
