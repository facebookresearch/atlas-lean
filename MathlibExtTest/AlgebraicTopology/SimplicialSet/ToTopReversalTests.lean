/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Co-Authored-By: Roy Toskas <uife8x27@avocadolabs.ai>
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ToTopReversal

/-!
Tests for naturality of the inverse realization-reversal iso: the stated
interface contract only, no nerve, comma, or Quillen-theorem claim.
-/

namespace SSet

namespace ToTopReversalTests

open CategoryTheory Opposite Simplicial

universe u

noncomputable example {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map f ≫ (toTopReversalIso Y).inv =
      (toTopReversalIso X).inv ≫
        SSet.toTop.map (SimplicialObject.opFunctor.map f) :=
  toTopReversalIso_inv_naturality f

end ToTopReversalTests

end SSet
