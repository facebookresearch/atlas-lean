/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.SteinerRatio

@[expose] public section

namespace MathlibExtTest.SteinerRatio

open MathlibExt.Geometry.SteinerRatio

/-- A degenerate edge has length zero. -/
example (x : Plane) : edgeLength s(x, x) = 0 := by
  simp

/-- Edge length is the Euclidean distance, symmetrically. -/
example (x y : Plane) : edgeLength s(x, y) = dist y x := by
  rw [edgeLength_mk, dist_comm]

/-- Steiner points never hurt, on every nonempty point set. -/
example {V : Finset Plane} (hV : V.Nonempty) :
    steinerLength V ≤ mstLength V :=
  steinerLength_le_mstLength hV

/-- The Steiner length is nonnegative on nonempty point sets. -/
example {V : Finset Plane} (hV : V.Nonempty) : 0 ≤ steinerLength V :=
  steinerLength_nonneg hV

end MathlibExtTest.SteinerRatio
