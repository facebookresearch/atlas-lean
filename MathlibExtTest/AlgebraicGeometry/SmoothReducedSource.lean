/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SmoothReducedSource

open CategoryTheory AlgebraicGeometry

/-- Smoke test of smooth morphisms preserving reducedness. -/
example {X Y : Scheme} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian f
