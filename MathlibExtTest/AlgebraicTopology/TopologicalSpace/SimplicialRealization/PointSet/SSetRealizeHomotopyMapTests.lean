/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap

/-!
# Realized simplicial homotopy endpoint clients

Direct universe-zero clients of `SSet.realizeHomotopyMap_zero`
(`0 ↔ ι₀`) and `SSet.realizeHomotopyMap_one` (`1 ↔ ι₁`) with all
homotopy arguments explicit.

Nonclaims: no homotopy-equivalence, weak-equivalence, additivity,
K-space, or `π₀` content.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SSet

/-- Direct client of the zero endpoint law. -/
theorem realizeHomotopyMap_zero_client (X Y : SSet.{0}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (0 : TopCat.I.{0}))
      (𝟙 (SSet.toTop.obj X)) ≫
      SSet.realizeHomotopyMap X Y f g H =
      SSet.toTop.map f :=
  SSet.realizeHomotopyMap_zero X Y f g H

/-- Direct client of the one endpoint law. -/
theorem realizeHomotopyMap_one_client (X Y : SSet.{0}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (1 : TopCat.I.{0}))
      (𝟙 (SSet.toTop.obj X)) ≫
      SSet.realizeHomotopyMap X Y f g H =
      SSet.toTop.map g :=
  SSet.realizeHomotopyMap_one X Y f g H

end SSet
