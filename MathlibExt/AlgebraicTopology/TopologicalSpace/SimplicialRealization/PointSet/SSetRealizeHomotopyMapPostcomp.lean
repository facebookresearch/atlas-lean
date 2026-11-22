/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap

/-!
# Target composition and the whole realized homotopy cylinder

Postcomposing the actual simplicial cylinder agrees with postcomposing its
realized homotopy. The realized map depends only on the complete cylinder
map, independently of the descriptions of its two endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory
open scoped Simplicial

namespace SSet

/-- Realization preserves target composition of the entire simplicial homotopy. -/
theorem realizeHomotopyMap_postcomp {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (q : Y ⟶ Z) :
    realizeHomotopyMap X Y f g H ≫ SSet.toTop.map q =
      realizeHomotopyMap X Z (f ≫ q) (g ≫ q) (H.postcomp q) := by
  simp only [realizeHomotopyMap, Homotopy.postcomp_h, Functor.map_comp, Category.assoc]

/-- Equal whole cylinder maps give equal realized homotopies even with different endpoint descriptions. -/
theorem realizeHomotopyMap_eq_of_h_eq {X Y : SSet.{u}}
    {f g f' g' : X ⟶ Y} (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (h : H.h = H'.h) :
    realizeHomotopyMap X Y f g H = realizeHomotopyMap X Y f' g' H' := by
  simp only [realizeHomotopyMap, h]

end SSet
