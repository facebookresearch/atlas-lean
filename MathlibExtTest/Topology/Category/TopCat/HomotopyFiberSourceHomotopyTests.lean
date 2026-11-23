/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberSourceHomotopy

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

#check TopCat.homotopyFiberSourceMap
#print axioms TopCat.homotopyFiberSourceMap
#check TopCat.homotopyFiberSourceMap_toTotal
#print axioms TopCat.homotopyFiberSourceMap_toTotal
#check TopCat.homotopyFiberSourceMap_path_apply
#print axioms TopCat.homotopyFiberSourceMap_path_apply
#check TopCat.homotopyFiberSourceMapHomotopy
#print axioms TopCat.homotopyFiberSourceMapHomotopy

variable {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (h : E ⟶ E)
  (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))

-- Every original path value has the projected prefix and the original carried tail.
example (z : TopCat.homotopyFiber p b) (t : TopCat.I.{u}) :
    TopCat.homotopyFiberPath p b (TopCat.homotopyFiberSourceMap p b h H z) t =
      if ht : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2 then
        p (H.toContinuousMap
          (⟨2 * TopCat.I.homeomorph t,
            (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨(TopCat.I.homeomorph t).2.1, ht⟩⟩,
            TopCat.homotopyFiberToTotal p b z))
      else
        TopCat.homotopyFiberPath p b z
          (TopCat.I.homeomorph.symm
            ⟨2 * TopCat.I.homeomorph t - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 ht).le, (TopCat.I.homeomorph t).2.2⟩⟩) :=
  TopCat.homotopyFiberSourceMap_path_apply p b h H z t

example :
    TopCat.homotopyFiberSourceMap p b h H ≫ TopCat.homotopyFiberToTotal p b =
      TopCat.homotopyFiberToTotal p b ≫ h :=
  TopCat.homotopyFiberSourceMap_toTotal p b h H

example : ContinuousMap.Homotopy (TopCat.homotopyFiberSourceMap p b h H).hom
    ((𝟙 (TopCat.homotopyFiber p b) :
      TopCat.homotopyFiber p b ⟶ TopCat.homotopyFiber p b).hom) :=
  TopCat.homotopyFiberSourceMapHomotopy p b h H

-- Both endpoint identities are equalities of whole continuous maps.
example : (TopCat.homotopyFiberSourceMapHomotopy p b h H).curry 0 =
    (TopCat.homotopyFiberSourceMap p b h H).hom :=
  (TopCat.homotopyFiberSourceMapHomotopy p b h H).curry_zero

example : (TopCat.homotopyFiberSourceMapHomotopy p b h H).curry 1 =
    ((𝟙 (TopCat.homotopyFiber p b) :
      TopCat.homotopyFiber p b ⟶ TopCat.homotopyFiber p b).hom) :=
  (TopCat.homotopyFiberSourceMapHomotopy p b h H).curry_one

example : Continuous (TopCat.homotopyFiberSourceMapHomotopy p b h H) :=
  (TopCat.homotopyFiberSourceMapHomotopy p b h H).continuous
