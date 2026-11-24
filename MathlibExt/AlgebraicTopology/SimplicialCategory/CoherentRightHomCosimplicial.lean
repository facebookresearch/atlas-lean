/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightHomResolution

/-!
# The genuine cosimplicial original right-Hom diagram

Every resolving degree is the actual source-to-target Hom of the
constructed fixed-front quotient realization. Its genuine simplex
operators have proved original endpoint, identity and composition laws.
No latching, cofibrancy or weak-frame conclusion is built into this data.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.CoherentRealization.RightHomCosimplicial

/-- The actual cosimplicial right-resolution diagram with its original source-to-target Hom objects and
  proved simplex operators. -/
def diagram : SimplexCategory ⥤ SSet.{u} where
  obj n := RightHomResolution.object.{u} n.len
  map θ := RightHomResolution.map θ
  map_id n := by
    induction n using SimplexCategory.rec with
    | _ n => exact RightHomResolution.map_id n
  map_comp θ ψ := RightHomResolution.map_comp θ ψ

/-- Every original resolving degree is the literal Hom of the actual fixed-front quotient realization. -/
theorem object_readback (n : ℕ) : diagram.{u}.obj (SimplexCategory.mk n) = FixedFrontCollapse.rightHom n := rfl

end CategoryTheory.CoherentRealization.RightHomCosimplicial
