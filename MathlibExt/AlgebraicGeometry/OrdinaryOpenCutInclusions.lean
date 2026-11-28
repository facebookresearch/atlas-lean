/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinarySheafOpenCuts

/-!
# Original inclusion maps between coefficient open cuts

The map is the literal inclusion of locally vanishing sections, followed
by native sheafification. Source: DK1311.2374v2 Section2.4; native
submodule and sheafification APIs at Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinaryOpenCutInclusions

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves OrdinarySheafOpenCuts

variable (k : Type) [Field k] (X : TopCat.{0}) (F : OrdinarySheaf k X)
  {U V : Opens X} (h : V ≤ U)

def cutPresheafInclusion : cutPresheaf k X F V ⟶ cutPresheaf k X F U where
  app W := ModuleCat.ofHom
    { toFun := fun s => ⟨s.val, fun x hx hxu =>
        s.property x hx (fun hxV => hxu (h hxV))⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  naturality {W Z} f := by ext s; rfl

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

def cutInclusion : (ordinaryOpenCut k X V).obj F ⟶ (ordinaryOpenCut k X U).obj F :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).map
    (cutPresheafInclusion k X F h)

end MathlibExt.AlgebraicGeometry.OrdinaryOpenCutInclusions
