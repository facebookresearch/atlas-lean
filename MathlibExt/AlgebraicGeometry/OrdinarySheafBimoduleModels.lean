/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PresheafRingMonoidModels
public import MathlibExt.CategoryTheory.NativeBimoduleTensorOperators

/-!
# Ordinary sheaf bimodules over the actual ring section presheaves

Both original ring actions are native Bimod actions in module-valued
presheaves. The underlying presheaf satisfies the actual sheaf condition.
This is an ordinary representation bridge. Analytic Ind modules use
Bimod over beta of the ring in actual Ind(k_X), as in DK Section 4.10.

Source: DK arXiv:1311.2374v2, Section 4.10; native Bimod/sheaf constructors
at Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinarySheafBimoduleModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves

variable (X : TopCat.{0})

abbrev ModulePresheaf := (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ

variable (A B : Mon (ModulePresheaf X))

def IsSheafBimodule : ObjectProperty (Bimod A B) :=
  fun M => Presheaf.IsSheaf (Opens.grothendieckTopology X) M.X

abbrev SheafBimodule := (IsSheafBimodule X A B).FullSubcategory

def underlyingSheaf : SheafBimodule X A B ⥤ OrdinarySheaf ℂ X where
  obj M := ⟨M.obj.X, M.property⟩
  map f := ⟨f.hom.hom⟩
  map_id M := rfl
  map_comp f g := rfl

end MathlibExt.AlgebraicGeometry.OrdinarySheafBimoduleModels
