/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DualDeformationData

/-!
# Public use of dual deformation data

Native split-epimorphism and ordinary homotopy data build the chosen datum
with the full over-base equation. Consumers retain the section and actual
homotopy map, and can cancel the base map using the derived epimorphism.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe v u

namespace DualDeformationDataTest

variable {C : Type u} [Category.{v} C]
variable (P : Precylinder (𝟭 C)) {X Y Z : C} {p : X ⟶ Y}

/-- Native input data give a dual datum with the same section and actual homotopy map. -/
def from_native (S : SplitEpi p)
    (H : (P.app X).LeftHomotopy (𝟙 X) (p ≫ S.section_))
    (hOver : H.h ≫ p = (P.app X).π ≫ p) :
    {D : P.DualDeformationData p // D.toSplitEpi = S ∧ D.homotopy.h = H.h} :=
  ⟨{ section_ := S.section_
     section_comp := S.id
     homotopy := H
     over_base := hOver }, ⟨rfl, rfl⟩⟩

/-- The over-base equation remains exact after any map into the full cylinder. -/
theorem over_after_precomp (D : P.DualDeformationData p)
    (a : Z ⟶ (P.app X).I) :
    (a ≫ D.homotopy.h) ≫ p = (a ≫ (P.app X).π) ≫ p := by
  simpa only [Category.assoc] using congrArg (fun f ↦ a ≫ f) D.over_base

/-- A dual datum supplies the epimorphism needed for cancellation. -/
theorem cancel_base (D : P.DualDeformationData p) (a b : Y ⟶ Z)
    (h : p ≫ a = p ≫ b) : a = b := by
  have : Epi p := D.epi
  exact (cancel_epi p).mp h

end DualDeformationDataTest
