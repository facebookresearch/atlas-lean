/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.RelativeHomotopy
public import Mathlib.CategoryTheory.EpiMono

/-!
# Dual deformation data over the base

A chosen section and a native identity-to-section-composite homotopy retain
the dual equations in Cisinski Definition 2.4.16. The whole homotopy lies
over the specified base map. The chosen section also gives the native
split-epimorphism datum.

These equations define data for any functorial precylinder; the exact-cylinder
application is the source definition. Stationarity along the chosen section
is a separate condition.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C]
variable (P : Precylinder (𝟭 C)) {X Y : C}

/-- A chosen section and an identity-to-section-composite homotopy whose
entire cylinder map lies over the specified base. -/
structure DualDeformationData (p : X ⟶ Y) : Type v where
  /-- The chosen section. -/
  section_ : Y ⟶ X
  /-- The section splits the specified map. -/
  section_comp : section_ ≫ p = 𝟙 Y
  /-- The native homotopy from the identity to the section composite. -/
  homotopy : (P.app X).LeftHomotopy (𝟙 X) (p ≫ section_)
  /-- The homotopy lies over the base on the whole cylinder. -/
  over_base : homotopy.h ≫ p = (P.app X).π ≫ p

namespace DualDeformationData

variable {P} {p : X ⟶ Y}

/-- Retain the chosen section in the native split-epimorphism datum. -/
def toSplitEpi (D : P.DualDeformationData p) : SplitEpi p where
  section_ := D.section_
  id := D.section_comp

/-- Dual deformation data imply that the specified map is epic. -/
lemma epi (D : P.DualDeformationData p) : Epi p := D.toSplitEpi.epi

/-- The identity has dual deformation data from the constant native homotopy. -/
def refl (X : C) : P.DualDeformationData (𝟙 X) where
  section_ := 𝟙 X
  section_comp := by simp
  homotopy :=
    { h := (LeftHomotopy.refl (P.app X) (𝟙 X)).h
      h₀ := (LeftHomotopy.refl (P.app X) (𝟙 X)).h₀
      h₁ := by
        simpa only [Category.id_comp] using
          (LeftHomotopy.refl (P.app X) (𝟙 X)).h₁ }
  over_base := by simp only [LeftHomotopy.refl_h, Category.comp_id]

end DualDeformationData

end HomotopicalAlgebra.Precylinder
