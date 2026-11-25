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
# Strong deformation data for a chosen cylinder

A retraction and a native relative homotopy from the identity to the
retract composite retain all three equations in Cisinski Definition 2.4.16.
The homotopy is stationary along the specified map throughout its cylinder.
The chosen retraction also gives the native split-monomorphism datum.

The equations make sense for every functorial precylinder. Their use with
an exact cylinder gives the source definition, before any model structure.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C]
variable (P : Precylinder (𝟭 C)) {K L S : C}

/-- A chosen retraction and an identity-to-retract homotopy stationary
on the whole cylinder of the specified source. -/
structure StrongDeformationData (i : K ⟶ L) where
  retraction : L ⟶ K
  retract : i ≫ retraction = 𝟙 K
  homotopy : P.RelativeLeftHomotopy i (𝟙 L) (retraction ≫ i)

namespace StrongDeformationData

variable {P} {i : K ⟶ L}

/-- Retain the chosen retraction in the native split-monomorphism datum. -/
def toSplitMono (D : P.StrongDeformationData i) : SplitMono i where
  retraction := D.retraction
  id := D.retract

/-- Strong deformation data imply that the specified map is monic. -/
lemma mono (D : P.StrongDeformationData i) : Mono i := D.toSplitMono.mono

/-- The homotopy is constant on the full cylinder of the retract. -/
lemma stationary (D : P.StrongDeformationData i) :
    P.I.map i ≫ D.homotopy.h = (P.app K).π ≫ i := by
  simpa only [Category.comp_id] using D.homotopy.stationary

/-- The identity has strong deformation data for the chosen cylinder. -/
def refl (K : C) : P.StrongDeformationData (𝟙 K) where
  retraction := 𝟙 K
  retract := by simp
  homotopy := by
    simpa only [Category.id_comp] using
      (RelativeLeftHomotopy.refl (P := P) (𝟙 K) (𝟙 K))

end StrongDeformationData

end HomotopicalAlgebra.Precylinder
