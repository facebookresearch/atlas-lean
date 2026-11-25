/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData

/-!
# Public clients of strong deformation data

The chosen deformation gives actual cancellation through its inclusion
and keeps stationarity on every further specified source.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.StrongDeformationData

variable {C : Type u} [Category.{v} C]
variable (P : Precylinder (𝟭 C)) {K L S : C} {i : K ⟶ L}

/-- Native monomorphism cancellation follows from the chosen retraction. -/
theorem cancel_inclusion (D : P.StrongDeformationData i)
    (f g : S ⟶ K) (h : f ≫ i = g ≫ i) : f = g := by
  have := D.mono
  exact (cancel_mono i).mp h

/-- Every smaller specified source retains the full stationary equation. -/
theorem stationary_on_smaller_source (D : P.StrongDeformationData i) (k : S ⟶ K) :
    P.I.map (k ≫ i) ≫ D.homotopy.h = (P.app S).π ≫ k ≫ i := by
  have h := (D.homotopy.precomp k).stationary
  change P.I.map (k ≫ i) ≫ D.homotopy.h = (P.app S).π ≫ (k ≫ i) ≫ 𝟙 L at h
  simpa only [Category.comp_id, Category.assoc] using h

/-- Identity data use the same chosen cylinder and retain a native relative
homotopy, so the identity deformation is available without existence input. -/
def identity_deformation (K : C) :
    P.RelativeLeftHomotopy (𝟙 K) (𝟙 K) (𝟙 K ≫ 𝟙 K) :=
  (Precylinder.StrongDeformationData.refl (P := P) K).homotopy

end MathlibExtTest.AlgebraicTopology.ModelCategory.StrongDeformationData
