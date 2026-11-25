/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.RelativeHomotopy

/-!
# Public clients of stationary relative homotopies

Restriction to a smaller subobject and postcomposition retain the entire
constant-cylinder equation. Deformation data consequently restrict to the
specified retract, with either endpoint used in that equation.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RelativeHomotopy

variable {C : Type u} [Category.{v} C]
variable (P : Precylinder (𝟭 C)) {S T X Y Z : C}

/-- The whole cylinder restriction remains constant after both operations. -/
theorem stationary_after_restriction_and_postcomp {i : S ⟶ X}
    {f₀ f₁ : X ⟶ Y} (H : P.RelativeLeftHomotopy i f₀ f₁)
    (k : T ⟶ S) (p : Y ⟶ Z) :
    P.I.map (k ≫ i) ≫ (H.h ≫ p) =
      (P.app T).π ≫ (k ≫ i) ≫ (f₀ ≫ p) :=
  ((H.precomp k).postcomp p).stationary

/-- A deformation homotopy restricts to the identity on its retract. -/
theorem deformation_stationary {i : S ⟶ X} {r : X ⟶ S}
    (hi : i ≫ r = 𝟙 S) (H : P.RelativeLeftHomotopy i (𝟙 X) (r ≫ i)) :
    P.I.map i ≫ H.h = (P.app S).π ≫ i ∧
      P.I.map i ≫ H.h = (P.app S).π ≫ i ≫ (r ≫ i) := by
  constructor
  · simpa only [Category.comp_id] using H.stationary
  · calc
      P.I.map i ≫ H.h = (P.app S).π ≫ i := by
        simpa only [Category.comp_id] using H.stationary
      _ = (P.app S).π ≫ i ≫ (r ≫ i) := by
        rw [← Category.assoc i, hi, Category.id_comp]

/-- Forgetting stationarity retains a native homotopy with its prescribed
endpoint restrictions, for the same chosen functorial cylinder. -/
def restricted_native_homotopy {i : S ⟶ X} {f₀ f₁ : X ⟶ Y}
    (H : P.RelativeLeftHomotopy i f₀ f₁) :
    (P.app S).LeftHomotopy (i ≫ f₀) (i ≫ f₁) :=
  P.precompLeftHomotopy H.toLeftHomotopy i

end MathlibExtTest.AlgebraicTopology.ModelCategory.RelativeHomotopy
