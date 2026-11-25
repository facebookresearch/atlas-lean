/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTesting
public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData

/-!
# Strong deformation data for anodyne maps

A supplied retraction of an anodyne map into a naive fibrant target extends
the constant source homotopy to the specified cylinder. The full source
restriction gives stationarity, and the strong datum keeps that exact
retraction. Naive fibrancy of the source supplies a retraction when none
has been chosen.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Lemma 2.4.33. The given-retraction version displays the minimal
target-fibrancy requirement. It needs no initial object, separate
monicity premise, model structure or over-retraction condition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C]
  [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- Any supplied retraction is retained literally in strong deformation
data, with the entire homotopy stationary on the original map. -/
theorem exists_strongDeformationData_of_anodyne_retraction {X Y : C}
    (i : X ⟶ Y) (hi : An i) (hY : An.naiveFibrantObjects Y)
    (r : Y ⟶ X) (hr : i ≫ r = 𝟙 X) :
    ∃ D : P.StrongDeformationData i, D.retraction = r := by
  let H_X : (P.app X).LeftHomotopy (i ≫ 𝟙 Y) (i ≫ (r ≫ i)) :=
    { h := (LeftHomotopy.refl (P.app X) i).h
      h₀ := by
        simpa only [Category.comp_id] using (LeftHomotopy.refl (P.app X) i).h₀
      h₁ := by
        simpa only [← Category.assoc, hr, Category.id_comp] using
          (LeftHomotopy.refl (P.app X) i).h₁ }
  obtain ⟨H, hH⟩ := extendLeftHomotopy_of_anodyne P An i hi hY (𝟙 Y) (r ≫ i) H_X
  refine ⟨{ retraction := r, retract := hr, homotopy :=
    { h := H.h, h₀ := H.h₀, h₁ := H.h₁, stationary := ?_ } }, rfl⟩
  simpa only [H_X, LeftHomotopy.refl_h, Category.comp_id] using hH

/-- An anodyne map between naive fibrant objects has strong deformation
data for the same specified functorial cylinder. -/
theorem nonempty_strongDeformationData_of_anodyne {X Y : C}
    (i : X ⟶ Y) (hi : An i) (hX : An.naiveFibrantObjects X)
    (hY : An.naiveFibrantObjects Y) : Nonempty (P.StrongDeformationData i) := by
  obtain ⟨r, hr⟩ := (An.naiveFibrantObjects_iff_extensions X).mp hX i hi (𝟙 X)
  obtain ⟨D, _⟩ := exists_strongDeformationData_of_anodyne_retraction P An i hi hY r hr
  exact ⟨D⟩

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
