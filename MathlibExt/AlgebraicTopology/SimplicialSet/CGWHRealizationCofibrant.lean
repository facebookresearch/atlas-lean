/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationCofibrations
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Cofibrancy of the actual native realization

The existing realization adjunction preserves the initial object, and the
existing native left-Quillen cofibration theorem maps the original empty
inclusion. Thus the actual realization is cofibrant, in every original
carrier and probe universe, without a supplied CW or cofibrancy witness.
-/

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen CGWH.modelCategory

universe u v

namespace SSet

/-- Every actual native realized simplicial set is cofibrant, through its
ORIGINAL empty inclusion and the SAME existing realization adjunction. -/
public theorem toCGWH_obj_isCofibrant (X : SSet.{v}) :
    IsCofibrant (SSet.toCGWH.{u, v}.obj X) := by
  let F := SSet.toCGWH.{u, v}
  letI : F.IsLeftAdjoint := ⟨_, ⟨SSet.sSetCGWHAdj.{u, v}⟩⟩
  let f : (⊥_ SSet.{v}) ⟶ X := initial.to X
  letI : Cofibration f := (SSet.modelCategoryQuillen.cofibration_iff f).mpr inferInstance
  letI : Cofibration (F.map f) := CGWH.modelCategory.toCGWH_map_cofibration f
  have hi : IsInitial (F.obj (⊥_ SSet.{v})) :=
    initialIsInitial.isInitialObj F (⊥_ SSet.{v})
  exact (isCofibrant_iff_of_isInitial (F.map f) hi).mpr inferInstance

end SSet

end
