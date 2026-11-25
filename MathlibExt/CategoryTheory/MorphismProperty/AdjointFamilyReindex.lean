/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

/-!
# Exact generator families with surjective original labels

Reindex the actual left functors while retaining the literal base arrows.
Surjectivity gives equality of the entire generator property.
-/

set_option autoImplicit false
universe uS uT uC vC uD vD
open CategoryTheory MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type uS} {T : Type uT}

/-- Original surjective labels describe exactly the same whole free-generator family. -/
theorem adjointFamilyGenerators_reindex (j : S → T) (hj : Function.Surjective j)
    (L : T → C ⥤ D) (P : MorphismProperty C) :
    adjointFamilyGenerators (fun s => L (j s)) P = adjointFamilyGenerators L P := by
  rw [adjointFamilyGenerators_eq_iSup_strictMap, adjointFamilyGenerators_eq_iSup_strictMap]
  ext X Y f
  simp only [MorphismProperty.iSup_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨j s, hs⟩
  · rintro ⟨t, ht⟩
    obtain ⟨s, rfl⟩ := hj t
    exact ⟨s, ht⟩

end CategoryTheory.MorphismProperty
