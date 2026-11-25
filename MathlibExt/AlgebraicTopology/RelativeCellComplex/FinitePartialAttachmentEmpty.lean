/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentMaps

/-!
# The original empty finite attachment

The actual pushout of the empty original family is isomorphic to its
original root object. Both inverse maps and the complete root formula
come from the original partial-attachment universal property.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace HomotopicalAlgebra.FinitePartialAttachment

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {I : Type w} {A B : I → C} (g : ∀ i, A i ⟶ B i) {X : C} (a : ∀ i, A i ⟶ X)

/-- The full original empty-family descender returns to the same root object. -/
def emptyInverse : object g a ∅ ⟶ X :=
  desc g a ∅ (𝟙 X) (fun i => False.elim (Finset.notMem_empty i.1 i.2))
    (fun i => False.elim (Finset.notMem_empty i.1 i.2))

/-- The original root and empty-family descender are inverse in the root direction. -/
theorem root_emptyInverse : root g a ∅ ≫ emptyInverse g a = 𝟙 X :=
  root_desc g a ∅ _ _ _

/-- The original empty-family descender and root are inverse on the entire partial attachment. -/
theorem emptyInverse_root : emptyInverse g a ≫ root g a ∅ = 𝟙 (object g a ∅) := by
  apply hom_ext g a ∅
  · rw [← Category.assoc, root_emptyInverse, Category.id_comp, Category.comp_id]
  · intro i
    exact False.elim (Finset.notMem_empty i.1 i.2)

/-- The actual empty-family attachment is isomorphic to its original root, with the same
root map. -/
def emptyIso : X ≅ object g a ∅ where
  hom := root g a ∅
  inv := emptyInverse g a
  hom_inv_id := root_emptyInverse g a
  inv_hom_id := emptyInverse_root g a

/-- The same original empty-family root is invertible. -/
theorem root_empty_isIso : IsIso (root g a ∅) := (emptyIso g a).isIso_hom

end HomotopicalAlgebra.FinitePartialAttachment
