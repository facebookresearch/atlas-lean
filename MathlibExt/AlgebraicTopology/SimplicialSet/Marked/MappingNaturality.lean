/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingComplex

/-!
# Same-map naturality of the actual marked mapping complexes

The original source and target compositions act strictly on the marked
standard-simplex complexes, and their two actions commute. All formulas
retain the same parameter and original marked maps at every value universe.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Target identity induces the same original identity of the mapping complex. -/
@[simp] theorem mappingComplexPost_id (k : ParameterMarking) (X Y : Marked.{u}) :
    mappingComplexPost k X (𝟙 Y) = 𝟙 (mappingComplex k X Y) := by
  ext n f
  apply Hom.ext
  rfl

/-- Actual target compositions give the same composed simplicial map. -/
theorem mappingComplexPost_comp (k : ParameterMarking) (X : Marked.{u})
    {Y Z A : Marked.{u}} (f : Y ⟶ Z) (g : Z ⟶ A) :
    mappingComplexPost k X (f ≫ g) = mappingComplexPost k X f ≫ mappingComplexPost k X g := by
  ext n a
  apply Hom.ext
  rfl

/-- Source identity retains the original identity simplicial map. -/
@[simp] theorem mappingComplexPre_id (k : ParameterMarking) (X Y : Marked.{u}) :
    mappingComplexPre k (𝟙 X) Y = 𝟙 (mappingComplex k X Y) := by
  ext n a
  apply Hom.ext
  rfl

/-- The source action is contravariant on those same original marked maps. -/
theorem mappingComplexPre_comp (k : ParameterMarking) {X Y Z : Marked.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Marked.{u}) :
    mappingComplexPre k (f ≫ g) A = mappingComplexPre k g A ≫ mappingComplexPre k f A := by
  ext n a
  apply Hom.ext
  rfl

/-- The original source and target actions commute without changing either map. -/
theorem mappingComplexPre_post (k : ParameterMarking) {X X' Y Y' : Marked.{u}}
    (f : X' ⟶ X) (g : Y ⟶ Y') :
    mappingComplexPre k f Y ≫ mappingComplexPost k X' g =
      mappingComplexPost k X g ≫ mappingComplexPre k f Y' := by
  ext n a
  apply Hom.ext
  rfl

end SSet.Marked
