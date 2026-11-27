/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplexCategory.ProperImage
public import MathlibExt.AlgebraicTopology.SimplicialObject.Matching
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The original image labels for cofree matching coordinates

Every original nonsurjective ordinal map has its actual proper-mono
image matching object. Its original epi map into that image determines
the coefficient coordinate. Alternative proper-face factorizations
map from this same original image and retain both exact original maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.CofreeMatching

/-- The actual original image is proper for every nonsurjective original ordinal map. -/
theorem image_len_lt {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : ¬ Epi θ) :
    (image θ).len < m :=
  SimplexCategory.image_len_lt_of_not_epi θ hθ

/-- The same full original image proper-mono matching index. -/
abbrev imageMatchingIndex {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : ¬ Epi θ) : matchingIndex m :=
  ⟨StructuredArrow.mk (image.ι θ).op, (inferInstance : Mono (image.ι θ)),
    SimplexCategory.image_len_lt_of_not_epi θ hθ⟩

/-- Every alternative original proper-face factorization receives the same original
image-matching arrow. -/
def imageToFactor {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : ¬ Epi θ)
    (a : matchingIndex m) (r : ⦋n⦌ ⟶ a.obj.right.unop)
    (hr : r ≫ a.obj.hom.unop = θ) : a ⟶ imageMatchingIndex θ hθ := by
  let _ : Mono a.obj.hom.unop := a.property.1
  let φ := image.lift (show MonoFactorisation θ from ⟨a.obj.right.unop, a.obj.hom.unop, r, hr⟩)
  exact ObjectProperty.homMk (StructuredArrow.homMk φ.op (by
    apply Quiver.Hom.unop_inj
    exact image.lift_fac _))

end CategoryTheory.SimplicialObject.CofreeMatching
