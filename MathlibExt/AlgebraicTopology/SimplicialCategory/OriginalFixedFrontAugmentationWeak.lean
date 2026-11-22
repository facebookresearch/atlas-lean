/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontDeformation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontZeroIso

/-!
# The SAME original fixed-front cosimplicial augmentation is degreewise Joyal weak

The original fixed-front operators form their full cosimplicial diagram.
Its actual constant-front projection and zero-object isomorphism give
the augmentation to the walking arrow. Every original degree map is a
categorical equivalence by the genuine vertex-fixed deformation.
No Reedy cofibrancy or cosimplicial-resolution outcome is assumed here.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The SAME original full fixed-front cosimplicial diagram, retaining all original operators. -/
def cosimplicialObject : CosimplicialObject SSet.{u} where
  obj n := FixedFrontCollapse.object n.len
  map θ := FixedFrontOperators.map θ
  map_id n := FixedFrontOperators.map_id n.len
  map_comp θ ψ := FixedFrontOperators.map_comp θ ψ

/-- EVERY actual original operator retains the SAME original constant-front projection. -/
theorem toZero_operator {n m : SimplexCategory} (θ : n ⟶ m) :
    FixedFrontOperators.map.{u} θ ≫ toZero m.len = toZero n.len := by
  have he : θ ≫ SimplexCategory.const m ⦋0⦌ 0 = SimplexCategory.const n ⦋0⦌ 0 := by
    ext j
    rfl
  exact (FixedFrontOperators.map_comp θ (SimplexCategory.const m ⦋0⦌ 0)).symm.trans
    (congrArg FixedFrontOperators.map he)

/-- The actual full original fixed-front augmentation to the SAME walking arrow. -/
def augmentation : cosimplicialObject.{u} ⟶ (Functor.const SimplexCategory).obj (Δ[1] : SSet.{u}) where
  app n := toZero n.len ≫ zeroObjectIso.hom
  naturality n m θ := by
    change FixedFrontOperators.map θ ≫ (toZero m.len ≫ zeroObjectIso.hom) =
      (toZero n.len ≫ zeroObjectIso.hom) ≫ 𝟙 (Δ[1] : SSet.{u})
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ zeroObjectIso.hom) (toZero_operator θ)).trans (Category.comp_id _).symm)

/-- EVERY original fixed-front augmentation degree is a genuine categorical equivalence. -/
theorem augmentation_app_categoricalEquivalence (n : SimplexCategory) :
    SSet.categoricalEquivalences (augmentation.{u}.app n) :=
  RespectsIso.postcomp SSet.categoricalEquivalences zeroObjectIso.hom (toZero n.len)
    (toZero_categoricalEquivalence n.len)

/-- EVERY original fixed-front cosimplicial operator is a genuine categorical equivalence on the SAME objects. -/
theorem operator_categoricalEquivalence {n m : SimplexCategory} (θ : n ⟶ m) :
    SSet.categoricalEquivalences (FixedFrontOperators.map.{u} θ) :=
  SSet.categoricalEquivalences.of_postcomp (FixedFrontOperators.map θ) (toZero m.len)
    (toZero_categoricalEquivalence m.len) ((toZero_operator θ).symm ▸ toZero_categoricalEquivalence n.len)

/-- The SAME full original augmentation retains its literal original constant-front and zero-object inverse maps. -/
theorem augmentation_app (n : SimplexCategory) : augmentation.{u}.app n = toZero n.len ≫ zeroObjectIso.hom := rfl

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
