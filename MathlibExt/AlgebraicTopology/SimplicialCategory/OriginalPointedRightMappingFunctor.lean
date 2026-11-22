/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHom
import MathlibExt.AlgebraicTopology.SimplicialSet.PointedRightMappingSpace
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.RightMappingBrown

/-!
# The same original pointed right-mapping functor

The original two boundary faces form the literal two-vertex coproduct
map. The established full pointed right-mapping functor then retains
the same join simplices, every operator and original endpoint equation.
The actual categorical weak criterion supplies weakness between the
original quasicategory carriers.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The literal two-boundary-face adapter retains both entire original endpoint maps. -/
def endpointPairFunctor : Category.{u} ⥤ Under SSet.PointedRightMappingSpace.endpointPair.{u} where
  obj X := SSet.PointedRightMappingSpace.of X.right (source X) (target X)
  map {X Y} f := Under.homMk f.right (by
    change coprod.desc (source X) (target X) ≫ f.right = coprod.desc (source Y) (target Y)
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, coprod.inl_desc, source_map]
    · rw [coprod.inr_desc_assoc, coprod.inr_desc, target_map])
  map_id X := by
    apply Under.UnderMorphism.ext
    rfl
  map_comp f g := by
    apply Under.UnderMorphism.ext
    rfl

/-- The canonical original full right-mapping functor applied to the same original pointed category. -/
def rightMappingFunctor : Category.{u} ⥤ SSet.{u} :=
  endpointPairFunctor ⋙ SSet.PointedRightMappingSpace.functor

/-- The entire pointed right-mapping object is the same original mapping space at both original boundary maps. -/
def rightMappingOriginalIso (X : Category.{u}) :
    rightMappingFunctor.obj X ≅ SSet.mappingSpaceRight X.right (source X) (target X) :=
  SSet.PointedRightMappingSpace.originalIso X.right (source X) (target X)

/-- Every whole original pointed right-mapping arrow retains the canonical original unwrapped source-map square. -/
theorem rightMappingOriginalIso_naturality {X Y : Category.{u}} (f : X ⟶ Y) :
    rightMappingFunctor.map f ≫ (rightMappingOriginalIso Y).hom =
      (rightMappingOriginalIso X).hom ≫ SSet.mappingSpaceRight.map X.right (source X) (target X) f.right ≫
        (SSet.PointedRightMappingSpace.endpointIso (source_map f) (target_map f)).hom := by
  ext n σ
  apply Subtype.ext
  change (SSet.PointedRightMappingSpace.object (endpointPairFunctor.obj X)).obj n at σ
  change (((rightMappingOriginalIso Y).hom.app n)
      ((SSet.PointedRightMappingSpace.map (endpointPairFunctor.map f)).app n σ)).val =
    (((SSet.PointedRightMappingSpace.endpointIso (source_map f) (target_map f)).hom.app n)
      ((SSet.mappingSpaceRight.map X.right (source X) (target X) f.right).app n
        (((rightMappingOriginalIso X).hom.app n) σ))).val
  have hl := SSet.PointedRightMappingSpace.originalIso_hom_val Y.right (source Y) (target Y) n
    ((SSet.PointedRightMappingSpace.map (endpointPairFunctor.map f)).app n σ)
  have hr := SSet.PointedRightMappingSpace.endpointIso_hom_val (source_map f) (target_map f) n
    ((SSet.mappingSpaceRight.map X.right (source X) (target X) f.right).app n
      (((rightMappingOriginalIso X).hom.app n) σ))
  exact hl.trans
    ((congrArg (fun h => h ≫ f.right)
      (SSet.PointedRightMappingSpace.originalIso_hom_val X.right (source X) (target X) n σ).symm).trans
        hr.symm)

/-- The same original categorical weak map of quasicategory carriers is weak on the full pointed right-mapping
functor. -/
theorem rightMappingFunctor_map_weak {X Y : Category.{u}} (f : X ⟶ Y)
    [SSet.Quasicategory X.right] [SSet.Quasicategory Y.right]
    (hf : SSet.categoricalEquivalences f.right) :
    SSet.realizationWeakEquivalences (rightMappingFunctor.map f) := by
  have hw := hf.rightMappingSpaceMap_weak (source X) (target X)
  have hc : SSet.realizationWeakEquivalences
      ((rightMappingOriginalIso X).hom ≫ SSet.mappingSpaceRight.map X.right (source X) (target X) f.right ≫
        (SSet.PointedRightMappingSpace.endpointIso (source_map f) (target_map f)).hom) :=
    SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso (rightMappingOriginalIso X).hom)
      (SSet.realizationWeakEquivalences.comp_mem _ _ hw
        (SSet.realizationWeakEquivalences.of_isIso
          (SSet.PointedRightMappingSpace.endpointIso (source_map f) (target_map f)).hom))
  rw [← rightMappingOriginalIso_naturality] at hc
  exact (SSet.realizationWeakEquivalences.cancel_right_of_respectsIso _ (rightMappingOriginalIso Y).hom).mp hc

end CategoryTheory.CoherentRealization.OriginalPointed
