/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundaryCellScalarPresentation
import MathlibExt.CategoryTheory.Category.FixedLabelPathMaps

/-!
# Full original boundary generator readbacks

The original complete scalar presentation is read on its same old
arrow inclusion and all full path maps. Every original endpoint label
is retained, and the full actual old Hom map is recovered.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeBoundaryCells
open RelativeWords
variable {O : Type u} {C D : FixedObjects O} {f : C ⟶ D}
  (a : AttachCells.{u} (boundaryFamily O).homFamily f)

/-- The literal old-generator inclusion in this actual full boundary attachment. -/
def generatorInclusion (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) {x y : O} :
    P.quiver.Hom x y → (scalarPresentation a q P).quiver.Hom x y := Sum.inl

/-- Every complete original path is retained by the SAME full boundary-attachment Hom map. -/
theorem scalarPresentation_oldPath (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) {x y : O}
    (p : @Quiver.Path O P.quiver x y) :
    (scalarPresentation a q P).map
        (FixedLabelPathMaps.mapPath P.quiver (scalarPresentation a q P).quiver
          (generatorInclusion a q P) p) =
      (homMap f x y).app q (P.map p) :=
  FreeIndexedMonoPushout.scalarPresentation_oldPath (fun i => quiverMap (index (a.π i)))
    (fun i => quiverMap_mono (index (a.π i)))
    (domainCofan a) (targetCofan a) (domainIsColimit a) (targetIsColimit a)
    a.m (coproductMap a) a.g₁ f a.g₂ a.isPushout q P p

/-- Every actual old boundary generator is included injectively without changing its original label pair. -/
theorem generatorInclusion_injective (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) (x y : O) :
    Function.Injective (@generatorInclusion O C D f a q P x y) := Sum.inl_injective

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeBoundaryCells
