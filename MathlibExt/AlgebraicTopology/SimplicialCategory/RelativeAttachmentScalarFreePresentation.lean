/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordMaps
import MathlibExt.CategoryTheory.Category.RelativeFreePresentation

/-!
# Actual scalar free presentations of original enriched attachments

In every scalar degree the full normalized attachment is the genuine
relative-word category of its original enrichment and the target arrows
outside the original attaching image. The constructed free presentation
retains all original labels, old complete paths and actual new letters.
Boundary letters evaluate by the same original attaching map.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O} (T : Data C) (q : SimplexCategoryᵒᵖ)

/-- The actual scalar attachment has its original normalized-word category dictionary. -/
theorem scalarCategory_eq : scalarCategory (object T) q =
    @RelativeWords.category O (scalarCategory C q) (newAt T q) := rfl

/-- Construct the actual full scalar free presentation from the original scalar presentation. -/
def scalarFreePresentation (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    FreePresentation.{u,u,u} (scalarCategory (object T) q) := by
  rw [scalarCategory_eq]
  exact P.relative (newAt T q)

/-- Its generator family retains the original arrows and exactly the genuine target complement. -/
theorem scalarFreePresentation_quiver (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    (scalarFreePresentation T q P).quiver = FreePaths.sumQuiver P.quiver (newAt T q) := rfl

/-- Every complete old generating path evaluates as the SAME old full Hom simplex. -/
theorem scalarFreePresentation_oldPath (P : FreePresentation.{u,u,u} (scalarCategory C q))
    {x y : O} (p : @Quiver.Path O P.quiver x y) :
    (scalarFreePresentation T q P).map (FreePaths.oldPath P.quiver (newAt T q) p) =
      oldWord T q (P.map p) :=
  P.relativeMap_oldPath (newAt T q) p

/-- Every actual new target simplex evaluates as its same supplied normalized letter. -/
theorem scalarFreePresentation_new (P : FreePresentation.{u,u,u} (scalarCategory C q))
    {x y : O} (g : newAt T q x y) :
    (scalarFreePresentation T q P).map
        (@Quiver.Hom.toPath O (FreePaths.sumQuiver P.quiver (newAt T q)) x y (Sum.inr g)) =
      letter T q g.val := by
  rw [letter_new]
  exact P.relativeMap_new (newAt T q) g

/-- Original attaching-domain letters keep their actual original whole Hom interpretation. -/
theorem scalarBoundary_readback {x y : O} (a : (T.domain.Hom x y).obj q) :
    (newHom T x y).app q ((T.inclusion x y).app q a) =
      (oldHom T x y).app q ((T.attaching x y).app q a) :=
  letter_image T q a

/-- The actual full scalar old enriched map is the literal original old-word inclusion. -/
theorem scalarOldMap_readback {x y : O} (a : (hom C x y).obj q) :
    (homMap (oldMap T) x y).app q a = oldWord T q a := by
  rw [homMap_oldMap]
  rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
