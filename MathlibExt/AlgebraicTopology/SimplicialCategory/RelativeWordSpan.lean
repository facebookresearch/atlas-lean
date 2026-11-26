/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeQuiver

/-!
# The actual original free attaching span in the normalized word enrichment

The original attaching Hom maps and original quiver inclusion extend
through the existing free enrichment. Their entire enriched square
commutes in the normalized word carrier, with the same original objects,
generators, identity maps and arbitrary composites.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C : FixedObjects O}

/-- The actual original free-domain attaching map supplied by the same original Hom assignment. -/
def domainMap (T : Data C) : FreeQuiver.object T.domain ⟶ C :=
  FreeQuiver.extend T.domain C T.attaching

/-- The actual original free map of the same componentwise quiver inclusion. -/
def targetMap (T : Data C) : FreeQuiver.object T.domain ⟶ FreeQuiver.object T.target :=
  FreeQuiver.map T.inclusion

/-- The actual whole target free enrichment maps by the same normalized target-letter maps. -/
def newMap (T : Data C) : FreeQuiver.object T.target ⟶ object T :=
  FreeQuiver.extend T.target (object T) (newHom T)

/-- The entire original enriched attaching square commutes on every original object and free path. -/
theorem domainMap_oldMap (T : Data C) : domainMap T ≫ oldMap T = targetMap T ≫ newMap T := by
  apply FreeQuiver.generators_ext T.domain
  intro x y
  rw [homMap_comp, homMap_comp, homMap_oldMap]
  change FreeQuiver.generator T.domain x y ≫
      (homMap (FreeQuiver.extend T.domain C T.attaching) x y ≫ oldHom T x y) =
    FreeQuiver.generator T.domain x y ≫
      (homMap (FreeQuiver.map T.inclusion) x y ≫
        homMap (FreeQuiver.extend T.target (object T) (newHom T)) x y)
  rw [← Category.assoc, FreeQuiver.generator_extend, ← Category.assoc,
    FreeQuiver.generator_map, Category.assoc, FreeQuiver.generator_extend]
  exact (inclusion_square T x y).symm

/-- The genuine whole enriched square over the original free attaching span. -/
theorem square (T : Data C) : CommSq (domainMap T) (targetMap T) (oldMap T) (newMap T) :=
  ⟨domainMap_oldMap T⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
