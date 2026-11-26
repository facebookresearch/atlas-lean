/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordLayerColimit

/-!
# The actual original relative-word attachment under source change

Compose the SAME original attaching Hom maps with a supplied full
original fixed-label functor. Both quivers and the original inclusion
remain unchanged. Whole normalized-word evaluation constructs the actual
source comparison, preserving all old Hom maps, target letters and
original scalar operators. The finite word filtration is retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME original attaching data with only the actual original source Hom map composed. -/
def sourceChange (T : Data C) (F : C ⟶ D) : Data D where
  domain := T.domain
  target := T.target
  inclusion := T.inclusion
  mono := T.mono
  attaching x y := T.attaching x y ≫ homMap F x y

/-- Both actual old maps and the unchanged target generators form the SAME whole relative attaching cocone. -/
theorem sourceChange_square (T : Data C) (F : C ⟶ D) (x y : O) :
    T.inclusion x y ≫ newHom (sourceChange T F) x y =
      T.attaching x y ≫ homMap (F ≫ oldMap (sourceChange T F)) x y := by
  exact (inclusion_square (sourceChange T F) x y).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => T.attaching x y ≫ homMap F x y ≫ k)
        (homMap_oldMap (sourceChange T F) x y).symm).trans
          (congrArg (fun k => T.attaching x y ≫ k)
            (homMap_comp F (oldMap (sourceChange T F)) x y).symm)))

/-- The genuine actual entire source-comparison map evaluates every original normalized relative word. -/
def sourceChangeMap (T : Data C) (F : C ⟶ D) : object T ⟶ object (sourceChange T F) :=
  desc T (F ≫ oldMap (sourceChange T F)) (newHom (sourceChange T F)) (sourceChange_square T F)

/-- The SAME full original old-Hom inclusion commutes with the actual entire source comparison. -/
theorem oldMap_sourceChangeMap (T : Data C) (F : C ⟶ D) :
    oldMap T ≫ sourceChangeMap T F = F ≫ oldMap (sourceChange T F) :=
  oldMap_desc T _ _ _

/-- Every unchanged original target generator is retained by the SAME full source-comparison map. -/
theorem newHom_sourceChangeMap (T : Data C) (F : C ⟶ D) (x y : O) :
    newHom T x y ≫ homMap (sourceChangeMap T F) x y = newHom (sourceChange T F) x y :=
  newHom_desc T _ _ _ x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
