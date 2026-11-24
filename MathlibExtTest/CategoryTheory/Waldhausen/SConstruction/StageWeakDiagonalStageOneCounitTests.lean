/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalStageOneCounit

/-!
# Stage-one counit-normalization tests

These tests pin the weak lift of the Stage counit, its underlying hom and
inverse, naturality, both Stage-zero face transports, the two degeneracy
relations, and the final source-first identity-edge normalization.  They make
no arbitrary-edge, generation, realization, K-zero, or additivity claim.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalStageOneCounitTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

variable {A B : StageWeakCategory C 1}

example (A : StageWeakCategory C 1) :
    stageOneWeakObj C ((stageOneEval C).obj A.obj) ≅ A :=
  stageOneCounitWeakIso C A

example (A : StageWeakCategory C 1) :
    (stageOneCounitWeakIso C A).hom.hom =
      (counitAppStageIso C A.obj).hom :=
  stageOneCounitWeakIso_hom_hom C A

example (A : StageWeakCategory C 1) :
    (stageOneCounitWeakIso C A).inv.hom =
      (counitAppStageIso C A.obj).inv :=
  stageOneCounitWeakIso_inv_hom C A

example (f : A ⟶ B) :
    stageOneWeakMap C ((stageOneEval C).map f.hom)
          (f.property (interval (0 : Fin 2) 1 (by decide))) ≫
        (stageOneCounitWeakIso C B).hom =
      (stageOneCounitWeakIso C A).hom ≫ f :=
  stageOneCounitWeakIso_hom_naturality C f

example (A : StageWeakCategory C 1)
    (h := stageOneWeakObj_reindex_d1 C ((stageOneEval C).obj A.obj)) :
    (reindexStageWeak C (SimplexCategory.δ 1)).map
        (stageOneCounitWeakIso C A).hom =
      eqToHom h ≫
        (stageWeakZeroIso C
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj A)).hom :=
  stageOneCounitWeakIso_reindex_d1_hom C A h

example (A : StageWeakCategory C 1)
    (h := stageOneWeakObj_reindex_d0 C ((stageOneEval C).obj A.obj)) :
    (reindexStageWeak C (SimplexCategory.δ 0)).map
        (stageOneCounitWeakIso C A).hom =
      eqToHom h ≫
        (stageWeakZeroIso C
          ((reindexStageWeak C (SimplexCategory.δ 0)).obj A)).hom :=
  stageOneCounitWeakIso_reindex_d0_hom C A h

example (A : StageWeakCategory C 1) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C
          (stageOneWeakObj C ((stageOneEval C).obj A.obj))) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 0)).map
            (stageOneCounitWeakIso C A).hom)) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C
        (stageOneCounitWeakIso C A).hom) :=
  stageOneCounitWeakIso_source_homMk_comp C A

example (A : StageWeakCategory C 1) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).map
            (stageOneCounitWeakIso C A).hom)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C A) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C
        (stageOneCounitWeakIso C A).hom) :=
  stageOneCounitWeakIso_target_homMk_comp C A

example (X : C) :
    (stageWeakDiagonalStageOneIdentityEdge C
        (stageOneWeakObj C X)).edge =
      (stageWeakDiagonalObjectEdge C X).edge :=
  stageWeakDiagonalStageOneIdentityEdge_stageOneWeakObj_edge C X

example (A : StageWeakCategory C 1) :
    (SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj A)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C A)) ≫
        inv (SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C
            ((reindexStageWeak C (SimplexCategory.δ 0)).obj A))) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C
          ((stageOneEval C).obj A.obj)) :=
  stageWeakDiagonalStageOneIdentityEdge_normalization C A

end StageWeakDiagonalStageOneCounitTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
