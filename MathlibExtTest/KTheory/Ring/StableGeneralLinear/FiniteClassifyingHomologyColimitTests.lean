/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingHomologyColimit

noncomputable section

open CategoryTheory Limits
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R]

example (A : AddCommGrpCat.{u}) (q : ℕ) :
    colimit (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) ≅
      (nerve (ClassifyingCategory R)).homology (C := AddCommGrpCat.{u}) A q :=
  finiteBGLHomologyColimitIso R A q

example (A : AddCommGrpCat.{u}) (q n : ℕ) :
    colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
        (finiteBGLHomologyColimitIso R A q).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap (finiteToStableCategoryMap R n).toFunctor) A q :=
  finiteBGLHomologyColimitIso_ι R A q n

#check AlgebraicKTheory.StableGL.finiteBGLHomologyCoconeIsColimit
#check AlgebraicKTheory.StableGL.finiteBGLHomologyColimitIso
#check AlgebraicKTheory.StableGL.finiteBGLHomologyColimitIso_ι
