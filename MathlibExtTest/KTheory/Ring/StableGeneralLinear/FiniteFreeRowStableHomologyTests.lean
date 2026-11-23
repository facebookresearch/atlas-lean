/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowStableHomology

noncomputable section

open CategoryTheory Limits
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example (n : ℕ) :
    SSet.homologyMap (C := AddCommGrpCat.{u})
      (nerveMap (finiteToStableCategoryMap R n).toFunctor) A q ≫
        finiteFreeRowStableHomologyComparison R A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q :=
  finiteFreeRowStableHomologyComparison_stage R A q n

example (n : ℕ) :
    colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
        finiteFreeRowHomologyColimitComparison R A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q :=
  finiteFreeRowHomologyColimitComparison_ι R A q n

example (n : ℕ)
    (x : ((finiteBGLNerveDiagram R).obj n).homology (C := AddCommGrpCat.{u}) A q) :
    finiteFreeRowHomologyColimitComparison R A q
        (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q) n x) =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q x :=
  ConcreteCategory.congr_hom (finiteFreeRowHomologyColimitComparison_ι R A q n) x

example (n : ℕ) :
    colimit.ι
        (finiteBGLNerveDiagram.{0} (Matrix (Fin 2) (Fin 2) ℤ) ⋙
          SSet.homologyFunctor (C := AddCommGrpCat.{0})
            AlgebraicTopology.singularIntegralCoefficients.{0} q) n ≫
        finiteFreeRowHomologyColimitComparison.{0} (Matrix (Fin 2) (Fin 2) ℤ)
          AlgebraicTopology.singularIntegralCoefficients.{0} q =
      SSet.homologyMap (C := AddCommGrpCat.{0})
        (finiteFreeRowStageZeroNerveMap.{0} (Matrix (Fin 2) (Fin 2) ℤ) n)
        AlgebraicTopology.singularIntegralCoefficients.{0} q :=
  finiteFreeRowHomologyColimitComparison_ι.{0} (Matrix (Fin 2) (Fin 2) ℤ)
    AlgebraicTopology.singularIntegralCoefficients.{0} q n

end
