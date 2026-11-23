/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowStableComparison

noncomputable section

open CategoryTheory
open AlgebraicKTheory.StableGL
open scoped unitInterval

universe u

variable (R : Type u) [Ring R]

example : ordinaryBGL R ⟶ SSet.toTop.obj
    (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
  finiteFreeRowStableZeroComparison R

example (n : ℕ) :
    TopCat.Homotopy (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n))
      (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
        finiteFreeRowStableZeroComparison R) :=
  finiteFreeRowStableZeroComparisonStageHomotopy R n

example (n : ℕ)
    (x : SSet.toTop.obj (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))) :
    finiteFreeRowStableZeroComparisonStageHomotopy R n (0, x) =
      SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n) x :=
  (finiteFreeRowStableZeroComparisonStageHomotopy R n).map_zero_left x

example (n : ℕ)
    (x : SSet.toTop.obj (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))) :
    finiteFreeRowStableZeroComparisonStageHomotopy R n (1, x) =
      finiteFreeRowStableZeroComparison R
        (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) x) :=
  (finiteFreeRowStableZeroComparisonStageHomotopy R n).map_one_left x

example (A : AddCommGrpCat.{u}) (q n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
        (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)) =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
          (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)) ≫
        ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
          (finiteFreeRowStableZeroComparison R) :=
  finiteFreeRowStableZeroComparison_homology_stage R A q n

example (q n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor q).map
        (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)) =
      (AlgebraicTopology.singularIntegralHomologyFunctor q).map
          (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)) ≫
        (AlgebraicTopology.singularIntegralHomologyFunctor q).map
          (finiteFreeRowStableZeroComparison R) :=
  finiteFreeRowStableZeroComparison_integral_stage R q n

example (q n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor q).map
        (SSet.toTop.map
          (finiteFreeRowStageZeroNerveMap (Matrix (Fin 2) (Fin 2) ℤ) n)) =
      (AlgebraicTopology.singularIntegralHomologyFunctor q).map
          (SSet.toTop.map (nerveMap
            (finiteToStableCategoryMap (Matrix (Fin 2) (Fin 2) ℤ) n).toFunctor)) ≫
        (AlgebraicTopology.singularIntegralHomologyFunctor q).map
          (finiteFreeRowStableZeroComparison (Matrix (Fin 2) (Fin 2) ℤ)) :=
  finiteFreeRowStableZeroComparison_integral_stage (Matrix (Fin 2) (Fin 2) ℤ) q n
