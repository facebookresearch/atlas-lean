/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoresolution
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinducedAcyclicity
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoefficientFunctor

/-! # Native acyclicity of the actual original coinduction terms -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [LocallyCompactSpace G]

/-- The actual original coinduced coefficient is native-acyclic in every positive degree. -/
theorem coind_native_isZero_succ (A : DiscreteAbelianAction.{g, max g w} G) (n : ℕ) :
    IsZero (continuousCohomology.{0, g, w} (n + 1) (toTopRep.obj (coind.{g, w}.obj A))) := by
  let F := ContinuousCohomology.homogeneousCochainsFunctor.{0, g, w} (k := ℤ) (G := G) ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{max g w} ℤ) (ComplexShape.up ℕ) (n + 1)
  let e := F.mapIso (coindToTopRepIso.{g, w} G A)
  have hz := ContinuousCohomology.isZero_coind₁_succ.{0, g, w} (toTopRep.obj A) n
  exact IsZero.of_iso hz e

/-- Every actual positive monad power is native-acyclic in every positive degree. -/
theorem coindPower_native_isZero_succ (A : DiscreteAbelianAction.{g, max g w} G)
    (p n : ℕ) :
    IsZero (continuousCohomology.{0, g, w} (n + 1)
      (toTopRep.obj ((Monad.monadPow (coindMonad.{g, w} G) (p + 1)).obj A))) := by
  let B := (Monad.monadPow (coindMonad.{g, w} G) p).obj A
  let F := ContinuousCohomology.homogeneousCochainsFunctor.{0, g, w} (k := ℤ) (G := G) ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{max g w} ℤ) (ComplexShape.up ℕ) (n + 1)
  let e := F.mapIso (toTopRep.mapIso
    (eqToIso (Monad.monadPow_succ_obj_eq (coindMonad.{g, w} G) p A)))
  exact IsZero.of_iso (coind_native_isZero_succ.{g, w} G B n) e

/-- The actual canonical coresolution coefficients are native-acyclic terms. -/
theorem coindCoresolution_native_isZero_succ (A : DiscreteAbelianAction.{g, max g w} G)
    (p n : ℕ) :
    IsZero (continuousCohomology.{0, g, w} (n + 1)
      (toTopRep.obj ((Monad.coresolution (coindMonad.{g, w} G) A).obj
          (SimplexCategory.mk p)))) := by
  let F := ContinuousCohomology.homogeneousCochainsFunctor.{0, g, w} (k := ℤ) (G := G) ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{max g w} ℤ) (ComplexShape.up ℕ) (n + 1)
  let e := F.mapIso (toTopRep.mapIso (Monad.coresolutionObjIso (coindMonad.{g, w} G) A p))
  exact IsZero.of_iso (coindPower_native_isZero_succ.{g, w} G A p n) e

end CategoryTheory.DiscreteAbelianAction
