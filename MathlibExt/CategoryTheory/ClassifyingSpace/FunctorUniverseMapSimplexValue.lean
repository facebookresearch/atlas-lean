/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap

/-!
# Every original mixed realization-map simplex value

The SAME original functor map has its original larger recipe. Actual source
and target lift homeomorphism simplex values, actual chain-map naturality and
both inverse laws recover its entire simplex image, in independent original
Obj/Hom universes. No original map/point/root or working choice is replaced.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD wExtra

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

private def originalSimplexValueLiftFunctor (F : C ⥤ D) :
    ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} C) ⥤
      ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} D) :=
  (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
    max uC vC uD vD wExtra, vC, uC} C).inverse ⋙ F ⋙
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
      max uC vC uD vD wExtra, vD, uD} D).functor

private def originalSimplexValueRecipe (F : C ⥤ D) :
    C(SSet.toTop.obj (nerve C), SSet.toTop.obj (nerve D)) :=
  (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD wExtra}
    D).toHomotopyEquiv.toFun.comp
      ((SSet.toTop.map (nerveMap
        (originalSimplexValueLiftFunctor.{uC, vC, uD, vD, wExtra} F))).hom.comp
        (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD wExtra}
          C).symm.toHomotopyEquiv.toFun)

private theorem originalSimplexValueRecipeComputed (F : C ⥤ D)
    (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    originalSimplexValueRecipe.{uC, vC, uD, vD, wExtra} F
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SSet.toTopSimplex.{max uC vC}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (σ ⋙ F))
        ((SSet.toTopSimplex.{max uD vD}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) := by
  let LC := ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} C)
  let LD := ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} D)
  let UC : C ⥤ LC :=
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
      max uC vC uD vD wExtra, vC, uC} C).functor
  let UD : D ⥤ LD :=
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
      max uC vC uD vD wExtra, vD, uD} D).functor
  let L : LC ⥤ LD := originalSimplexValueLiftFunctor.{uC, vC, uD, vD, wExtra} F
  let σC : (nerve LC).obj (op n) := σ ⋙ UC
  let σD : (nerve LD).obj (op n) := (σ ⋙ F) ⋙ UD
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD wExtra} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD wExtra} D
  let y : SimplexCategory.toTop.{max uC vC uD vD wExtra}.obj n := ULift.up t
  let zC := SSet.toTop.map (SSet.yonedaEquiv.symm σC)
    ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)
  let zD := SSet.toTop.map (SSet.yonedaEquiv.symm σD)
    ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)
  let x := SSet.toTop.map (SSet.yonedaEquiv.symm σ)
    ((SSet.toTopSimplex.{max uC vC}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))
  have hC : HC zC = x :=
    SSet.realizedNerveLiftHomeomorph_simplexValue.{uC, vC, max uC vC uD vD wExtra} C n σ t
  have hCInverse : HC.symm x = zC :=
    (congrArg HC.symm hC).symm.trans (HC.symm_apply_apply zC)
  have hD : HD zD = SSet.toTop.map (SSet.yonedaEquiv.symm (σ ⋙ F))
      ((SSet.toTopSimplex.{max uD vD}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) :=
    SSet.realizedNerveLiftHomeomorph_simplexValue.{uD, vD, max uC vC uD vD wExtra}
      D n (σ ⋙ F) t
  have hChain : σC ⋙ L = σD := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change σD.map f = eqToHom (rfl : σD.obj i = σD.obj i) ≫ σD.map f ≫
        eqToHom (rfl : σD.obj j = σD.obj j)
      exact CategoryTheory.eq_conj_eqToHom (σD.map f))
  have hNerve : (nerveMap L).app (op n) σC = σD := hChain
  have hYoneda : SSet.yonedaEquiv.symm σC ≫ nerveMap L = SSet.yonedaEquiv.symm σD :=
    (SSet.yonedaEquiv_symm_comp σC (nerveMap L)).trans
      (congrArg (fun q : (nerve LD).obj (op n) => SSet.yonedaEquiv.symm q) hNerve)
  have hPoint : SSet.toTop.map (nerveMap L) zC = zD :=
    (TopCat.comp_app (SSet.toTop.map (SSet.yonedaEquiv.symm σC))
      (SSet.toTop.map (nerveMap L))
      ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)).symm.trans
      ((ConcreteCategory.congr_hom
        (SSet.toTop.map_comp (SSet.yonedaEquiv.symm σC) (nerveMap L)).symm
        ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)).trans
        (congrArg (fun f : SSet.stdSimplex.{max uC vC uD vD wExtra}.obj n ⟶ nerve LD =>
          SSet.toTop.map f ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)) hYoneda))
  change HD (SSet.toTop.map (nerveMap L) (HC.symm x)) = _
  exact (congrArg (fun z => HD (SSet.toTop.map (nerveMap L) z)) hCInverse).trans
    ((congrArg HD hPoint).trans hD)

private theorem originalRealizedFunctorSimplexValueComputed
    (F : C ⥤ D) (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizedNerveFunctorMap F
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SSet.toTopSimplex.{max uC vC}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (σ ⋙ F))
        ((SSet.toTopSimplex.{max uD vD}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) := by
  have hRecipe : realizedNerveFunctorMap F =
      originalSimplexValueRecipe.{uC, vC, uD, vD, 0} F :=
    realizedNerveFunctorMap_larger_recipe.{uC, vC, uD, vD, 0} F
  let x := SSet.toTop.map (SSet.yonedaEquiv.symm σ)
    ((SSet.toTopSimplex.{max uC vC}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))
  exact (congrArg (fun k : C(SSet.toTop.obj (nerve C), SSet.toTop.obj (nerve D)) => k x)
    hRecipe).trans (originalSimplexValueRecipeComputed.{uC, vC, uD, vD, 0} F n σ t)

/-- EVERY original simplex and EVERY original barycentric point maps to the
simplex of the actual original functor image. All four original category roles
are independent; no simplex/map/naturality comparison is supplied by the caller. -/
theorem realizedNerveFunctorMap_simplexValue
    (F : C ⥤ D) (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizedNerveFunctorMap F
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SSet.toTopSimplex.{max uC vC}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (σ ⋙ F))
        ((SSet.toTopSimplex.{max uD vD}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) :=
  originalRealizedFunctorSimplexValueComputed F n σ t

end CategoryTheory

end
