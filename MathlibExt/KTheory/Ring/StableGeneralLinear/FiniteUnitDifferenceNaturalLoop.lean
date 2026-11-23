/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitNaturalIso
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitStabilizationDifferences
public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactiveNaturalLoop

/-!
# The actual whole consecutive unit difference

The NEXT computed conjugator acts on the ORIGINAL finite stage because
stabilization preserves its original stable representative. Its whole
natural comparison therefore has the same source and target as the old
comparison. Their actual difference equals the whole computed inactive
natural loop, at every object and hence as an entire natural transformation.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private def finiteNextLeftUnitIsoRecipe (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R := by
  let w : StableGL R := (leftBlockElementaryConjugator R (n + 1) : StableGL R)
  refine NatIso.ofComponents (fun _ =>
    { hom := MulOpposite.op w⁻¹
      inv := MulOpposite.op w
      hom_inv_id := by
        apply MulOpposite.unop_injective
        change w⁻¹ * w = 1
        exact inv_mul_cancel w
      inv_hom_id := by
        apply MulOpposite.unop_injective
        change w * w⁻¹ = 1
        exact mul_inv_cancel w }) ?_
  intro x y g
  rw [Functor.comp_map, blockSumLeftClassifyingFunctor_map]
  apply MulOpposite.unop_injective
  change StableGL.of (MulOpposite.unop g) * w⁻¹ =
    w⁻¹ * blockSumLeftHom R (StableGL.of (MulOpposite.unop g))
  have hNext : w * StableGL.of
      (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g)) * w⁻¹ =
        blockSumLeftHom R (StableGL.of
          (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))) :=
    leftBlockElementaryConjugator_conjugates R (n + 1)
      (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))
  have h : w * StableGL.of (MulOpposite.unop g) * w⁻¹ =
      blockSumLeftHom R (StableGL.of (MulOpposite.unop g)) := by
    simpa only [StableGL.of_stabilization] using hNext
  have hc := congrArg (fun z : StableGL R => w⁻¹ * z) h
  have hCancel : w⁻¹ * (w * StableGL.of (MulOpposite.unop g) * w⁻¹) =
      StableGL.of (MulOpposite.unop g) * w⁻¹ := by
    rw [mul_assoc, inv_mul_cancel_left]
  exact hCancel.symm.trans hc

private theorem finiteNextLeftUnitIsoRecipe_inv_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextLeftUnitIsoRecipe R n).inv.app x =
      MulOpposite.op (leftBlockElementaryConjugator R (n + 1) : StableGL R) := by
  unfold finiteNextLeftUnitIsoRecipe
  rw [← Iso.app_inv, NatIso.ofComponents.app]

private theorem finiteNextLeftUnitIsoRecipe_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextLeftUnitIsoRecipe R n).hom.app x =
      MulOpposite.op (leftBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ := by
  unfold finiteNextLeftUnitIsoRecipe
  rw [← Iso.app_hom, NatIso.ofComponents.app]

/-- The actual next conjugator provides its comparison on the original
stage, through the proved original stabilization equation. -/
public def finiteNextLeftBlockUnitIso (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R :=
  finiteNextLeftUnitIsoRecipe R n

/-- Its inverse component is the SAME next computed elementary matrix. -/
public theorem finiteNextLeftBlockUnitIso_inv_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextLeftBlockUnitIso R n).inv.app x =
      MulOpposite.op (leftBlockElementaryConjugator R (n + 1) : StableGL R) :=
  finiteNextLeftUnitIsoRecipe_inv_app R n x

/-- The forward component retains the normalized opposite inverse of
the SAME next computed elementary matrix. -/
public theorem finiteNextLeftBlockUnitIso_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextLeftBlockUnitIso R n).hom.app x =
      MulOpposite.op (leftBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ :=
  finiteNextLeftUnitIsoRecipe_hom_app R n x

/-- The original transition followed by the original next inclusion is
the original current inclusion, as an ENTIRE classifying functor. -/
public theorem finiteToStableSuccessorFunctor_eq (n : ℕ) :
    ((finiteClassifyingCategoryDiagram R).map (homOfLE (Nat.le_add_right n 1))).toFunctor ⋙
        (finiteToStableCategoryMap R (n + 1)).toFunctor =
      (finiteToStableCategoryMap R n).toFunctor :=
  congrArg (fun f : (finiteClassifyingCategoryDiagram R).obj n ⟶
    Cat.of (ClassifyingCategory R) => f.toFunctor)
      (finiteToStableCategoryMap_naturality R (homOfLE (Nat.le_add_right n 1)))

/-- The literal restriction of the next original unit comparison,
transported only along the PROVED original inclusion triangle. -/
public def finiteRestrictedNextLeftBlockUnitHom (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ⟶
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R :=
  eqToHom (finiteToStableSuccessorFunctor_eq R n).symm ≫
    Functor.whiskerLeft
      ((finiteClassifyingCategoryDiagram R).map (homOfLE (Nat.le_add_right n 1))).toFunctor
      (finiteLeftBlockUnitIso R (n + 1)).hom ≫
        eqToHom (congrArg (fun F : (finiteClassifyingCategoryDiagram R).obj n ⥤
          ClassifyingCategory R => F ⋙ blockSumLeftClassifyingFunctor R)
            (finiteToStableSuccessorFunctor_eq R n))

private theorem finiteUnitBundledClassifyingTransport
    {a b c d : Cat.of (ClassifyingCategory R)}
    (hab : a = b) (hcd : c = d) (g : (StableGL R)ᵐᵒᵖ) :
    (eqToHom hab : a ⟶ b) ≫ (show b ⟶ c from g) ≫ (eqToHom hcd : c ⟶ d) =
      (show a ⟶ d from g) := by
  cases hab
  cases hcd
  simp only [eqToHom_refl, Category.id_comp]
  exact @Category.comp_id (Cat.of (ClassifyingCategory R))
    (Cat.str (Cat.of (ClassifyingCategory R))) a c (show a ⟶ c from g)

/-- The WHOLE restriction is the previously computed next comparison,
not merely an equality at the selected classifying-space point. -/
public theorem finiteRestrictedNextLeftBlockUnitHom_eq (n : ℕ) :
    finiteRestrictedNextLeftBlockUnitHom R n = (finiteNextLeftBlockUnitIso R n).hom := by
  apply NatTrans.ext
  funext c
  simp only [finiteRestrictedNextLeftBlockUnitHom, NatTrans.comp_app, eqToHom_app,
    Functor.whiskerLeft_app, finiteLeftBlockUnitIso_hom_app, finiteNextLeftBlockUnitIso_hom_app]
  exact finiteUnitBundledClassifyingTransport R _ _
    (MulOpposite.op (leftBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹)

/-- The ENTIRE next comparison prism on the old stage is the original
next-stage prism precomposed by the actual successor nerve map. -/
public theorem finiteNextLeftBlockUnitIso_nerveHomotopyMap_restriction (n : ℕ) :
    NatTrans.nerveHomotopyMap (finiteNextLeftBlockUnitIso R n).hom =
      (nerveMap
        (((finiteClassifyingCategoryDiagram R).map
          (homOfLE (Nat.le_add_right n 1))).toFunctor) ▷ (Δ[1] : SSet.{u})) ≫
            NatTrans.nerveHomotopyMap (finiteLeftBlockUnitIso R (n + 1)).hom := by
  let I := ((finiteClassifyingCategoryDiagram R).map
    (homOfLE (Nat.le_add_right n 1))).toFunctor
  let α := (finiteLeftBlockUnitIso R (n + 1)).hom
  have ht := NatTrans.nerveHomotopyMap_eqToHomEndpoints
    (finiteToStableSuccessorFunctor_eq R n)
    (congrArg (fun F : (finiteClassifyingCategoryDiagram R).obj n ⥤
      ClassifyingCategory R => F ⋙ blockSumLeftClassifyingFunctor R)
        (finiteToStableSuccessorFunctor_eq R n))
    (Functor.whiskerLeft I α)
  calc
    NatTrans.nerveHomotopyMap (finiteNextLeftBlockUnitIso R n).hom =
        NatTrans.nerveHomotopyMap (finiteRestrictedNextLeftBlockUnitHom R n) :=
      congrArg NatTrans.nerveHomotopyMap (finiteRestrictedNextLeftBlockUnitHom_eq R n).symm
    _ = NatTrans.nerveHomotopyMap (Functor.whiskerLeft I α) := ht
    _ = (nerveMap I ▷ (Δ[1] : SSet.{u})) ≫ NatTrans.nerveHomotopyMap α :=
      (NatTrans.nerveHomotopyMap_precomp I α).symm

/-- The difference of the two actual whole original finite comparisons. -/
public abbrev finiteLeftUnitDifferenceLoop (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ⟶ (finiteToStableCategoryMap R n).toFunctor :=
  (finiteLeftBlockUnitIso R n).hom ≫ (finiteNextLeftBlockUnitIso R n).inv

/-- This WHOLE natural-transformation difference is the computed perfect
inactive loop, not merely equality of its selected vertex trace. -/
public theorem finiteLeftUnitDifferenceLoop_eq_inactive (n : ℕ) :
    finiteLeftUnitDifferenceLoop R n =
      finiteInactiveClassifyingLoop R (leftUnitCommonRank_bound.{u} n)
        (leftUnitDifferencePerfectFactor R n) := by
  apply NatTrans.ext
  funext c
  rw [NatTrans.comp_app, finiteLeftBlockUnitIso_hom_app,
    finiteNextLeftBlockUnitIso_inv_app, finiteInactiveClassifyingLoop_app,
    leftUnitDifferencePerfectFactor_reconstruct]
  rw [classifyingCategory_comp_as_mul]
  apply MulOpposite.unop_injective
  change (leftBlockElementaryConjugator R n : StableGL R)⁻¹ *
      (leftBlockElementaryConjugator R (n + 1) : StableGL R) =
    ((leftBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ *
      (leftBlockElementaryConjugator R n : StableGL R))⁻¹
  rw [mul_inv_rev, inv_inv]

/-- Their ENTIRE nerve-cylinder difference is the original complete
inactive family cylinder with its computed perfect factor. -/
public theorem finiteLeftUnitDifferenceLoop_nerveHomotopyMap (n : ℕ) :
    NatTrans.nerveHomotopyMap (finiteLeftUnitDifferenceLoop R n) =
      NatTrans.nerveHomotopyMap
        (initialInactiveClassifyingLoop R (leftUnitCommonRank_bound.{u} n)
          (leftUnitDifferencePerfectFactor R n)) := by
  rw [finiteLeftUnitDifferenceLoop_eq_inactive, finiteInactiveClassifyingLoop_nerveHomotopyMap]

end AlgebraicKTheory.StableGL

end
