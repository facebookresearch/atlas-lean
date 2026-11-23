/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockSumClassifying
public import MathlibExt.KTheory.Ring.StableGeneralLinear.InterleavedUnitConjugators
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpace
public import MathlibExt.CategoryTheory.NerveHomotopyRealization
public import MathlibExt.CategoryTheory.NerveIhomComposition

/-!
# Whole finite classifying-category unit comparisons

The computed elementary unit conjugator gives a natural isomorphism on
the ENTIRE original finite general-linear classifying category. Its
component is the normalized opposite inverse of that same elementary
matrix. This is categorical data for a whole finite-stage homotopy;
no arbitrary homotopy, nullity, or compatibility witness is assumed.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private def finiteLeftUnitIsoRecipe (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R := by
  let w : StableGL R := (leftBlockElementaryConjugator R n : StableGL R)
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
  have h : w * StableGL.of (MulOpposite.unop g) * w⁻¹ =
      blockSumLeftHom R (StableGL.of (MulOpposite.unop g)) :=
    leftBlockElementaryConjugator_conjugates R n (MulOpposite.unop g)
  have hc := congrArg (fun z : StableGL R => w⁻¹ * z) h
  have hCancel : w⁻¹ * (w * StableGL.of (MulOpposite.unop g) * w⁻¹) =
      StableGL.of (MulOpposite.unop g) * w⁻¹ := by
    rw [mul_assoc, inv_mul_cancel_left]
  exact hCancel.symm.trans hc

private theorem finiteLeftUnitIsoRecipe_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteLeftUnitIsoRecipe R n).hom.app x =
      MulOpposite.op (leftBlockElementaryConjugator R n : StableGL R)⁻¹ := by
  unfold finiteLeftUnitIsoRecipe
  rw [← Iso.app_hom, NatIso.ofComponents.app]

/-- The full original finite-stage inclusion is naturally isomorphic to
its actual first block-sum embedding. -/
public def finiteLeftBlockUnitIso (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R :=
  finiteLeftUnitIsoRecipe R n

/-- The component is the original normalized loop coefficient of the
computed elementary matrix, with the opposite/inverse order retained. -/
public theorem finiteLeftBlockUnitIso_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteLeftBlockUnitIso R n).hom.app x =
      MulOpposite.op (leftBlockElementaryConjugator R n : StableGL R)⁻¹ :=
  finiteLeftUnitIsoRecipe_hom_app R n x

private theorem finiteLeftZeroFunctor_eq :
    (finiteToStableCategoryMap R 0).toFunctor =
      (finiteToStableCategoryMap R 0).toFunctor ⋙ blockSumLeftClassifyingFunctor R := by
  letI : Subsingleton (Cat.of (ClassifyingCategory R)) := by
    change Subsingleton ((Cat.of (ClassifyingCategory R)).α)
    rw [Cat.of_α]
    exact inferInstanceAs (Subsingleton (SingleObj ((StableGL R)ᵐᵒᵖ)))
  refine Functor.hext (fun _ => Subsingleton.elim _ _) ?_
  intro x y f
  have hf : (MulOpposite.unop f : Matrix.GeneralLinearGroup (Fin 0) R) = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact Fin.elim0 i
  apply heq_of_eq
  rw [Functor.comp_map, blockSumLeftClassifyingFunctor_map]
  change MulOpposite.op (StableGL.of (MulOpposite.unop f)) =
    MulOpposite.op (blockSumLeftHom R (StableGL.of (MulOpposite.unop f)))
  rw [hf, StableGL.of_one, (blockSumLeftHom R).map_one]

private theorem finiteLeftZeroUnitHom_eq :
    (finiteLeftBlockUnitIso R 0).hom = eqToHom (finiteLeftZeroFunctor_eq R) := by
  apply NatTrans.ext
  funext c
  rw [finiteLeftBlockUnitIso_hom_app, leftBlockElementaryConjugator_zero,
    inv_one, eqToHom_app, classifyingCategory_eqToHom]
  rfl

/-- The original zero-stage unit cylinder is the literal constant
prism on the original finite inclusion, not only a null loop class. -/
public theorem finiteLeftUnitZeroCylinder_eq :
    NatTrans.nerveHomotopyMap (finiteLeftBlockUnitIso R 0).hom =
      CartesianMonoidalCategory.fst (nerve ((finiteClassifyingCategoryDiagram R).obj 0))
          (Δ[1] : SSet.{u}) ≫ nerveMap (finiteToStableCategoryMap R 0).toFunctor := by
  have ht := NatTrans.nerveHomotopyMap_eqToHomEndpoints
    (rfl : (finiteToStableCategoryMap R 0).toFunctor = (finiteToStableCategoryMap R 0).toFunctor)
    (finiteLeftZeroFunctor_eq R) (𝟙 (finiteToStableCategoryMap R 0).toFunctor)
  have ht' : NatTrans.nerveHomotopyMap (eqToHom (finiteLeftZeroFunctor_eq R)) =
      NatTrans.nerveHomotopyMap (𝟙 (finiteToStableCategoryMap R 0).toFunctor) := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ht
  rw [finiteLeftZeroUnitHom_eq, ht',
    ← NatTrans.nervePrismMap_nerveCylinderFunctor, NatTrans.nerveCylinderFunctor_id,
    Functor.nervePrismMap_fst_comp]

/-- The whole finite-stage natural isomorphism gives an actual simplicial
homotopy between the original nerve maps. -/
public def finiteLeftBlockUnitSimplicialHomotopy (n : ℕ) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (finiteToStableCategoryMap R n).toFunctor)
      (CategoryTheory.nerveMap
        ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R)) :=
  NatTrans.nerveHomotopy (finiteLeftUnitIsoRecipe R n).hom

/-- Realization gives a genuine whole finite-stage homotopy between the
original inclusion and original first block map. Its unit trace has not
been discarded or assumed constant; based retuning and compatible stage
descent are the subsequent proof steps. -/
public def finiteLeftBlockUnitHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (SSet.toTop.map
        (CategoryTheory.nerveMap (finiteToStableCategoryMap R n).toFunctor)).hom
      (SSet.toTop.map
        (CategoryTheory.nerveMap
          ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumLeftClassifyingFunctor R))).hom :=
  SSet.realizeHomotopy _ _ _ _ (finiteLeftBlockUnitSimplicialHomotopy R n)

private def finiteRightUnitIsoRecipe (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R := by
  let w : StableGL R := (rightBlockElementaryConjugator R n : StableGL R)
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
  rw [Functor.comp_map, blockSumRightClassifyingFunctor_map]
  apply MulOpposite.unop_injective
  change StableGL.of (MulOpposite.unop g) * w⁻¹ =
    w⁻¹ * blockSumRightHom R (StableGL.of (MulOpposite.unop g))
  have h : w * StableGL.of (MulOpposite.unop g) * w⁻¹ =
      blockSumRightHom R (StableGL.of (MulOpposite.unop g)) :=
    rightBlockElementaryConjugator_conjugates R n (MulOpposite.unop g)
  have hc := congrArg (fun z : StableGL R => w⁻¹ * z) h
  have hCancel : w⁻¹ * (w * StableGL.of (MulOpposite.unop g) * w⁻¹) =
      StableGL.of (MulOpposite.unop g) * w⁻¹ := by
    rw [mul_assoc, inv_mul_cancel_left]
  exact hCancel.symm.trans hc

private theorem finiteRightUnitIsoRecipe_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteRightUnitIsoRecipe R n).hom.app x =
      MulOpposite.op (rightBlockElementaryConjugator R n : StableGL R)⁻¹ := by
  unfold finiteRightUnitIsoRecipe
  rw [← Iso.app_hom, NatIso.ofComponents.app]

/-- The full original finite-stage inclusion is naturally isomorphic to
its actual second block-sum embedding. -/
public def finiteRightBlockUnitIso (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R :=
  finiteRightUnitIsoRecipe R n

/-- The second comparison retains the normalized elementary component. -/
public theorem finiteRightBlockUnitIso_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteRightBlockUnitIso R n).hom.app x =
      MulOpposite.op (rightBlockElementaryConjugator R n : StableGL R)⁻¹ :=
  finiteRightUnitIsoRecipe_hom_app R n x

private theorem finiteRightZeroFunctor_eq :
    (finiteToStableCategoryMap R 0).toFunctor =
      (finiteToStableCategoryMap R 0).toFunctor ⋙ blockSumRightClassifyingFunctor R := by
  letI : Subsingleton (Cat.of (ClassifyingCategory R)) := by
    change Subsingleton ((Cat.of (ClassifyingCategory R)).α)
    rw [Cat.of_α]
    exact inferInstanceAs (Subsingleton (SingleObj ((StableGL R)ᵐᵒᵖ)))
  refine Functor.hext (fun _ => Subsingleton.elim _ _) ?_
  intro x y f
  have hf : (MulOpposite.unop f : Matrix.GeneralLinearGroup (Fin 0) R) = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact Fin.elim0 i
  apply heq_of_eq
  rw [Functor.comp_map, blockSumRightClassifyingFunctor_map]
  change MulOpposite.op (StableGL.of (MulOpposite.unop f)) =
    MulOpposite.op (blockSumRightHom R (StableGL.of (MulOpposite.unop f)))
  rw [hf, StableGL.of_one, (blockSumRightHom R).map_one]

private theorem finiteRightZeroUnitHom_eq :
    (finiteRightBlockUnitIso R 0).hom = eqToHom (finiteRightZeroFunctor_eq R) := by
  apply NatTrans.ext
  funext c
  rw [finiteRightBlockUnitIso_hom_app, rightBlockElementaryConjugator_zero,
    inv_one, eqToHom_app, classifyingCategory_eqToHom]
  rfl

/-- The ORIGINAL zero-stage right-unit cylinder is the literal constant
whole prism, with no marked-point loop discarded. -/
public theorem finiteRightUnitZeroCylinder_eq :
    NatTrans.nerveHomotopyMap (finiteRightBlockUnitIso R 0).hom =
      CartesianMonoidalCategory.fst (nerve ((finiteClassifyingCategoryDiagram R).obj 0))
          (Δ[1] : SSet.{u}) ≫ nerveMap (finiteToStableCategoryMap R 0).toFunctor := by
  have ht := NatTrans.nerveHomotopyMap_eqToHomEndpoints
    (rfl : (finiteToStableCategoryMap R 0).toFunctor = (finiteToStableCategoryMap R 0).toFunctor)
    (finiteRightZeroFunctor_eq R) (𝟙 (finiteToStableCategoryMap R 0).toFunctor)
  have ht' : NatTrans.nerveHomotopyMap (eqToHom (finiteRightZeroFunctor_eq R)) =
      NatTrans.nerveHomotopyMap (𝟙 (finiteToStableCategoryMap R 0).toFunctor) := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ht
  rw [finiteRightZeroUnitHom_eq, ht',
    ← NatTrans.nervePrismMap_nerveCylinderFunctor, NatTrans.nerveCylinderFunctor_id,
    Functor.nervePrismMap_fst_comp]

/-- The original second block comparison is a whole simplicial homotopy. -/
public def finiteRightBlockUnitSimplicialHomotopy (n : ℕ) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (finiteToStableCategoryMap R n).toFunctor)
      (CategoryTheory.nerveMap
        ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R)) :=
  NatTrans.nerveHomotopy (finiteRightUnitIsoRecipe R n).hom

/-- Its realization is an actual whole finite-stage homotopy. Both unit
traces and the later stage-compatibility obligations are retained. -/
public def finiteRightBlockUnitHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (SSet.toTop.map
        (CategoryTheory.nerveMap (finiteToStableCategoryMap R n).toFunctor)).hom
      (SSet.toTop.map
        (CategoryTheory.nerveMap
          ((finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R))).hom :=
  SSet.realizeHomotopy _ _ _ _ (finiteRightBlockUnitSimplicialHomotopy R n)

end AlgebraicKTheory.StableGL

end
