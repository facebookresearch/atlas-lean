/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionFunctorObject
import MathlibExt.AlgebraicTopology.SimplicialSpace.TrueSpacePowerConsumer

/-!
# The literal first-JT Cartesian closed comparison

The first-projection source counit and the whole first-projection power Iso
give a specified map from the right image of the CSS functor object to the
native scalar functor object. Its evaluation mate is the original right
product comparison followed by the original evaluation. Thus it is exactly
the existing Cartesian exponential comparison, on the same maps.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialSpace.FirstProjection

private local instance leftBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) left.{u} := by
  dsimp [left, comparisonLeft, SSet.simplicialSpaceDiscrete]
  infer_instance

private local instance rightBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) right.{u} := by
  let h : PreservesLimitsOfSize.{0, 0} right.{u} := adjunction.rightAdjoint_preservesLimits
  exact h.preservesLimitsOfShape

/-- The actual right product Iso retains its original two projections. -/
def rightProductIso (W V : SimplicialSpace.{u}) :
    right.obj (W ⊗ V) ≅ right.obj W ⊗ right.obj V :=
  CartesianMonoidalCategory.prodComparisonIso right W V

/-- Its forward leg is the original Cartesian right product comparison. -/
theorem rightProductIso_hom (W V : SimplicialSpace.{u}) :
    (rightProductIso W V).hom = CartesianMonoidalCategory.prodComparison right W V := rfl

/-- The specified first-projection counit, including the original wrapping equivalence. -/
def counit (W : SimplicialSpace.{u}) : left.obj (right.obj W) ⟶ W :=
  adjunction.counit.app W

/-- The counit uses the original first-JT counit and its literal scalar-carrier identification. -/
theorem counit_eq (W : SimplicialSpace.{u}) :
    counit W = comparisonLeft.map
        (JoyalSSet.equivalenceSSet.unitIso.app (comparisonRight.obj W)).inv ≫
      comparisonAdjunction.counit.app W := by
  exact (JoyalSSet.equivalenceSSet.symm.toAdjunction).comp_counit_app comparisonAdjunction W

private theorem counitAdjunct (W : SimplicialSpace.{u}) :
    adjunction.homEquiv (right.obj W) W (counit W) = 𝟙 (right.obj W) := by
  change adjunction.homEquiv (right.obj W) W (adjunction.counit.app W) = 𝟙 (right.obj W)
  simpa only [Adjunction.homEquiv_symm_id] using
    (adjunction.homEquiv (right.obj W) W).apply_symm_apply (𝟙 (right.obj W))

private theorem productCounitTranspose (W V : SimplicialSpace.{u}) :
    adjunction.homEquiv (right.obj W ⊗ right.obj V) (W ⊗ V)
        (CartesianMonoidalCategory.prodComparison left (right.obj W) (right.obj V) ≫
          (counit W ⊗ₘ counit V)) = (rightProductIso W V).inv := by
  apply (cancel_mono (rightProductIso W V).hom).mp
  rw [Iso.inv_hom_id]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, rightProductIso_hom, CartesianMonoidalCategory.prodComparison_fst,
      ← adjunction.homEquiv_naturality_right]
    simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst]
    rw [← Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
      adjunction.homEquiv_naturality_left, counitAdjunct, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, rightProductIso_hom, CartesianMonoidalCategory.prodComparison_snd,
      ← adjunction.homEquiv_naturality_right]
    simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd]
    rw [← Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
      adjunction.homEquiv_naturality_left, counitAdjunct, Category.comp_id, Category.id_comp]

private theorem functorIsoTranspose (Q P : SSet.{u}) (V : SimplicialSpace.{u})
    (g : left.obj P ⟶ (ihom (left.obj Q)).obj V) :
    adjunction.homEquiv P ((ihom (left.obj Q)).obj V) g ≫ (functorObjectIso Q).hom.app V =
      MonoidalClosed.curry (adjunction.homEquiv (Q ⊗ P) V
        (CartesianMonoidalCategory.prodComparison left Q P ≫ MonoidalClosed.uncurry g)) := by
  have h := functorObjectIso_transpose Q P V
    ((β_ (left.obj P) (left.obj Q)).hom ≫ MonoidalClosed.uncurry g)
  have hb : (β_ (left.obj Q) (left.obj P)).hom ≫
      ((β_ (left.obj P) (left.obj Q)).hom ≫ MonoidalClosed.uncurry g) =
        MonoidalClosed.uncurry g := by
    rw [← Category.assoc]
    simp
  change (adjunction.comp (ihom.adjunction (left.obj Q))).homEquiv P V _ ≫
      (functorObjectIso Q).hom.app V =
    (((ihom.adjunction Q).comp adjunction).ofNatIsoLeft
      (CartesianMonoidalCategory.prodComparisonNatIso left Q)).homEquiv P V _ at h
  rw [hb, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv, Equiv.trans_apply] at h
  change adjunction.homEquiv P ((ihom (left.obj Q)).obj V)
      (MonoidalClosed.curry (MonoidalClosed.uncurry g)) ≫ (functorObjectIso Q).hom.app V =
    MonoidalClosed.curry (adjunction.homEquiv (Q ⊗ P) V
      (CartesianMonoidalCategory.prodComparison left Q P ≫ MonoidalClosed.uncurry g)) at h
  rw [MonoidalClosed.curry_uncurry] at h
  exact h

/-- The canonical comparison first restricts along the actual source counit. -/
def comparison (W V : SimplicialSpace.{u}) :
    right.obj ((ihom W).obj V) ⟶ (ihom (right.obj W)).obj (right.obj V) :=
  right.map ((MonoidalClosed.pre (counit W)).app V) ≫
    (functorObjectIso (right.obj W)).hom.app V

private def powerCounitMap (W V : SimplicialSpace.{u}) :
    left.obj (right.obj ((ihom W).obj V)) ⟶ (ihom (left.obj (right.obj W))).obj V :=
  counit ((ihom W).obj V) ≫ (MonoidalClosed.pre (counit W)).app V

private theorem powerCounitMapAdjunct (W V : SimplicialSpace.{u}) :
    adjunction.homEquiv (right.obj ((ihom W).obj V))
        ((ihom (left.obj (right.obj W))).obj V) (powerCounitMap W V) =
      right.map ((MonoidalClosed.pre (counit W)).app V) := by
  unfold powerCounitMap
  rw [adjunction.homEquiv_naturality_right, counitAdjunct, Category.id_comp]

private theorem powerCounitMapUncurry (W V : SimplicialSpace.{u}) :
    MonoidalClosed.uncurry (powerCounitMap W V) =
      (counit W ⊗ₘ counit ((ihom W).obj V)) ≫ (ihom.ev W).app V := by
  unfold powerCounitMap
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
    MonoidalClosed.id_tensor_pre_app_comp_ev, ← Category.assoc, ← tensorHom_def']

/-- The comparison is the full native scalar transpose of the original right evaluation mate. -/
theorem comparison_transpose (W V : SimplicialSpace.{u}) :
    comparison W V = MonoidalClosed.curry
      ((rightProductIso W ((ihom W).obj V)).inv ≫ right.map ((ihom.ev W).app V)) := by
  have h := functorIsoTranspose (right.obj W) (right.obj ((ihom W).obj V)) V (powerCounitMap W V)
  rw [powerCounitMapAdjunct, powerCounitMapUncurry, ← Category.assoc,
    adjunction.homEquiv_naturality_right, productCounitTranspose] at h
  exact h

/-- The literal evaluation mate retains the original product Iso and original CSS evaluation. -/
theorem comparison_evaluation (W V : SimplicialSpace.{u}) :
    MonoidalClosed.uncurry (comparison W V) =
      (rightProductIso W ((ihom W).obj V)).inv ≫ right.map ((ihom.ev W).app V) := by
  rw [comparison_transpose, MonoidalClosed.uncurry_curry]

/-- This is exactly the existing Cartesian exponential comparison on the actual first-JT right functor. -/
theorem comparison_eq_expComparison (W V : SimplicialSpace.{u}) :
    comparison W V = (CategoryTheory.expComparison right W).app V := by
  let _ : IsIso (CartesianMonoidalCategory.prodComparison right W ((ihom W).obj V)) := by
    rw [← rightProductIso_hom]
    infer_instance
  apply ((ihom.adjunction (right.obj W)).homEquiv
    (right.obj ((ihom W).obj V)) (right.obj V)).symm.injective
  change MonoidalClosed.uncurry (comparison W V) =
    MonoidalClosed.uncurry ((CategoryTheory.expComparison right W).app V)
  rw [comparison_evaluation, CategoryTheory.uncurry_expComparison]
  have hi : inv (CartesianMonoidalCategory.prodComparison right W ((ihom W).obj V)) =
      (rightProductIso W ((ihom W).obj V)).inv :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← rightProductIso_hom]; exact Iso.hom_inv_id _)
  rw [hi]

/-- Every supplied first-left source map retains its actual adjunct under the entire power Iso. -/
theorem comparison_restriction (Q : SSet.{u}) (W V : SimplicialSpace.{u}) (f : left.obj Q ⟶ W) :
    right.map ((MonoidalClosed.pre f).app V) ≫ (functorObjectIso Q).hom.app V =
      comparison W V ≫ (MonoidalClosed.pre (adjunction.homEquiv Q W f)).app (right.obj V) := by
  let P := right.obj ((ihom W).obj V)
  let a := adjunction.homEquiv Q W f
  have hf : f = left.map a ≫ counit W := ((adjunction.homEquiv Q W).symm_apply_apply f).symm
  have ht : (f ⊗ₘ counit ((ihom W).obj V)) =
      left.map a ▷ left.obj P ≫ (counit W ⊗ₘ counit ((ihom W).obj V)) := by
    rw [hf]
    simp only [tensorHom_def, comp_whiskerRight, Category.assoc]
    rfl
  have hp : CartesianMonoidalCategory.prodComparison left Q P ≫
      ((f ⊗ₘ counit ((ihom W).obj V)) ≫ (ihom.ev W).app V) =
    left.map (a ▷ P) ≫ (CartesianMonoidalCategory.prodComparison left (right.obj W) P ≫
      (counit W ⊗ₘ counit ((ihom W).obj V)) ≫ (ihom.ev W).app V) := by
    rw [ht]
    simp only [Category.assoc]
    rw [← CartesianMonoidalCategory.prodComparison_natural_whiskerRight_assoc]
  let g : left.obj P ⟶ (ihom (left.obj Q)).obj V :=
    counit ((ihom W).obj V) ≫ (MonoidalClosed.pre f).app V
  have hg : adjunction.homEquiv P ((ihom (left.obj Q)).obj V) g =
      right.map ((MonoidalClosed.pre f).app V) := by
    change adjunction.homEquiv P _ (counit ((ihom W).obj V) ≫ _) = _
    rw [adjunction.homEquiv_naturality_right, counitAdjunct, Category.id_comp]
  have hu : MonoidalClosed.uncurry g =
      (f ⊗ₘ counit ((ihom W).obj V)) ≫ (ihom.ev W).app V := by
    change MonoidalClosed.uncurry (counit ((ihom W).obj V) ≫ (MonoidalClosed.pre f).app V) = _
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
      MonoidalClosed.id_tensor_pre_app_comp_ev, ← Category.assoc, ← tensorHom_def']
  have h := functorIsoTranspose Q P V g
  have he : adjunction.homEquiv (right.obj W ⊗ P) V
      (CartesianMonoidalCategory.prodComparison left (right.obj W) P ≫
        (counit W ⊗ₘ counit ((ihom W).obj V)) ≫ (ihom.ev W).app V) =
      (rightProductIso W ((ihom W).obj V)).inv ≫ right.map ((ihom.ev W).app V) := by
    rw [← Category.assoc]
    change adjunction.homEquiv (right.obj W ⊗ right.obj ((ihom W).obj V)) V
      ((CartesianMonoidalCategory.prodComparison left (right.obj W) (right.obj ((ihom W).obj V)) ≫
        (counit W ⊗ₘ counit ((ihom W).obj V))) ≫ (ihom.ev W).app V) = _
    rw [adjunction.homEquiv_naturality_right, productCounitTranspose]
  rw [hg, hu, hp, adjunction.homEquiv_naturality_left, he] at h
  rw [comparison_transpose]
  exact h.trans (MonoidalClosed.curry_pre_app a
    ((rightProductIso W ((ihom W).obj V)).inv ≫ right.map ((ihom.ev W).app V))).symm

end SimplicialSpace.FirstProjection
