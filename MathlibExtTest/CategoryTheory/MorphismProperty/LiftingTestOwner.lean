/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.MorphismProperty.LiftingTest
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
universe w s u v

open CategoryTheory TypeCat MorphismProperty

namespace MathlibExtTest.TaggedLiftingTestOwner

variable {C : Type u} [Category.{v} C] {ι : Type s} (f : ι → Arrow C)

private theorem entire_raw_forward_function :
    (fun (p : Arrow C) (z : LiftingTest.RawLifts f p) =>
      ((LiftingTest.rawFunctor f).obj p).hom z) =
    (fun (p : Arrow C) (z : LiftingTest.RawLifts f p) =>
      (⟨z.1, Arrow.homMk ((f z.1).hom ≫ z.2) (z.2 ≫ p.hom)
        (Category.assoc _ _ _)⟩ : LiftingTest.RawSquares f p)) := rfl

private theorem entire_raw_source_map_function :
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawLifts f p) =>
      ((LiftingTest.rawFunctor f).map τ).left z) =
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawLifts f p) =>
      (⟨z.1, z.2 ≫ τ.left⟩ : LiftingTest.RawLifts f q)) := rfl

private theorem entire_raw_target_map_function :
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawSquares f p) =>
      ((LiftingTest.rawFunctor f).map τ).right z) =
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawSquares f p) =>
      (⟨z.1, z.2 ≫ τ⟩ : LiftingTest.RawSquares f q)) := rfl

private theorem original_diagonal_gives_original_square
    (p : Arrow C) (k : ι) (a : f k ⟶ p) (l : Arrow.LiftStruct a) :
    LiftingTest.liftToSquare f p ⟨k, l.l⟩ = ⟨k, a⟩ := by
  apply congrArg (fun b : f k ⟶ p => (⟨k, b⟩ : LiftingTest.RawSquares f p))
  apply Arrow.hom_ext
  · exact l.fac_left
  · exact l.fac_right

private def original_lift_of_preimage
    (p : Arrow C) (k : ι) (a : f k ⟶ p) (l : (f k).right ⟶ p.left)
    (h : LiftingTest.liftToSquare f p ⟨k, l⟩ = ⟨k, a⟩) :
    Arrow.LiftStruct a := by
  have ha := sigma_mk_injective h
  exact
    { l := l
      fac_left := congrArg (fun b : f k ⟶ p => b.left) ha
      fac_right := congrArg (fun b : f k ⟶ p => b.right) ha }

private theorem original_lift_of_preimage_value
    (p : Arrow C) (k : ι) (a : f k ⟶ p) (l : (f k).right ⟶ p.left)
    (h : LiftingTest.liftToSquare f p ⟨k, l⟩ = ⟨k, a⟩) :
    (original_lift_of_preimage f p k a l h).l = l := rfl

private theorem original_lift_of_preimage_left
    (p : Arrow C) (k : ι) (a : f k ⟶ p) (l : (f k).right ⟶ p.left)
    (h : LiftingTest.liftToSquare f p ⟨k, l⟩ = ⟨k, a⟩) :
    (f k).hom ≫ (original_lift_of_preimage f p k a l h).l = a.left :=
  (original_lift_of_preimage f p k a l h).fac_left

private theorem original_lift_of_preimage_right
    (p : Arrow C) (k : ι) (a : f k ⟶ p) (l : (f k).right ⟶ p.left)
    (h : LiftingTest.liftToSquare f p ⟨k, l⟩ = ⟨k, a⟩) :
    (original_lift_of_preimage f p k a l h).l ≫ p.hom = a.right :=
  (original_lift_of_preimage f p k a l h).fac_right

private theorem all_original_lifts_iff_surjectivity (p : Arrow C) :
    (∀ k : ι, ∀ a : f k ⟶ p, Nonempty (Arrow.LiftStruct a)) ↔
      Function.Surjective ((LiftingTest.rawFunctor f).obj p).hom := by
  rw [LiftingTest.rawFunctor_surjective_iff]
  apply forall_congr'
  intro k
  exact (Arrow.hasLiftingProperty_iff (f k).hom p.hom).symm

private theorem native_right_class_of_every_actual_generator (p : Arrow C) :
    (ofHoms (fun k => (f k).hom)).rlp p.hom ↔
      Function.Surjective ((LiftingTest.rawFunctor f).obj p).hom :=
  (LiftingTest.rawFunctor_surjective_iff_rlp f p).symm

private theorem raw_source_identity_function (p : Arrow C) :
    (fun z : LiftingTest.RawLifts f p =>
      ((LiftingTest.rawFunctor f).map (𝟙 p)).left z) = id := by
  funext z
  exact congrFun (LiftingTest.rawLiftMap_id f p) z

private theorem raw_target_identity_function (p : Arrow C) :
    (fun z : LiftingTest.RawSquares f p =>
      ((LiftingTest.rawFunctor f).map (𝟙 p)).right z) = id := by
  funext z
  exact congrFun (LiftingTest.rawSquareMap_id f p) z

private theorem raw_source_composition_function {p q r : Arrow C}
    (τ : p ⟶ q) (σ : q ⟶ r) :
    (fun z : LiftingTest.RawLifts f p =>
      ((LiftingTest.rawFunctor f).map (τ ≫ σ)).left z) =
    (fun z : LiftingTest.RawLifts f p =>
      ((LiftingTest.rawFunctor f).map σ).left
        (((LiftingTest.rawFunctor f).map τ).left z)) := by
  funext z
  exact congrFun (LiftingTest.rawLiftMap_comp f τ σ) z

private theorem raw_target_composition_function {p q r : Arrow C}
    (τ : p ⟶ q) (σ : q ⟶ r) :
    (fun z : LiftingTest.RawSquares f p =>
      ((LiftingTest.rawFunctor f).map (τ ≫ σ)).right z) =
    (fun z : LiftingTest.RawSquares f p =>
      ((LiftingTest.rawFunctor f).map σ).right
        (((LiftingTest.rawFunctor f).map τ).right z)) := by
  funext z
  exact congrFun (LiftingTest.rawSquareMap_comp f τ σ) z

private theorem original_whole_square_function {p q : Arrow C} (τ : p ⟶ q) :
    (fun z : LiftingTest.RawLifts f p =>
      ((LiftingTest.rawFunctor f).map τ).right
        (((LiftingTest.rawFunctor f).obj p).hom z)) =
    (fun z : LiftingTest.RawLifts f p =>
      ((LiftingTest.rawFunctor f).obj q).hom
        (((LiftingTest.rawFunctor f).map τ).left z)) :=
  LiftingTest.liftToSquare_naturality f τ

section Working

variable [Small.{w} ι] [LocallySmall.{w} C]

private theorem actual_source_smallness (p : Arrow C) :
    Small.{w} (LiftingTest.RawLifts f p) := inferInstance

private theorem actual_target_smallness (p : Arrow C) :
    Small.{w} (LiftingTest.RawSquares f p) := inferInstance

private theorem complete_original_source_roundtrip (p : Arrow C) :
    (fun z : LiftingTest.RawLifts f p =>
      (LiftingTest.liftsEquiv.{w} f p).symm (LiftingTest.liftsEquiv.{w} f p z)) = id := by
  funext z
  exact (LiftingTest.liftsEquiv.{w} f p).symm_apply_apply z

private theorem complete_original_target_roundtrip (p : Arrow C) :
    (fun z : LiftingTest.RawSquares f p =>
      (LiftingTest.squaresEquiv.{w} f p).symm (LiftingTest.squaresEquiv.{w} f p z)) = id := by
  funext z
  exact (LiftingTest.squaresEquiv.{w} f p).symm_apply_apply z

private theorem complete_small_source_roundtrip (p : Arrow C) :
    (fun z : Shrink.{w} (LiftingTest.RawLifts f p) =>
      LiftingTest.liftsEquiv.{w} f p ((LiftingTest.liftsEquiv.{w} f p).symm z)) = id := by
  funext z
  exact (LiftingTest.liftsEquiv.{w} f p).apply_symm_apply z

private theorem complete_small_target_roundtrip (p : Arrow C) :
    (fun z : Shrink.{w} (LiftingTest.RawSquares f p) =>
      LiftingTest.squaresEquiv.{w} f p ((LiftingTest.squaresEquiv.{w} f p).symm z)) = id := by
  funext z
  exact (LiftingTest.squaresEquiv.{w} f p).apply_symm_apply z

private theorem entire_normalized_original_forward_function :
    (fun (p : Arrow C) (z : LiftingTest.RawLifts f p) =>
      ((LiftingTest.smallFunctor.{w} f).obj p).hom
        (LiftingTest.liftsEquiv.{w} f p z)) =
    (fun (p : Arrow C) (z : LiftingTest.RawLifts f p) =>
      LiftingTest.squaresEquiv.{w} f p
        (⟨z.1, Arrow.homMk ((f z.1).hom ≫ z.2) (z.2 ≫ p.hom)
          (Category.assoc _ _ _)⟩ : LiftingTest.RawSquares f p)) := by
  funext p z
  exact congrFun (LiftingTest.smallFunctor_hom_function.{w} f p) z

private theorem entire_normalized_inverse_decoding_function :
    (fun (p : Arrow C) (z : Shrink.{w} (LiftingTest.RawLifts f p)) =>
      (LiftingTest.squaresEquiv.{w} f p).symm
        (((LiftingTest.smallFunctor.{w} f).obj p).hom z)) =
    (fun (p : Arrow C) (z : Shrink.{w} (LiftingTest.RawLifts f p)) =>
      LiftingTest.liftToSquare f p ((LiftingTest.liftsEquiv.{w} f p).symm z)) := by
  funext p z
  exact (LiftingTest.squaresEquiv.{w} f p).symm_apply_apply _

private theorem entire_normalized_original_source_map_function :
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawLifts f p) =>
      ((LiftingTest.smallFunctor.{w} f).map τ).left
        (LiftingTest.liftsEquiv.{w} f p z)) =
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawLifts f p) =>
      LiftingTest.liftsEquiv.{w} f q
        (⟨z.1, z.2 ≫ τ.left⟩ : LiftingTest.RawLifts f q)) := by
  funext p q τ z
  exact congrFun (LiftingTest.smallFunctor_map_left_function.{w} f τ) z

private theorem entire_normalized_original_target_map_function :
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawSquares f p) =>
      ((LiftingTest.smallFunctor.{w} f).map τ).right
        (LiftingTest.squaresEquiv.{w} f p z)) =
    (fun (p q : Arrow C) (τ : p ⟶ q) (z : LiftingTest.RawSquares f p) =>
      LiftingTest.squaresEquiv.{w} f q
        (⟨z.1, z.2 ≫ τ⟩ : LiftingTest.RawSquares f q)) := by
  funext p q τ z
  exact congrFun (LiftingTest.smallFunctor_map_right_function.{w} f τ) z

private theorem entire_normalized_inverse_source_map_function {p q : Arrow C} (τ : p ⟶ q) :
    (fun z : Shrink.{w} (LiftingTest.RawLifts f p) =>
      (LiftingTest.liftsEquiv.{w} f q).symm
        (((LiftingTest.smallFunctor.{w} f).map τ).left z)) =
    (fun z : Shrink.{w} (LiftingTest.RawLifts f p) =>
      LiftingTest.rawLiftMap f τ ((LiftingTest.liftsEquiv.{w} f p).symm z)) := by
  funext z
  exact (LiftingTest.liftsEquiv.{w} f q).symm_apply_apply _

private theorem entire_normalized_inverse_target_map_function {p q : Arrow C} (τ : p ⟶ q) :
    (fun z : Shrink.{w} (LiftingTest.RawSquares f p) =>
      (LiftingTest.squaresEquiv.{w} f q).symm
        (((LiftingTest.smallFunctor.{w} f).map τ).right z)) =
    (fun z : Shrink.{w} (LiftingTest.RawSquares f p) =>
      LiftingTest.rawSquareMap f τ ((LiftingTest.squaresEquiv.{w} f p).symm z)) := by
  funext z
  exact (LiftingTest.squaresEquiv.{w} f q).symm_apply_apply _

private theorem normalized_source_identity_function (p : Arrow C) :
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).left =>
      ((LiftingTest.smallFunctor.{w} f).map (𝟙 p)).left z) = id := by
  have h := congrArg Arrow.Hom.left ((LiftingTest.smallFunctor.{w} f).map_id p)
  funext z
  exact ConcreteCategory.congr_hom h z

private theorem normalized_target_identity_function (p : Arrow C) :
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).right =>
      ((LiftingTest.smallFunctor.{w} f).map (𝟙 p)).right z) = id := by
  have h := congrArg Arrow.Hom.right ((LiftingTest.smallFunctor.{w} f).map_id p)
  funext z
  exact ConcreteCategory.congr_hom h z

private theorem normalized_source_composition_function {p q r : Arrow C}
    (τ : p ⟶ q) (σ : q ⟶ r) :
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).left =>
      ((LiftingTest.smallFunctor.{w} f).map (τ ≫ σ)).left z) =
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).left =>
      ((LiftingTest.smallFunctor.{w} f).map σ).left
        (((LiftingTest.smallFunctor.{w} f).map τ).left z)) := by
  have h := congrArg Arrow.Hom.left ((LiftingTest.smallFunctor.{w} f).map_comp τ σ)
  funext z
  exact ConcreteCategory.congr_hom h z

private theorem normalized_target_composition_function {p q r : Arrow C}
    (τ : p ⟶ q) (σ : q ⟶ r) :
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).right =>
      ((LiftingTest.smallFunctor.{w} f).map (τ ≫ σ)).right z) =
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).right =>
      ((LiftingTest.smallFunctor.{w} f).map σ).right
        (((LiftingTest.smallFunctor.{w} f).map τ).right z)) := by
  have h := congrArg Arrow.Hom.right ((LiftingTest.smallFunctor.{w} f).map_comp τ σ)
  funext z
  exact ConcreteCategory.congr_hom h z

private theorem normalized_whole_square_function {p q : Arrow C} (τ : p ⟶ q) :
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).left =>
      ((LiftingTest.smallFunctor.{w} f).map τ).right
        (((LiftingTest.smallFunctor.{w} f).obj p).hom z)) =
    (fun z : ((LiftingTest.smallFunctor.{w} f).obj p).left =>
      ((LiftingTest.smallFunctor.{w} f).obj q).hom
        (((LiftingTest.smallFunctor.{w} f).map τ).left z)) := by
  funext z
  exact (ConcreteCategory.congr_hom ((LiftingTest.smallFunctor.{w} f).map τ).w z).symm

private theorem original_tested_arrow_isos_preserve_test_surjectivity
    {p q : Arrow C} (e : p ≅ q) :
    Function.Surjective ((LiftingTest.smallFunctor.{w} f).obj p).hom ↔
      Function.Surjective ((LiftingTest.smallFunctor.{w} f).obj q).hom := by
  rw [LiftingTest.smallFunctor_surjective_iff.{w},
    LiftingTest.smallFunctor_surjective_iff.{w}]
  let P : MorphismProperty C := MorphismProperty.ofHoms (fun k => (f k).hom)
  let _ : P.rlp.RespectsIso := by
    apply MorphismProperty.respectsIso_of_isStableUnderComposition
    intro A B i hi
    let _ : IsIso i := hi
    exact P.rlp_of_isIso i
  exact P.rlp.arrow_mk_iso_iff e

end Working
end MathlibExtTest.TaggedLiftingTestOwner
