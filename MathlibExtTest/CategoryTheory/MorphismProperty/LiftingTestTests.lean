/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.MorphismProperty.LiftingTest
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
universe w s u v

open CategoryTheory TypeCat MorphismProperty

namespace MathlibExtTest.TaggedLiftingTest

private def emptyMap : PEmpty.{w + 1} ⟶ PUnit.{w + 1} :=
  ofHom PEmpty.elim

private def pointGenerator : Arrow (Type w) := Arrow.mk emptyMap

private def pointFamily (_ : PUnit) : Arrow (Type w) := pointGenerator

private theorem point_hasLiftingProperty_iff (p : Arrow (Type w)) :
    HasLiftingProperty emptyMap p.hom ↔ Function.Surjective p.hom := by
  constructor
  · intro h y
    let _ : HasLiftingProperty emptyMap p.hom := h
    let sq : CommSq (ofHom PEmpty.elim) emptyMap p.hom (ofHom (fun _ => y)) :=
      ⟨by apply ConcreteCategory.hom_ext; intro z; cases z⟩
    exact ⟨sq.lift PUnit.unit,
      ConcreteCategory.congr_hom sq.fac_right PUnit.unit⟩
  · intro h
    refine ⟨fun {a} {b} sq => ?_⟩
    let l : PUnit.{w + 1} ⟶ p.left :=
      ofHom (fun _ => (h (b PUnit.unit)).choose)
    apply CommSq.HasLift.mk'
    refine { l := l, fac_left := ?_, fac_right := ?_ }
    · apply ConcreteCategory.hom_ext
      intro z
      cases z
    · apply ConcreteCategory.hom_ext
      intro z
      cases z
      exact (h (b PUnit.unit)).choose_spec

private theorem point_raw_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.rawFunctor pointFamily).obj p).hom ↔
      Function.Surjective p.hom := by
  rw [LiftingTest.rawFunctor_surjective_iff]
  constructor
  · intro h
    exact (point_hasLiftingProperty_iff p).mp (h PUnit.unit)
  · intro h k
    exact (point_hasLiftingProperty_iff p).mpr h

private theorem point_small_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.smallFunctor.{w} pointFamily).obj p).hom ↔
      Function.Surjective p.hom := by
  rw [LiftingTest.smallFunctor_surjective_iff.{w},
    ← LiftingTest.rawFunctor_surjective_iff_rlp]
  exact point_raw_surjective_iff p

private def foldMap : ULift.{w} Bool ⟶ PUnit.{w + 1} :=
  ofHom (fun _ => PUnit.unit)

private def foldGenerator : Arrow (Type w) := Arrow.mk foldMap

private def foldFamily (_ : PUnit) : Arrow (Type w) := foldGenerator

private theorem fold_hasLiftingProperty_iff (p : Arrow (Type w)) :
    HasLiftingProperty foldMap p.hom ↔ Function.Injective p.hom := by
  constructor
  · intro h a b hab
    let _ : HasLiftingProperty foldMap p.hom := h
    let top : ULift.{w} Bool ⟶ p.left :=
      ofHom (fun z => if z.down then b else a)
    let bottom : PUnit.{w + 1} ⟶ p.right := ofHom (fun _ => p.hom a)
    let sq : CommSq top foldMap p.hom bottom := ⟨by
      apply ConcreteCategory.hom_ext
      intro z
      rcases z with ⟨z⟩
      cases z
      · rfl
      · exact hab.symm⟩
    have ha : sq.lift PUnit.unit = a :=
      ConcreteCategory.congr_hom sq.fac_left ⟨false⟩
    have hb : sq.lift PUnit.unit = b :=
      ConcreteCategory.congr_hom sq.fac_left ⟨true⟩
    exact ha.symm.trans hb
  · intro h
    refine ⟨fun {top} {bottom} sq => ?_⟩
    let l : PUnit.{w + 1} ⟶ p.left := ofHom (fun _ => top ⟨false⟩)
    apply CommSq.HasLift.mk'
    refine { l := l, fac_left := ?_, fac_right := ?_ }
    · apply ConcreteCategory.hom_ext
      intro z
      rcases z with ⟨z⟩
      cases z
      · rfl
      · apply h
        exact (ConcreteCategory.congr_hom sq.w ⟨false⟩).trans
          (ConcreteCategory.congr_hom sq.w ⟨true⟩).symm
    · apply ConcreteCategory.hom_ext
      intro z
      cases z
      exact ConcreteCategory.congr_hom sq.w ⟨false⟩

private theorem fold_raw_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.rawFunctor foldFamily).obj p).hom ↔
      Function.Injective p.hom := by
  rw [LiftingTest.rawFunctor_surjective_iff]
  constructor
  · intro h
    exact (fold_hasLiftingProperty_iff p).mp (h PUnit.unit)
  · intro h k
    exact (fold_hasLiftingProperty_iff p).mpr h

private theorem fold_small_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.smallFunctor.{w} foldFamily).obj p).hom ↔
      Function.Injective p.hom := by
  rw [LiftingTest.smallFunctor_surjective_iff.{w},
    ← LiftingTest.rawFunctor_surjective_iff_rlp]
  exact fold_raw_surjective_iff p

private def bijectionFamily : Bool → Arrow (Type w)
  | false => pointGenerator
  | true => foldGenerator

private theorem combined_raw_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.rawFunctor bijectionFamily).obj p).hom ↔
      Function.Bijective p.hom := by
  rw [LiftingTest.rawFunctor_surjective_iff]
  constructor
  · intro h
    exact ⟨(fold_hasLiftingProperty_iff p).mp (h true),
      (point_hasLiftingProperty_iff p).mp (h false)⟩
  · intro h k
    cases k
    · exact (point_hasLiftingProperty_iff p).mpr h.2
    · exact (fold_hasLiftingProperty_iff p).mpr h.1

private theorem combined_small_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.smallFunctor.{w} bijectionFamily).obj p).hom ↔
      Function.Bijective p.hom := by
  rw [LiftingTest.smallFunctor_surjective_iff.{w},
    ← LiftingTest.rawFunctor_surjective_iff_rlp]
  exact combined_raw_surjective_iff p

private def emptyFamily : PEmpty.{s + 1} → Arrow (Type w) := PEmpty.elim

private theorem empty_raw_surjective (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.rawFunctor emptyFamily).obj p).hom := by
  rw [LiftingTest.rawFunctor_surjective_iff]
  intro k
  cases k

private theorem empty_small_surjective (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.smallFunctor.{w} emptyFamily).obj p).hom := by
  rw [LiftingTest.smallFunctor_surjective_iff.{w},
    ← LiftingTest.rawFunctor_surjective_iff_rlp]
  exact empty_raw_surjective p

private def duplicateFamily (_ : Bool) : Arrow (Type w) := pointGenerator

private theorem duplicate_arrows_equal :
    duplicateFamily.{w} false = duplicateFamily true := rfl

private theorem duplicate_lift_tags_distinct (p : Arrow (Type w))
    (l : PUnit.{w + 1} ⟶ p.left) :
    (⟨false, l⟩ : LiftingTest.RawLifts duplicateFamily p) ≠ ⟨true, l⟩ := by
  intro h
  have htag := congrArg Sigma.fst h
  exact Bool.false_ne_true htag

private theorem duplicate_square_tags_distinct (p : Arrow (Type w))
    (l : PUnit.{w + 1} ⟶ p.left) :
    LiftingTest.liftToSquare duplicateFamily p ⟨false, l⟩ ≠
      LiftingTest.liftToSquare duplicateFamily p ⟨true, l⟩ := by
  intro h
  have htag := congrArg Sigma.fst h
  exact Bool.false_ne_true htag

private theorem duplicate_square_values_equal (p : Arrow (Type w))
    (l : PUnit.{w + 1} ⟶ p.left) :
    (LiftingTest.liftToSquare duplicateFamily p ⟨false, l⟩).2 =
      (LiftingTest.liftToSquare duplicateFamily p ⟨true, l⟩).2 := rfl

private theorem duplicate_small_lift_tags_distinct (p : Arrow (Type w))
    (l : PUnit.{w + 1} ⟶ p.left) :
    LiftingTest.liftsEquiv.{w} duplicateFamily p ⟨false, l⟩ ≠
      LiftingTest.liftsEquiv.{w} duplicateFamily p ⟨true, l⟩ := by
  intro h
  exact duplicate_lift_tags_distinct p l
      ((LiftingTest.liftsEquiv.{w} duplicateFamily p).injective h)

private theorem duplicate_small_square_tags_distinct (p : Arrow (Type w))
    (l : PUnit.{w + 1} ⟶ p.left) :
    LiftingTest.squaresEquiv.{w} duplicateFamily p
        (LiftingTest.liftToSquare duplicateFamily p ⟨false, l⟩) ≠
      LiftingTest.squaresEquiv.{w} duplicateFamily p
        (LiftingTest.liftToSquare duplicateFamily p ⟨true, l⟩) := by
  intro h
  exact duplicate_square_tags_distinct p l
    ((LiftingTest.squaresEquiv.{w} duplicateFamily p).injective h)

private def boolIdentity : Arrow (Type w) := Arrow.mk (𝟙 (ULift.{w} Bool))

private def pointIdentity : Arrow (Type w) := Arrow.mk (𝟙 (PUnit.{w + 1}))

private def collapseSquare : boolIdentity.{w} ⟶ pointIdentity :=
  Arrow.homMk (ofHom (fun _ => PUnit.unit)) (ofHom (fun _ => PUnit.unit)) (by
    apply ConcreteCategory.hom_ext
    intro z
    rfl)

private def falseDiagonal : PUnit.{w + 1} ⟶ ULift.{w} Bool :=
  ofHom (fun _ => ⟨false⟩)

private def trueDiagonal : PUnit.{w + 1} ⟶ ULift.{w} Bool :=
  ofHom (fun _ => ⟨true⟩)

private theorem original_diagonals_distinct :
    falseDiagonal.{w} ≠ trueDiagonal := by
  intro h
  have hfalseTrue := congrArg ULift.down (ConcreteCategory.congr_hom h PUnit.unit)
  exact Bool.false_ne_true hfalseTrue

private theorem collapse_diagonal_values_equal :
    LiftingTest.rawLiftMap duplicateFamily collapseSquare ⟨false, falseDiagonal⟩ =
      LiftingTest.rawLiftMap duplicateFamily collapseSquare ⟨false, trueDiagonal⟩ := by
  apply congrArg (fun l => (⟨false, l⟩ :
    LiftingTest.RawLifts duplicateFamily pointIdentity))
  apply ConcreteCategory.hom_ext
  intro z
  rfl

private theorem collapse_preserves_distinct_generator_tags :
    LiftingTest.rawLiftMap duplicateFamily collapseSquare ⟨false, falseDiagonal⟩ ≠
      LiftingTest.rawLiftMap duplicateFamily collapseSquare ⟨true, trueDiagonal⟩ := by
  intro h
  exact Bool.false_ne_true (congrArg Sigma.fst h)

private theorem actual_collapse_whole_square_function :
    LiftingTest.rawSquareMap duplicateFamily collapseSquare ∘
        LiftingTest.liftToSquare duplicateFamily boolIdentity =
      LiftingTest.liftToSquare duplicateFamily pointIdentity ∘
        LiftingTest.rawLiftMap duplicateFamily collapseSquare :=
  LiftingTest.liftToSquare_naturality duplicateFamily collapseSquare

private theorem actual_collapse_whole_normalized_source_function :
    ((LiftingTest.smallFunctor.{w} duplicateFamily).map collapseSquare).left ∘
        LiftingTest.liftsEquiv.{w} duplicateFamily boolIdentity =
      LiftingTest.liftsEquiv.{w} duplicateFamily pointIdentity ∘
        LiftingTest.rawLiftMap duplicateFamily collapseSquare :=
  LiftingTest.smallFunctor_map_left_function.{w} duplicateFamily collapseSquare

private theorem actual_collapse_whole_normalized_target_function :
    ((LiftingTest.smallFunctor.{w} duplicateFamily).map collapseSquare).right ∘
        LiftingTest.squaresEquiv.{w} duplicateFamily boolIdentity =
      LiftingTest.squaresEquiv.{w} duplicateFamily pointIdentity ∘
        LiftingTest.rawSquareMap duplicateFamily collapseSquare :=
  LiftingTest.smallFunctor_map_right_function.{w} duplicateFamily collapseSquare

private def infiniteFamily (_ : Nat) : Arrow (Type w) := pointGenerator

private theorem infinite_original_tags (p : Arrow (Type w))
    (l : PUnit.{w + 1} ⟶ p.left) :
    (⟨0, l⟩ : LiftingTest.RawLifts infiniteFamily p) ≠ ⟨1, l⟩ := by
  intro h
  exact Nat.zero_ne_one (congrArg Sigma.fst h)

private theorem infinite_small_surjective_iff (p : Arrow (Type w)) :
    Function.Surjective ((LiftingTest.smallFunctor.{w} infiniteFamily).obj p).hom ↔
      Function.Surjective p.hom := by
  rw [LiftingTest.smallFunctor_surjective_iff.{w},
    ← LiftingTest.rawFunctor_surjective_iff_rlp, LiftingTest.rawFunctor_surjective_iff]
  constructor
  · intro h
    exact (point_hasLiftingProperty_iff p).mp (h 0)
  · intro h k
    exact (point_hasLiftingProperty_iff p).mpr h

section OriginalGeneration

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : HomotopicalAlgebra.CofibrantGenerationData C κ)

private theorem original_I_test (p : Arrow C) :
    letI : LocallySmall.{w} C := d.I_smallObject.locallySmall
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    Function.Surjective
      ((LiftingTest.smallFunctor.{w} (fun k : d.I.toSet => k.val)).obj p).hom ↔
        HomotopicalAlgebra.trivialFibrations C p.hom := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  rw [LiftingTest.smallFunctor_surjective_iff.{w}]
  change (ofHoms d.I.homFamily).rlp p.hom ↔ _
  rw [ofHoms_homFamily, d.I_rlp]

private theorem original_J_test (p : Arrow C) :
    letI : LocallySmall.{w} C := d.J_smallObject.locallySmall
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    Function.Surjective
      ((LiftingTest.smallFunctor.{w} (fun k : d.J.toSet => k.val)).obj p).hom ↔
        HomotopicalAlgebra.fibrations C p.hom := by
  let _ : LocallySmall.{w} C := d.J_smallObject.locallySmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  rw [LiftingTest.smallFunctor_surjective_iff.{w}]
  change (ofHoms d.J.homFamily).rlp p.hom ↔ _
  rw [ofHoms_homFamily, d.J_rlp]

end OriginalGeneration
end MathlibExtTest.TaggedLiftingTest
