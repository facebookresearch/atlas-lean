/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveIsomorphismArrow

import Mathlib.CategoryTheory.SingleObj

/-!
# Tests for the isomorphism-arrow nerve source

These tests pin the source and identity-arrow functors, their nerve maps, the
strict section equation, both endpoints and the over-source equation of the
deformation, arbitrary nonidentity base change, and the degree-zero and
degree-one source/target formulas for `isomorphismArrowNerveObjEquiv`.  They
also exercise a one-object nontrivial groupoid and all four combinations of
object and hom universe levels zero and one.  Negative guards exclude global
categorical-property, fibration, category-bar, Theorem A/B, and Quillen claims.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
  CartesianMonoidalCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.CategoryTheory.NerveIsomorphismArrowTests

variable {D : Type u} [Category.{v} D]

section Functors

example : CategoryTheory.IsomorphismArrow D ⥤ D :=
  CategoryTheory.isomorphismArrowSource D

example : D ⥤ CategoryTheory.IsomorphismArrow D :=
  CategoryTheory.isomorphismArrowIdentity D

example (e : CategoryTheory.IsomorphismArrow D) :
    (CategoryTheory.isomorphismArrowSource D).obj e = e.left :=
  CategoryTheory.isomorphismArrowSource_obj D e

example (X : D) :
    ((CategoryTheory.isomorphismArrowIdentity D).obj X).hom = 𝟙 X :=
  CategoryTheory.isomorphismArrowIdentity_obj_hom D X

example :
    CategoryTheory.isomorphismArrowIdentity D ⋙
        CategoryTheory.isomorphismArrowSource D =
      Functor.id D :=
  CategoryTheory.isomorphismArrowIdentity_comp_source (D := D)

example (e : CategoryTheory.IsomorphismArrow D) :
    ((CategoryTheory.isomorphismArrowSourceToIdentity (D := D)).app e).left =
      𝟙 e.left :=
  CategoryTheory.isomorphismArrowSourceToIdentity_app_left D e

example (e : CategoryTheory.IsomorphismArrow D) :
    ((CategoryTheory.isomorphismArrowSourceToIdentity (D := D)).app e).right =
      e.hom :=
  CategoryTheory.isomorphismArrowSourceToIdentity_app_right D e

end Functors

section NerveMaps

example :
    CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D) ⟶
      CategoryTheory.nerve D :=
  CategoryTheory.isomorphismArrowNerveSource D

example :
    CategoryTheory.nerve D ⟶
      CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D) :=
  CategoryTheory.isomorphismArrowNerveIdentity D

example (e : CategoryTheory.IsomorphismArrow D) :
    (CategoryTheory.isomorphismArrowNerveSource D).app (op ⦋0⦌)
        (ComposableArrows.mk₀ e) =
      ComposableArrows.mk₀ e.left :=
  CategoryTheory.isomorphismArrowNerveSource_app_mk₀ D e

example (X : D) :
    (CategoryTheory.isomorphismArrowNerveIdentity D).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀
        ((CategoryTheory.isomorphismArrowIdentity D).obj X) :=
  CategoryTheory.isomorphismArrowNerveIdentity_app_mk₀ D X

example {e e' : CategoryTheory.IsomorphismArrow D} (f : e ⟶ e') :
    (CategoryTheory.isomorphismArrowNerveSource D).app (op ⦋1⦌)
        (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ f.left :=
  CategoryTheory.isomorphismArrowNerveSource_app_mk₁ D f

example {X Y : D} (f : X ⟶ Y) :
    (CategoryTheory.isomorphismArrowNerveIdentity D).app (op ⦋1⦌)
        (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁
        ((CategoryTheory.isomorphismArrowIdentity D).map f) :=
  CategoryTheory.isomorphismArrowNerveIdentity_app_mk₁ D f

example :
    CategoryTheory.isomorphismArrowNerveIdentity D ≫
        CategoryTheory.isomorphismArrowNerveSource D =
      𝟙 (CategoryTheory.nerve D) :=
  CategoryTheory.isomorphismArrowNerveIdentity_comp_source (D := D)

end NerveMaps

section HomotopyOver

private noncomputable abbrev split :=
  CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
    (D := D)

example :
    (split (D := D)).section_ =
      CategoryTheory.isomorphismArrowNerveIdentity D :=
  rfl

example :
    (split (D := D)).section_ ≫
        CategoryTheory.isomorphismArrowNerveSource D =
      𝟙 (CategoryTheory.nerve D) :=
  (split (D := D)).section_comp

example :
    SSet.ι₀ ≫ (split (D := D)).homotopyOver.h =
      CategoryTheory.isomorphismArrowNerveSource D ≫
        CategoryTheory.isomorphismArrowNerveIdentity D :=
  (split (D := D)).homotopyOver.h₀

example :
    SSet.ι₁ ≫ (split (D := D)).homotopyOver.h =
      𝟙 (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D)) :=
  (split (D := D)).homotopyOver.h₁

example :
    (split (D := D)).homotopyOver.h ≫
        CategoryTheory.isomorphismArrowNerveSource D =
      fst (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D))
          (Δ[1] : SSet.{max u v}) ≫
        ((CategoryTheory.isomorphismArrowNerveSource D ≫
            CategoryTheory.isomorphismArrowNerveIdentity D) ≫
          CategoryTheory.isomorphismArrowNerveSource D) :=
  (split (D := D)).homotopyOver.over

example : SSet.realizationWeakEquivalences
    (CategoryTheory.isomorphismArrowNerveSource D) :=
  (split (D := D)).mem_realizationWeakEquivalences

variable (X : SSet.{max u v})
  (f : X ⟶ CategoryTheory.nerve D)

example : SSet.realizationWeakEquivalences
    (pullback.fst f (CategoryTheory.isomorphismArrowNerveSource D)) :=
  CategoryTheory.isomorphismArrowNerveSource_baseChange_mem_realizationWeakEquivalences
    D f

/-- Base change along the source map itself is a concrete nonidentity base
change, not the identity-base specialization. -/
example : SSet.realizationWeakEquivalences
    (pullback.fst
      (CategoryTheory.isomorphismArrowNerveSource D)
      (CategoryTheory.isomorphismArrowNerveSource D)) :=
  CategoryTheory.isomorphismArrowNerveSource_baseChange_mem_realizationWeakEquivalences
      D (CategoryTheory.isomorphismArrowNerveSource D)

end HomotopyOver

section ObjectEquivalence

example (a : SimplexCategoryᵒᵖ) :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D)).obj a ≃
      Σ X Y : ComposableArrows D a.unop.len, X ≅ Y :=
  CategoryTheory.isomorphismArrowNerveObjEquiv (D := D) a

example (Z :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D)).obj
      (op ⦋0⦌)) :
    (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := D) (op ⦋0⦌) Z).1 =
        ComposableArrows.mk₀ (Z.obj 0).left := by
  rw [CategoryTheory.isomorphismArrowNerveObjEquiv_source]
  exact ComposableArrows.ext₀ rfl

example (Z :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D)).obj
      (op ⦋0⦌)) :
    (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := D) (op ⦋0⦌) Z).2.1 =
        ComposableArrows.mk₀ (Z.obj 0).right := by
  rw [CategoryTheory.isomorphismArrowNerveObjEquiv_target]
  exact ComposableArrows.ext₀ rfl

example (Z :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D)).obj
      (op ⦋1⦌)) :
    (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := D) (op ⦋1⦌) Z).1 =
        ComposableArrows.mk₁ (Z.map' 0 1).left := by
  rw [CategoryTheory.isomorphismArrowNerveObjEquiv_source]
  let W := ((CategoryTheory.isomorphismArrowSource D).mapComposableArrows 1).obj Z
  change W = _
  have hW : W.hom = (Z.map' 0 1).left :=
    CategoryTheory.isomorphismArrowSource_map D _
  rw [← hW]
  exact (ComposableArrows.mk₁_hom W).symm

example (Z :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D)).obj
      (op ⦋1⦌)) :
    (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := D) (op ⦋1⦌) Z).2.1 =
        ComposableArrows.mk₁ (Z.map' 0 1).right := by
  rw [CategoryTheory.isomorphismArrowNerveObjEquiv_target]
  let W := ((CategoryTheory.isomorphismArrowTarget D).mapComposableArrows 1).obj Z
  change W = _
  have hW : W.hom = (Z.map' 0 1).right :=
    CategoryTheory.isomorphismArrowTarget_map D _
  rw [← hW]
  exact (ComposableArrows.mk₁_hom W).symm

example (X Y : ComposableArrows D 1) (e : X ≅ Y) :
    (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := D) (op ⦋1⦌)).symm ⟨X, Y, e⟩ =
        CategoryTheory.isomorphismArrowComposableOfIso D X Y e :=
  rfl

end ObjectEquivalence

section NontrivialGroupoid

private abbrev TwoGroupoid :=
  CategoryTheory.SingleObj (Equiv.Perm (Fin 2))

private def swapPermutation : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

private def swapArrow : CategoryTheory.IsomorphismArrow TwoGroupoid :=
  { left := CategoryTheory.SingleObj.star _
    right := CategoryTheory.SingleObj.star _
    hom := (CategoryTheory.SingleObj.toEnd _ swapPermutation).asHom
    prop := by infer_instance }

private theorem swapPermutation_ne_one : swapPermutation ≠ 1 := by
  intro h
  have h0 := congrArg (fun e : Equiv.Perm (Fin 2) ↦ e 0) h
  simp [swapPermutation] at h0

example : swapPermutation ≠ 1 :=
  swapPermutation_ne_one

example : swapArrow.hom ≠ 𝟙 swapArrow.left := by
  intro h
  apply swapPermutation_ne_one
  change swapPermutation = 1 at h
  exact h

example :
    ((CategoryTheory.isomorphismArrowSourceToIdentity
      (D := TwoGroupoid)).app swapArrow).right = swapArrow.hom :=
  rfl

example : SSet.SplitHomotopyEquivOver
    (CategoryTheory.isomorphismArrowNerveSource TwoGroupoid) :=
  CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
    (D := TwoGroupoid)

end NontrivialGroupoid

section TypeZero

variable {D₀₀ : Type} [Category D₀₀]

example : SSet.SplitHomotopyEquivOver
    (CategoryTheory.isomorphismArrowNerveSource D₀₀) :=
  CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
    (D := D₀₀)

example :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D₀₀)).obj
        (op ⦋0⦌) ≃
      Σ X Y : ComposableArrows D₀₀ 0, X ≅ Y :=
  CategoryTheory.isomorphismArrowNerveObjEquiv (D := D₀₀) (op ⦋0⦌)

end TypeZero

section TypeOne

variable {D₁₁ : Type 1} [Category.{1} D₁₁]

example : SSet.SplitHomotopyEquivOver
    (CategoryTheory.isomorphismArrowNerveSource D₁₁) :=
  CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
    (D := D₁₁)

example :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D₁₁)).obj
        (op ⦋0⦌) ≃
      Σ X Y : ComposableArrows D₁₁ 0, X ≅ Y :=
  CategoryTheory.isomorphismArrowNerveObjEquiv (D := D₁₁) (op ⦋0⦌)

end TypeOne

section MixedObjectSmallHomLarge

variable {D₀₁ : Type} [Category.{1} D₀₁]

example : SSet.SplitHomotopyEquivOver
    (CategoryTheory.isomorphismArrowNerveSource D₀₁) :=
  CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
    (D := D₀₁)

example :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D₀₁)).obj
        (op ⦋1⦌) ≃
      Σ X Y : ComposableArrows D₀₁ 1, X ≅ Y :=
  CategoryTheory.isomorphismArrowNerveObjEquiv (D := D₀₁) (op ⦋1⦌)

end MixedObjectSmallHomLarge

section MixedObjectLargeHomSmall

variable {D₁₀ : Type 1} [Category.{0} D₁₀]

example : SSet.SplitHomotopyEquivOver
    (CategoryTheory.isomorphismArrowNerveSource D₁₀) :=
  CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
    (D := D₁₀)

example :
    (CategoryTheory.nerve (CategoryTheory.IsomorphismArrow D₁₀)).obj
        (op ⦋1⦌) ≃
      Σ X Y : ComposableArrows D₁₀ 1, X ≅ Y :=
  CategoryTheory.isomorphismArrowNerveObjEquiv (D := D₁₀) (op ⦋1⦌)

end MixedObjectLargeHomSmall

section Nonclaims

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (CategoryTheory.isomorphismArrowSource D).Full

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (CategoryTheory.isomorphismArrowSource D).Faithful

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (CategoryTheory.isomorphismArrowSource D).IsEquivalence

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (CategoryTheory.isomorphismArrowSource D).Final

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (CategoryTheory.isomorphismArrowSource D).Initial

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth Fibration (CategoryTheory.isomorphismArrowNerveSource D)

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.isomorphismArrowTheoremA

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.isomorphismArrowTheoremB

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.isomorphismArrowCategoryBarComparison

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridStageProjectionRowPullbackIso

end Nonclaims

#print axioms CategoryTheory.IsomorphismArrow
#print axioms CategoryTheory.isomorphismArrowSourceToIdentity
#print axioms CategoryTheory.isomorphismArrowNerveIdentity
#print axioms CategoryTheory.isomorphismArrowNerveSourceHomotopyOver
#print axioms CategoryTheory.isomorphismArrowNerveSource_splitHomotopyEquivOver
#print axioms CategoryTheory.isomorphismArrowNerveSource_baseChange_mem_realizationWeakEquivalences
#print axioms CategoryTheory.isomorphismArrowNerveObjEquiv

end MathlibExtTest.CategoryTheory.NerveIsomorphismArrowTests

end
