/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Tests for factorization and lifting classes

The clients use explicit weak factorization proofs, independent universes and
the supplied order data of an actual transfinite composition.

The right-class clients use only factorization, right orthogonality and
relative cancellation, and obtain genuine square lifts from the public equality.
-/

set_option autoImplicit false

universe w v u

open CategoryTheory MorphismProperty

namespace MathlibExtTest.CategoryTheory.MorphismProperty.WeakFactorizationSystemTests

#check @IsStableUnderCoproducts.of_llp_eq
#check @IsStableUnderTransfiniteComposition.of_llp_eq
#check @IsWeakFactorizationSystem.isStableUnderCoproducts
#check @IsWeakFactorizationSystem.isStableUnderTransfiniteComposition

variable {C : Type u} [Category.{v} C]
variable (L R : MorphismProperty C)

example (h : R.llp = L) : L.IsStableUnderCoproducts.{w} :=
  IsStableUnderCoproducts.of_llp_eq L R h

example (h : R.llp = L) : L.IsStableUnderTransfiniteComposition.{w} :=
  IsStableUnderTransfiniteComposition.of_llp_eq L R h

example (h : IsWeakFactorizationSystem L R) : L.coproducts.{w} ≤ L := by
  let _ : L.IsStableUnderCoproducts.{w} :=
    IsWeakFactorizationSystem.isStableUnderCoproducts L R h
  exact L.coproducts_le

example (h : IsWeakFactorizationSystem L R) : L.transfiniteCompositions.{w} ≤ L := by
  let _ : L.IsStableUnderTransfiniteComposition.{w} :=
    IsWeakFactorizationSystem.isStableUnderTransfiniteComposition L R h
  exact L.transfiniteCompositions_le

example (h : IsWeakFactorizationSystem L R)
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : C} {f : X ⟶ Y} (c : L.TransfiniteCompositionOfShape J f)
    {a b : J} (φ : a ⟶ b) : L (c.F.map φ) := by
  let _ : L.IsStableUnderTransfiniteComposition.{w} :=
    IsWeakFactorizationSystem.isStableUnderTransfiniteComposition L R h
  exact c.mem_map φ

example {D : Type 2} [Category.{1} D] (P Q : MorphismProperty D)
    (h : IsWeakFactorizationSystem P Q) : P.IsStableUnderCoproducts.{0} :=
  IsWeakFactorizationSystem.isStableUnderCoproducts P Q h

example {D : Type 2} [Category.{1} D] (P Q : MorphismProperty D)
    (h : IsWeakFactorizationSystem P Q)
    {J : Type} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : D} {f : X ⟶ Y} (c : P.TransfiniteCompositionOfShape J f)
    {a b : J} (φ : a ⟶ b) : P (c.F.map φ) := by
  let _ : P.IsStableUnderTransfiniteComposition.{0} :=
    IsWeakFactorizationSystem.isStableUnderTransfiniteComposition P Q h
  exact c.mem_map φ

#print axioms IsStableUnderCoproducts.of_llp_eq
#print axioms IsStableUnderTransfiniteComposition.of_llp_eq
#print axioms IsWeakFactorizationSystem.isStableUnderCoproducts
#print axioms IsWeakFactorizationSystem.isStableUnderTransfiniteComposition

section WeakRightClass

variable (W : MorphismProperty C) [HasFactorization L R]
  [W.HasOfPostcompProperty R]

/-- Membership in the auxiliary class and the derived right class recovers `R`. -/
theorem right_of_weak_and_rlp (hR : L.rlp = R) (hRW : R ≤ W)
    {X Y : C} (p : X ⟶ Y) (hp : (L ⊓ W).rlp p) (hWp : W p) : R p := by
  rw [← rlp_inf_inf_eq_of_hasFactorization L R W hR hRW]
  exact ⟨hp, hWp⟩

/-- An `R`-map belongs to `W` and lifts any actual square from `L ⊓ W`. -/
theorem weak_and_lift_of_right (hR : L.rlp = R) (hRW : R ≤ W)
    {A B X Y : C} (a : A ⟶ B) (p : X ⟶ Y) (ha : L a) (hWa : W a) (hp : R p)
    (f : A ⟶ X) (g : B ⟶ Y) (sq : CommSq f a p g) :
    W p ∧ ∃ l : B ⟶ X, a ≫ l = f ∧ l ≫ p = g := by
  have hmem : ((L ⊓ W).rlp ⊓ W) p := by
    rw [rlp_inf_inf_eq_of_hasFactorization L R W hR hRW]
    exact hp
  have : HasLiftingProperty a p := hmem.1 a ⟨ha, hWa⟩
  exact ⟨hmem.2, sq.lift, sq.fac_left, sq.fac_right⟩

#print axioms rlp_inf_inf_eq_of_hasFactorization
#print axioms right_of_weak_and_rlp
#print axioms weak_and_lift_of_right

end WeakRightClass

section WeakFactorizationRightClass

variable (W : MorphismProperty C) [W.HasOfPostcompProperty R]

/-- An explicit WFS proof supplies the wrapper's factorization data; the client
obtains right-class membership and a strict square lift from its equality. -/
theorem weak_and_lift_of_wfs_right (h : IsWeakFactorizationSystem L R) (hRW : R ≤ W)
    {A B X Y : C} (a : A ⟶ B) (p : X ⟶ Y) (ha : L a) (hWa : W a) (hp : R p)
    (f : A ⟶ X) (g : B ⟶ Y) (sq : CommSq f a p g) :
    W p ∧ ∃ l : B ⟶ X, a ≫ l = f ∧ l ≫ p = g := by
  have hmem : ((L ⊓ W).rlp ⊓ W) p := by
    rw [IsWeakFactorizationSystem.rlp_inf_inf_eq L R W h hRW]
    exact hp
  have : HasLiftingProperty a p := hmem.1 a ⟨ha, hWa⟩
  exact ⟨hmem.2, sq.lift, sq.fac_left, sq.fac_right⟩

#check @IsWeakFactorizationSystem.rlp_inf_inf_eq
#check @weak_and_lift_of_wfs_right
#print axioms IsWeakFactorizationSystem.rlp_inf_inf_eq
#print axioms weak_and_lift_of_wfs_right

end WeakFactorizationRightClass

end MathlibExtTest.CategoryTheory.MorphismProperty.WeakFactorizationSystemTests
