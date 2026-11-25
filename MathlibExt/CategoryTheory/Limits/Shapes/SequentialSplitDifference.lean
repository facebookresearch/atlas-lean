/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOne

/-!
# The actual product difference of a split inverse tower

Specified sections of the adjacent tower maps give a specified section of
its standard product difference. The n-th coordinate is constructed by a
finite recursion, beginning with zero. No infinite sum, exactness of products,
abelian structure, or compatibility between the chosen sections is needed.
The difference and its signs are the existing `sequentialDifference`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCountableProducts C]
  (A : ℕᵒᵖ ⥤ C)
  (s : ∀ n : ℕ, A.obj (op n) ⟶ A.obj (op (n + 1)))
  (hs : ∀ n : ℕ, s n ≫ A.map (homOfLE (Nat.le_succ n)).op = 𝟙 _)

/-- The finite recursive coordinates of the actual difference section. -/
def sequentialDifferenceSectionCoordinate :
    ∀ n : ℕ, sequentialProduct A ⟶ A.obj (op n)
  | 0 => 0
  | n + 1 =>
      (sequentialDifferenceSectionCoordinate n - Pi.π (fun n : ℕ => A.obj (op n)) n) ≫ s n

@[simp]
theorem sequentialDifferenceSectionCoordinate_zero :
    sequentialDifferenceSectionCoordinate A s 0 = 0 := rfl

@[simp]
theorem sequentialDifferenceSectionCoordinate_succ (n : ℕ) :
    sequentialDifferenceSectionCoordinate A s (n + 1) =
      (sequentialDifferenceSectionCoordinate A s n -
        Pi.π (fun n : ℕ => A.obj (op n)) n) ≫ s n := rfl

include hs in
/-- Each coordinate satisfies the original signed difference equation. -/
theorem sequentialDifferenceSectionCoordinate_equation (n : ℕ) :
    sequentialDifferenceSectionCoordinate A s n -
        sequentialDifferenceSectionCoordinate A s (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op =
      Pi.π (fun n : ℕ => A.obj (op n)) n := by
  rw [sequentialDifferenceSectionCoordinate_succ, Category.assoc, hs, Category.comp_id]
  exact sub_sub_cancel _ _

/-- The section of the product difference uses the recursive coordinate family. -/
def sequentialDifferenceSection : sequentialProduct A ⟶ sequentialProduct A :=
  Pi.lift (sequentialDifferenceSectionCoordinate A s)

/-- Its projections are exactly the recursively specified finite coordinates. -/
@[reassoc]
theorem sequentialDifferenceSection_π (n : ℕ) :
    sequentialDifferenceSection A s ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      sequentialDifferenceSectionCoordinate A s n := Pi.lift_comp_π _ n

include hs in
/-- The recursive map is a section of the actual standard product difference. -/
@[reassoc]
theorem sequentialDifferenceSection_difference :
    sequentialDifferenceSection A s ≫ sequentialDifference A = 𝟙 (sequentialProduct A) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, sequentialDifference_π, Preadditive.comp_sub,
    sequentialDifferenceSection_π, ← Category.assoc,
    sequentialDifferenceSection_π, Category.id_comp]
  exact sequentialDifferenceSectionCoordinate_equation A s hs n

include hs in
/-- Adjacent specified sections earn split epimorphy of the existing product difference. -/
def sequentialDifferenceSplitEpi : SplitEpi (sequentialDifference A) where
  section_ := sequentialDifferenceSection A s
  id := sequentialDifferenceSection_difference A s hs

include s hs in
/-- In particular the original standard difference is epi; no product exactness is required. -/
theorem epi_sequentialDifference_of_sections : Epi (sequentialDifference A) :=
  (sequentialDifferenceSplitEpi A s hs).epi

/-- Any split adjacent tower maps supply a section, independently at each finite stage. -/
def sequentialDifferenceSplitEpiOfSplitTransitions
    [∀ n : ℕ, IsSplitEpi (A.map (homOfLE (Nat.le_succ n)).op)] :
    SplitEpi (sequentialDifference A) :=
  sequentialDifferenceSplitEpi A
    (fun n => CategoryTheory.section_ (A.map (homOfLE (Nat.le_succ n)).op))
    (fun n => IsSplitEpi.id (A.map (homOfLE (Nat.le_succ n)).op))

include s hs in
/-- Concrete sequential lim¹ vanishes for a tower with these original sections. -/
theorem isZero_sequentialLimOne_of_sections [HasCokernels C] :
    IsZero (sequentialLimOne A) := by
  letI : Epi (sequentialDifference A) := epi_sequentialDifference_of_sections A s hs
  exact isZero_sequentialLimOne_of_epi A

variable {A} {B : ℕᵒᵖ ⥤ C}
  (t : ∀ n : ℕ, B.obj (op n) ⟶ B.obj (op (n + 1)))

/-- If original tower maps commute with the specified sections, the recursive solutions
are natural. This extra section compatibility is not needed for the canonical Milnor maps. -/
@[reassoc]
theorem sequentialDifferenceSectionCoordinate_naturality (α : A ⟶ B)
    (hst : ∀ n : ℕ, s n ≫ α.app (op (n + 1)) = α.app (op n) ≫ t n) (n : ℕ) :
    sequentialProductMap α ≫ sequentialDifferenceSectionCoordinate B t n =
      sequentialDifferenceSectionCoordinate A s n ≫ α.app (op n) := by
  induction n with
  | zero => simp only [sequentialDifferenceSectionCoordinate_zero, comp_zero, zero_comp]
  | succ n hn =>
    rw [sequentialDifferenceSectionCoordinate_succ, sequentialDifferenceSectionCoordinate_succ,
      ← Category.assoc, Preadditive.comp_sub, hn, sequentialProductMap_π,
      ← Preadditive.sub_comp, Category.assoc, ← hst n, ← Category.assoc]

/-- The actual product-difference sections are natural under the same original section squares. -/
@[reassoc]
theorem sequentialDifferenceSection_naturality (α : A ⟶ B)
    (hst : ∀ n : ℕ, s n ≫ α.app (op (n + 1)) = α.app (op n) ≫ t n) :
    sequentialProductMap α ≫ sequentialDifferenceSection B t =
      sequentialDifferenceSection A s ≫ sequentialProductMap α := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, sequentialDifferenceSection_π, Category.assoc,
    sequentialProductMap_π, ← Category.assoc, sequentialDifferenceSection_π]
  exact sequentialDifferenceSectionCoordinate_naturality s t α hst n

end CategoryTheory.Limits
