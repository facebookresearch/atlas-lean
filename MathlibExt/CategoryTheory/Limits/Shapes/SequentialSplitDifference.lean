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
# Recursive right inverses of split tower differences

Let C be preadditive with countable products, A an inverse tower with transitions t_n :
A_{n+1} → A_n and s_n : A_n → A_{n+1} chosen sections, satisfying s_n ≫ t_n = id_{A_n}. On P_A
= ∏ₙA_n define r₀ = 0 and rₙ₊₁ = (rₙ−πₙ) ≫ sₙ. These finite recursive coordinates satisfy
rₙ−rₙ₊₁ ≫ tₙ = πₙ.

The product map R with coordinates rₙ therefore satisfies R ≫ d_A = id_{P_A}, where d_A is the
identity-minus-shift difference. Thus d_A is split epic and its cokernel lim¹ A is zero
whenever cokernels exist. If a tower map commutes with the chosen upward maps s_n, the
recursive coordinates and R are natural under that map. The construction uses only
preadditivity and countable products.
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

/-- Recursive coordinates associated to upward tower maps.

For a tower A in a preadditive category with countable products and maps s_n : A_n → A_{n+1},
define r_n : P_A → A_n by r₀ = 0 and rₙ₊₁ = (rₙ−πₙ) ≫ sₙ. Each coordinate uses a finite
recursion. -/
def sequentialDifferenceSectionCoordinate :
    ∀ n : ℕ, sequentialProduct A ⟶ A.obj (op n)
  | 0 => 0
  | n + 1 =>
      (sequentialDifferenceSectionCoordinate n - Pi.π (fun n : ℕ => A.obj (op n)) n) ≫ s n

/-- Initial recursive difference coordinate.

For an inverse tower A and upward maps s_n in a preadditive category with countable products,
the recursive coordinate r₀ : P_A → A₀ is the zero morphism. -/
@[simp]
theorem sequentialDifferenceSectionCoordinate_zero :
    sequentialDifferenceSectionCoordinate A s 0 = 0 := rfl

/-- Successor recursive difference coordinate.

For an inverse tower A and upward maps s_n : A_n → A_{n+1}, the recursive coordinates satisfy
rₙ₊₁ = (rₙ−πₙ) ≫ sₙ, where πₙ : P_A → A_n is the product projection. -/
@[simp]
theorem sequentialDifferenceSectionCoordinate_succ (n : ℕ) :
    sequentialDifferenceSectionCoordinate A s (n + 1) =
      (sequentialDifferenceSectionCoordinate A s n -
        Pi.π (fun n : ℕ => A.obj (op n)) n) ≫ s n := rfl

include hs in
/-- Signed difference equation for recursive section coordinates.

If the upward maps s_n are sections of the successor transitions t_n, so s_n ≫ t_n = id_{A_n},
then rₙ−rₙ₊₁ ≫ tₙ = πₙ for every n. The equation follows directly from the recursion rₙ₊₁ =
(rₙ−πₙ) ≫ sₙ. -/
theorem sequentialDifferenceSectionCoordinate_equation (n : ℕ) :
    sequentialDifferenceSectionCoordinate A s n -
        sequentialDifferenceSectionCoordinate A s (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op =
      Pi.π (fun n : ℕ => A.obj (op n)) n := by
  rw [sequentialDifferenceSectionCoordinate_succ, Category.assoc, hs, Category.comp_id]
  exact sub_sub_cancel _ _

/-- Product map determined by recursive difference coordinates.

For an inverse tower A in a preadditive category with countable products and upward maps s_n,
define R : P_A → P_A as the product lift of the coordinates r₀ = 0 and rₙ₊₁ = (rₙ−πₙ) ≫ sₙ.
Its right-inverse equation for d_A holds when the s_n are sections of the transitions. -/
def sequentialDifferenceSection : sequentialProduct A ⟶ sequentialProduct A :=
  Pi.lift (sequentialDifferenceSectionCoordinate A s)

/-- Projection formula for the recursive product map.

For an inverse tower A and upward maps s_n, the product lift R of the recursive coordinates
satisfies R ≫ πₙ = rₙ for every n. Here r₀ = 0 and rₙ₊₁ = (rₙ−πₙ) ≫ sₙ. -/
@[reassoc]
theorem sequentialDifferenceSection_π (n : ℕ) :
    sequentialDifferenceSection A s ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      sequentialDifferenceSectionCoordinate A s n := Pi.lift_comp_π _ n

include hs in
/-- Right-inverse equation for the split tower difference.

For an inverse tower A with chosen sections s_n of each successor transition, the recursive
product map R satisfies R ≫ d_A = id_{P_A}. Its coordinate equation is rₙ−rₙ₊₁ ≫ tₙ = πₙ, with
d_A = 1−shift. -/
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
/-- Split epimorphism of a tower difference from specified sections.

For an inverse tower A in a preadditive category with countable products and sections s_n ≫
t_n = id_{A_n}, the difference d_A is split epic. Its specified section is the recursive
product map R with r₀ = 0 and rₙ₊₁ = (rₙ−πₙ) ≫ sₙ. -/
def sequentialDifferenceSplitEpi : SplitEpi (sequentialDifference A) where
  section_ := sequentialDifferenceSection A s
  id := sequentialDifferenceSection_difference A s hs

include s hs in
/-- Epimorphism of a difference for a tower with chosen sections.

In a preadditive category with countable products, chosen right inverses s_n for all successor
transitions of A make d_A : P_A → P_A epic, because the recursive map R satisfies R ≫ d_A =
id_{P_A}. -/
theorem epi_sequentialDifference_of_sections : Epi (sequentialDifference A) :=
  (sequentialDifferenceSplitEpi A s hs).epi

/-- Split difference from split successor transitions.

If each successor transition of an inverse tower A is split epic in a preadditive category
with countable products, choose its section and apply the recursive coordinate construction.
This gives a SplitEpi structure on the identity-minus-shift difference d_A. -/
def sequentialDifferenceSplitEpiOfSplitTransitions
    [∀ n : ℕ, IsSplitEpi (A.map (homOfLE (Nat.le_succ n)).op)] :
    SplitEpi (sequentialDifference A) :=
  sequentialDifferenceSplitEpi A
    (fun n => CategoryTheory.section_ (A.map (homOfLE (Nat.le_succ n)).op))
    (fun n => IsSplitEpi.id (A.map (homOfLE (Nat.le_succ n)).op))

include s hs in
/-- Vanishing of lim-one for a tower with chosen transition sections.

In a preadditive category with countable products and cokernels, if sections s_n of every
successor transition of A are specified, then lim¹ A = Coker(d_A) is zero. The recursive
product map makes d_A split epic. -/
theorem isZero_sequentialLimOne_of_sections [HasCokernels C] :
    IsZero (sequentialLimOne A) := by
  letI : Epi (sequentialDifference A) := epi_sequentialDifference_of_sections A s hs
  exact isZero_sequentialLimOne_of_epi A

variable {A} {B : ℕᵒᵖ ⥤ C}
  (t : ∀ n : ℕ, B.obj (op n) ⟶ B.obj (op (n + 1)))

/-- Naturality of recursive difference coordinates.

Let α : A → B be a tower map and s_n : A_n → A_{n+1}, t_n : B_n → B_{n+1} upward maps
satisfying s_n ≫ α_{n+1} = α_n ≫ t_n. Their recursive coordinates satisfy P(α) ≫ r_B,n = r_A,n
≫ α_n. This coordinate identity uses the upward-map compatibility, without requiring them to
be transition sections. -/
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

/-- Naturality of recursive product difference maps.

For a tower map α : A → B commuting with upward maps s_n and t_n, the recursive product lifts
satisfy P(α) ≫ R_B = R_A ≫ P(α). Both are defined from r₀ = 0 and rₙ₊₁ = (rₙ−πₙ) followed by
the respective upward map. -/
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
