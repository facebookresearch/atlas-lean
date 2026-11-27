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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialSplitDifference
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialMittagLeffler

/-!
# Splitting the difference map after a finite stage

In a preadditive category with countable products, sections of the successor
maps from a stage N onward give a section of the standard product difference.
The finite prefix is solved backwards from zero at N, and the remaining
coordinates use forward recursion. Eventual isomorphisms therefore give
vanishing of the concrete sequential lim¹; in a concrete category they also
give the Mittag-Leffler condition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCountableProducts C]
  (A : ℕᵒᵖ ⥤ C) (N : ℕ)
  (s : ∀ n : ℕ, N ≤ n → (A.obj (op n) ⟶ A.obj (op (n + 1))))
  (hs : ∀ (n : ℕ) (hn : N ≤ n),
    s n hn ≫ A.map (homOfLE (Nat.le_succ n)).op = 𝟙 _)

/-- Extend eventual transition sections by the zero map before the cutoff. -/
def extendedTransitionSection (n : ℕ) :
    A.obj (op n) ⟶ A.obj (op (n + 1)) :=
  if hn : N ≤ n then s n hn else 0

/-- Solve a finite prefix of `k` difference equations backwards from zero at stage `n+k`. -/
def prefixDifferenceCoordinate :
    ∀ (k n : ℕ), sequentialProduct A ⟶ A.obj (op n)
  | 0, _ => 0
  | k + 1, n =>
      Pi.π (fun j : ℕ => A.obj (op j)) n +
        prefixDifferenceCoordinate k (n + 1) ≫ A.map (homOfLE (Nat.le_succ n)).op

/-- The existing forward recursion starts with zero at the eventual-section cutoff. -/
theorem forwardDifferenceCoordinate_at_cutoff :
    sequentialDifferenceSectionCoordinate A (extendedTransitionSection A N s) N = 0 := by
  cases N with
  | zero => exact sequentialDifferenceSectionCoordinate_zero A _
  | succ m =>
      rw [sequentialDifferenceSectionCoordinate_succ, extendedTransitionSection,
        dif_neg (by omega : ¬ m + 1 ≤ m), comp_zero]

/-- Coordinates of a section of the given difference, with a finite backwards recursion before the
stated cutoff and the existing forward recursion after it. -/
def sequentialDifferenceEventuallySectionCoordinate (n : ℕ) :
    sequentialProduct A ⟶ A.obj (op n) :=
  if n < N then prefixDifferenceCoordinate A (N - n) n
  else sequentialDifferenceSectionCoordinate A (extendedTransitionSection A N s) n

include hs in
/-- Every coordinate satisfies the signed equation for the given tower. -/
theorem sequentialDifferenceEventuallySectionCoordinate_equation (n : ℕ) :
    sequentialDifferenceEventuallySectionCoordinate A N s n -
        sequentialDifferenceEventuallySectionCoordinate A N s (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op =
      Pi.π (fun j : ℕ => A.obj (op j)) n := by
  by_cases hn : n < N
  · by_cases hn' : n + 1 < N
    · have hgap : N - n = (N - (n + 1)) + 1 := by omega
      rw [sequentialDifferenceEventuallySectionCoordinate, if_pos hn,
        sequentialDifferenceEventuallySectionCoordinate, if_pos hn', hgap,
        prefixDifferenceCoordinate]
      exact add_sub_cancel_right _ _
    · have hcut : n + 1 = N := by omega
      have hnext : sequentialDifferenceEventuallySectionCoordinate A N s (n + 1) = 0 := by
        rw [sequentialDifferenceEventuallySectionCoordinate, if_neg hn', hcut]
        exact forwardDifferenceCoordinate_at_cutoff A N s
      have hgap : N - n = 1 := by omega
      rw [hnext, zero_comp, sub_zero, sequentialDifferenceEventuallySectionCoordinate,
        if_pos hn, hgap, prefixDifferenceCoordinate, prefixDifferenceCoordinate,
        zero_comp, add_zero]
  · have hNn : N ≤ n := by omega
    have hn' : ¬ n + 1 < N := by omega
    have hsection : extendedTransitionSection A N s n ≫
        A.map (homOfLE (Nat.le_succ n)).op = 𝟙 _ := by
      rw [extendedTransitionSection, dif_pos hNn]
      exact hs n hNn
    rw [sequentialDifferenceEventuallySectionCoordinate, if_neg hn,
      sequentialDifferenceEventuallySectionCoordinate, if_neg hn',
      sequentialDifferenceSectionCoordinate_succ, Category.assoc, hsection, Category.comp_id]
    exact sub_sub_cancel _ _

/-- The countable-product map assembled from these finite recursions. -/
def sequentialDifferenceEventuallySection : sequentialProduct A ⟶ sequentialProduct A :=
  Pi.lift (sequentialDifferenceEventuallySectionCoordinate A N s)

/-- The product coordinates of the difference section are the stated recursions. -/
@[reassoc]
theorem sequentialDifferenceEventuallySection_π (n : ℕ) :
    sequentialDifferenceEventuallySection A N s ≫
        Pi.π (fun j : ℕ => A.obj (op j)) n =
      sequentialDifferenceEventuallySectionCoordinate A N s n :=
  Pi.lift_comp_π _ n

include hs in
/-- The finite-prefix construction is a section of the existing standard difference. -/
@[reassoc]
theorem sequentialDifferenceEventuallySection_difference :
    sequentialDifferenceEventuallySection A N s ≫ sequentialDifference A =
      𝟙 (sequentialProduct A) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, sequentialDifference_π, Preadditive.comp_sub,
    sequentialDifferenceEventuallySection_π, ← Category.assoc,
    sequentialDifferenceEventuallySection_π, Category.id_comp]
  exact sequentialDifferenceEventuallySectionCoordinate_equation A N s hs n

include hs in
/-- Eventual adjacent sections split the given whole-tower difference. -/
def sequentialDifferenceSplitEpiOfEventuallySections : SplitEpi (sequentialDifference A) where
  section_ := sequentialDifferenceEventuallySection A N s
  id := sequentialDifferenceEventuallySection_difference A N s hs

include s hs in
/-- A finite prefix imposes no obstruction to vanishing of concrete sequential `lim¹`. -/
theorem isZero_sequentialLimOne_of_eventually_sections [HasCokernels C] :
    IsZero (sequentialLimOne A) := by
  letI : Epi (sequentialDifference A) :=
    (sequentialDifferenceSplitEpiOfEventuallySections A N s hs).epi
  exact isZero_sequentialLimOne_of_epi A

/-- Eventual adjacent isomorphisms earn a section of the standard difference. -/
def sequentialDifferenceSplitEpiOfEventuallyTransitionIso
    (h : ∀ n : ℕ, N ≤ n → IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    SplitEpi (sequentialDifference A) := by
  let s' : ∀ n : ℕ, N ≤ n → (A.obj (op n) ⟶ A.obj (op (n + 1))) := fun n hn => by
    letI : IsIso (A.map (homOfLE (Nat.le_succ n)).op) := h n hn
    exact inv (A.map (homOfLE (Nat.le_succ n)).op)
  have hs' (n : ℕ) (hn : N ≤ n) :
      s' n hn ≫ A.map (homOfLE (Nat.le_succ n)).op = 𝟙 _ := by
    letI : IsIso (A.map (homOfLE (Nat.le_succ n)).op) := h n hn
    exact IsIso.inv_hom_id _
  exact sequentialDifferenceSplitEpiOfEventuallySections A N s' hs'

/-- Every eventually isomorphic inverse sequence has zero concrete sequential `lim¹`, in an
arbitrary preadditive category with the required products and cokernels. -/
theorem isZero_sequentialLimOne_of_eventually_transition_iso [HasCokernels C]
    (h : ∀ n : ℕ, N ≤ n → IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (sequentialLimOne A) := by
  letI : Epi (sequentialDifference A) :=
    (sequentialDifferenceSplitEpiOfEventuallyTransitionIso A N h).epi
  exact isZero_sequentialLimOne_of_epi A

end CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w u v

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- Eventual adjacent isomorphisms imply the ordinary numerical Mittag--Leffler condition. -/
theorem isSequentialMittagLeffler_of_eventually_transition_iso
    (A : ℕᵒᵖ ⥤ C) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    A.IsSequentialMittagLeffler := by
  let U := A ⋙ forget C
  apply U.isMittagLeffler_of_eventually_surjective_transition
  refine ⟨N, fun n hn => ?_⟩
  letI : IsIso (A.map (homOfLE (Nat.le_succ n)).op) := h n hn
  letI : IsIso (U.map (homOfLE (Nat.le_succ n)).op) :=
    (forget C).map_isIso _
  exact (CategoryTheory.isIso_iff_bijective _).mp inferInstance |>.surjective

end CategoryTheory.Functor

end
