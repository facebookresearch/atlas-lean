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

public import Mathlib.Algebra.Star.StarAlgHom
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator

import Mathlib.Tactic.NoncommRing

/-!
# Bounded Hilbert-space Fredholm modules over an involutive algebra

This file gives the neutral bounded-operator carrier shared by Connes's
Fredholm modules and the Hilbert-space specialization of Kasparov cycles.  The
source algebra is purely algebraic: it is not assumed normed, complete,
separable, or a C-star algebra.  Its representation is the existing
`NonUnitalStarAlgHom` into bounded Hilbert-space operators.

The bundled unnormalized carrier uses the right-localized compact defects of
Higson--Roe and Blackadar.  The left-localized form printed by Connes is
strictly equivalent, by compact-ideal, composition, and adjoint laws; it is
not a second set of structure fields.  Normalized odd and even carriers store
only their literal exact equations and compact commutators.

No quotient class, index, Calkin unit, `KK` object, scalar Hilbert-module
dictionary, or source theorem is part of these definitions.
-/

@[expose] public section

noncomputable section

namespace HilbertFredholmModule

universe uA uH

/-- The representation and bounded operator underlying a Hilbert-space
Fredholm module.  There are deliberately no compactness conclusions in this
raw carrier. -/
structure Data (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The possibly nonunital involutive complex representation. -/
  representation : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- The bounded cycle operator. -/
  operator : H →L[ℂ] H

variable {A : Type uA} {H : Type uH}
variable [NonUnitalRing A] [_root_.Module ℂ A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable [StarRing A] [StarModule ℂ A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ordinary commutator of the cycle operator with a represented
coefficient.  Graded source algebras require a separate signed extension. -/
def Data.commutator (M : Data A H) (a : A) : H →L[ℂ] H :=
  M.operator * M.representation a - M.representation a * M.operator

/-- The square defect `F² - 1`. -/
def Data.squareDefect (M : Data A H) : H →L[ℂ] H :=
  M.operator * M.operator - 1

/-- The adjoint defect `F - F*`. -/
def Data.adjointDefect (M : Data A H) : H →L[ℂ] H :=
  M.operator - star M.operator

/-- The right-localized compact-defect convention of Higson--Roe and
Blackadar. -/
def Data.IsRightFredholm (M : Data A H) : Prop :=
  (∀ a : A, IsCompactOperator (M.commutator a)) ∧
    (∀ a : A, IsCompactOperator (M.squareDefect * M.representation a)) ∧
    ∀ a : A, IsCompactOperator (M.adjointDefect * M.representation a)

/-- The left-localized compact-defect convention used in Connes's comparison
with normalized Fredholm modules. -/
def Data.IsLeftFredholm (M : Data A H) : Prop :=
  (∀ a : A, IsCompactOperator (M.commutator a)) ∧
    (∀ a : A, IsCompactOperator (M.representation a * M.squareDefect)) ∧
    ∀ a : A, IsCompactOperator (M.representation a * M.adjointDefect)

/-- An unnormalized bounded Hilbert-space Fredholm module, using one literal
set of right-localized compactness fields. -/
structure Module (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends Data A H where
  commutator_compact : ∀ a : A, IsCompactOperator (toData.commutator a)
  square_compact_right :
    ∀ a : A, IsCompactOperator (toData.squareDefect * toData.representation a)
  adjoint_compact_right :
    ∀ a : A, IsCompactOperator (toData.adjointDefect * toData.representation a)

/-- Package a proved right-oriented defining predicate.  This is only the
constructor for the literal fields, not a selected Fredholm output. -/
def Data.toModule (M : Data A H) (hM : M.IsRightFredholm) : Module A H where
  toData := M
  commutator_compact := hM.1
  square_compact_right := hM.2.1
  adjoint_compact_right := hM.2.2

/-- The bundled fields are exactly the right-localized Fredholm predicate. -/
theorem Module.isRightFredholm (M : Module A H) : M.toData.IsRightFredholm :=
  ⟨M.commutator_compact, M.square_compact_right, M.adjoint_compact_right⟩

omit [CompleteSpace H] in
private theorem compact_mul_left (S T : H →L[ℂ] H)
    (hT : IsCompactOperator T) : IsCompactOperator (S * T) := by
  change IsCompactOperator (S.comp T)
  exact hT.clm_comp S

omit [CompleteSpace H] in
private theorem compact_mul_right (T S : H →L[ℂ] H)
    (hT : IsCompactOperator T) : IsCompactOperator (T * S) := by
  change IsCompactOperator (T.comp S)
  exact hT.comp_clm S

private theorem squareDefect_commutator_identity (M : Data A H) (a : A) :
    M.squareDefect * M.representation a -
        M.representation a * M.squareDefect =
      M.operator * M.commutator a + M.commutator a * M.operator := by
  dsimp only [Data.squareDefect, Data.commutator]
  noncomm_ring

private theorem adjointDefect_commutator_identity (M : Data A H) (a : A) :
    M.adjointDefect * M.representation a -
        M.representation a * M.adjointDefect =
      M.commutator a + star (M.commutator (star a)) := by
  simp only [Data.adjointDefect, Data.commutator, map_star, star_sub,
    star_mul, star_star]
  noncomm_ring

private theorem squareDefect_difference_compact (M : Data A H)
    (hcomm : ∀ a : A, IsCompactOperator (M.commutator a)) (a : A) :
    IsCompactOperator
      (M.squareDefect * M.representation a -
        M.representation a * M.squareDefect) := by
  rw [squareDefect_commutator_identity]
  exact (compact_mul_left _ _ (hcomm a)).add
    (compact_mul_right _ _ (hcomm a))

private theorem adjointDefect_difference_compact (M : Data A H)
    (hcomm : ∀ a : A, IsCompactOperator (M.commutator a)) (a : A) :
    IsCompactOperator
      (M.adjointDefect * M.representation a -
        M.representation a * M.adjointDefect) := by
  have hstar : IsCompactOperator
      (ContinuousLinearMap.adjoint (M.commutator (star a))) :=
    (hcomm (star a)).adjoint
  have hstar' : IsCompactOperator
      (star (M.commutator (star a)) : H →L[ℂ] H) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hstar
  rw [adjointDefect_commutator_identity]
  exact (hcomm a).add hstar'

omit [CompleteSpace H] in
private theorem compact_left_of_right_of_sub
    (right left : H →L[ℂ] H)
    (hright : IsCompactOperator right)
    (hdiff : IsCompactOperator (right - left)) :
    IsCompactOperator left := by
  change IsCompactOperator (fun x => left x)
  have h := hright.sub hdiff
  change IsCompactOperator (fun x => right x - (right - left) x) at h
  have heq : (fun x => right x - (right - left) x) =
      (fun x => left x) := by
    funext x
    change right x - (right x - left x) = left x
    rw [sub_sub_cancel]
  rw [← heq]
  exact h

omit [CompleteSpace H] in
private theorem compact_right_of_left_of_sub
    (right left : H →L[ℂ] H)
    (hleft : IsCompactOperator left)
    (hdiff : IsCompactOperator (right - left)) :
    IsCompactOperator right := by
  change IsCompactOperator (fun x => right x)
  have h := hdiff.add hleft
  change IsCompactOperator (fun x => (right - left) x + left x) at h
  have heq : (fun x => (right - left) x + left x) =
      (fun x => right x) := by
    funext x
    change (right x - left x) + left x = right x
    rw [sub_add_cancel]
  rw [← heq]
  exact h

/-- The right- and left-localized compact-defect conventions are equivalent.
Only the right convention is stored in `Module`. -/
theorem Data.isRightFredholm_iff_isLeftFredholm (M : Data A H) :
    M.IsRightFredholm ↔ M.IsLeftFredholm := by
  constructor
  · rintro ⟨hcomm, hsquare, hadjoint⟩
    refine ⟨hcomm, ?_, ?_⟩
    · intro a
      exact compact_left_of_right_of_sub _ _ (hsquare a)
        (squareDefect_difference_compact M hcomm a)
    · intro a
      exact compact_left_of_right_of_sub _ _ (hadjoint a)
        (adjointDefect_difference_compact M hcomm a)
  · rintro ⟨hcomm, hsquare, hadjoint⟩
    refine ⟨hcomm, ?_, ?_⟩
    · intro a
      exact compact_right_of_left_of_sub _ _ (hsquare a)
        (squareDefect_difference_compact M hcomm a)
    · intro a
      exact compact_right_of_left_of_sub _ _ (hadjoint a)
        (adjointDefect_difference_compact M hcomm a)

/-- A right-localized square defect is also compact after localization on the
left. -/
theorem Module.square_compact_left (M : Module A H) (a : A) :
    IsCompactOperator (M.toData.representation a * M.toData.squareDefect) :=
  (M.toData.isRightFredholm_iff_isLeftFredholm.mp M.isRightFredholm).2.1 a

/-- A right-localized adjoint defect is also compact after localization on the
left. -/
theorem Module.adjoint_compact_left (M : Module A H) (a : A) :
    IsCompactOperator (M.toData.representation a * M.toData.adjointDefect) :=
  (M.toData.isRightFredholm_iff_isLeftFredholm.mp M.isRightFredholm).2.2 a

/-- The right-oriented bundled definition strictly implies Connes's
left-localized compact-defect convention. -/
theorem Module.isLeftFredholm (M : Module A H) : M.toData.IsLeftFredholm :=
  M.toData.isRightFredholm_iff_isLeftFredholm.mp M.isRightFredholm

/-- A normalized odd Fredholm module.  Compactness of the square and adjoint
defects is not requested because both defects are literally zero. -/
structure NormalizedOdd (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends Data A H where
  commutator_compact : ∀ a : A, IsCompactOperator (toData.commutator a)
  operator_selfAdjoint : star toData.operator = toData.operator
  operator_square : toData.operator * toData.operator = 1

/-- A normalized odd module gives an unnormalized module without any selected
compactness output. -/
def NormalizedOdd.toModule (M : NormalizedOdd A H) : Module A H where
  toData := M.toData
  commutator_compact := M.commutator_compact
  square_compact_right := by
    intro a
    rw [Data.squareDefect, M.operator_square, sub_self, zero_mul]
    exact isCompactOperator_zero
  adjoint_compact_right := by
    intro a
    rw [Data.adjointDefect, M.operator_selfAdjoint, sub_self, zero_mul]
    exact isCompactOperator_zero

/-- A normalized even Fredholm module over an ungraded source algebra.  The
grading is stored as the literal selfadjoint involution of Connes IV.1. -/
structure NormalizedEven (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends NormalizedOdd A H where
  /-- The self-adjoint grading involution on the Hilbert space. -/
  grading : H →L[ℂ] H
  grading_selfAdjoint : star grading = grading
  grading_square : grading * grading = 1
  representation_even : ∀ a : A,
    grading * toNormalizedOdd.toData.representation a =
      toNormalizedOdd.toData.representation a * grading
  operator_odd :
    grading * toNormalizedOdd.toData.operator =
      -(toNormalizedOdd.toData.operator * grading)

/-- Forgetting the grading of a normalized even module gives the same strict
unnormalized Fredholm module as its normalized odd part. -/
def NormalizedEven.toModule (M : NormalizedEven A H) : Module A H :=
  M.toNormalizedOdd.toModule

end HilbertFredholmModule
