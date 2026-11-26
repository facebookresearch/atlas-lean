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
# Bounded Hilbert-space Fredholm modules over star algebras

Let `A` be an algebraic nonunital complex star algebra and `H` a complete complex Hilbert space.
The representation `π : A → B(H)` is a nonunital complex star homomorphism, and `F ∈ B(H)` is
the cycle operator. An unnormalized Fredholm module requires compactness of `[F,π(a)]`,
`(F²-I)π(a)` and `(F-F*)π(a)` for every `a ∈ A`.

Localizing the two defects on the left is equivalent. A normalized odd module has `F*=F`, `F²=I`
and compact commutators. A normalized even module additionally has a self-adjoint involution `Γ`
with `Γπ(a)=π(a)Γ` and `ΓF=-FΓ`.

No norm, completeness, separability or C-star condition is imposed on the coefficient algebra
`A`. These definitions do not include a quotient class or index.
-/

@[expose] public section

noncomputable section

namespace HilbertFredholmModule

universe uA uH

/-- **Representation and bounded operator of a Fredholm cycle.** Let `A` be an algebraic
nonunital complex star algebra with compatible scalar multiplication and involution, and
`H` a complete complex Hilbert space. No norm, completeness or C-star condition is imposed
on `A`. `Data A H` consists of a nonunital complex star homomorphism `π : A → B(H)` and a
bounded cycle operator `F ∈ B(H)`, without compactness assumptions. -/
structure Data (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- **Star representation of a Hilbert-space cycle.** Let `A` be an algebraic nonunital
  complex star algebra with compatible scalar multiplication and involution, and `H` a
  complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
  `A`. the representation field is the nonunital complex star homomorphism `π : A →⋆ₙₐ[ℂ]
  B(H)`. -/
  representation : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- **Bounded cycle operator of a Hilbert-space module.** Let `A` be an algebraic nonunital
  complex star algebra with compatible scalar multiplication and involution, and `H` a
  complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
  `A`. the operator field is `F : H →L[ℂ] H`, with no self-adjointness or involution
  equation in the underlying data record. -/
  operator : H →L[ℂ] H

variable {A : Type uA} {H : Type uH}
variable [NonUnitalRing A] [_root_.Module ℂ A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable [StarRing A] [StarModule ℂ A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Cycle commutator with a represented coefficient.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. Let `π : A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation and cycle operator.
`Data.commutator a=Fπ(a)-π(a)F` for `a ∈ A`; this is the ordinary commutator for an
ungraded coefficient algebra. -/
def Data.commutator (M : Data A H) (a : A) : H →L[ℂ] H :=
  M.operator * M.representation a - M.representation a * M.operator

/-- **Square defect of a bounded Fredholm cycle.** Let `A` be an algebraic nonunital complex
star algebra with compatible scalar multiplication and involution, and `H` a complete
complex Hilbert space. No norm, completeness or C-star condition is imposed on `A`. Let `π
: A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation and cycle operator.
`Data.squareDefect=F²-I_H`. -/
def Data.squareDefect (M : Data A H) : H →L[ℂ] H :=
  M.operator * M.operator - 1

/-- **Adjoint defect of a bounded Fredholm cycle.** Let `A` be an algebraic nonunital complex
star algebra with compatible scalar multiplication and involution, and `H` a complete
complex Hilbert space. No norm, completeness or C-star condition is imposed on `A`. Let `π
: A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation and cycle operator.
`Data.adjointDefect=F-F*`. -/
def Data.adjointDefect (M : Data A H) : H →L[ℂ] H :=
  M.operator - star M.operator

/-- **Right-localized compact Fredholm cycle defects.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. Let `π : A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation and cycle operator.
`IsRightFredholm` means `[F,π(a)]`, `(F²-I)π(a)` and `(F-F*)π(a)` are compact for every `a
∈ A`. -/
def Data.IsRightFredholm (M : Data A H) : Prop :=
  (∀ a : A, IsCompactOperator (M.commutator a)) ∧
    (∀ a : A, IsCompactOperator (M.squareDefect * M.representation a)) ∧
    ∀ a : A, IsCompactOperator (M.adjointDefect * M.representation a)

/-- **Left-localized compact Fredholm cycle defects.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. Let `π : A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation and cycle operator.
`IsLeftFredholm` means `[F,π(a)]`, `π(a)(F²-I)` and `π(a)(F-F*)` are compact for every `a
∈ A`. -/
def Data.IsLeftFredholm (M : Data A H) : Prop :=
  (∀ a : A, IsCompactOperator (M.commutator a)) ∧
    (∀ a : A, IsCompactOperator (M.representation a * M.squareDefect)) ∧
    ∀ a : A, IsCompactOperator (M.representation a * M.adjointDefect)

/-- **Unnormalized bounded Hilbert-space Fredholm module.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. `Module A H` contains `π : A →⋆ₙₐ[ℂ] B(H)`, `F ∈ B(H)` and compactness of `[F,π(a)]`,
`(F²-I)π(a)` and `(F-F*)π(a)` for all `a ∈ A`. -/
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

/-- **Fredholm module from right-localized compact defects.** Let `A` be an algebraic
nonunital complex star algebra with compatible scalar multiplication and involution, and
`H` a complete complex Hilbert space. No norm, completeness or C-star condition is imposed
on `A`. Let `π : A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation and cycle operator.
if `[F,π(a)]`, `(F²-I)π(a)` and `(F-F*)π(a)` are compact for every `a`, `Data.toModule`
bundles those properties with the same representation and operator. -/
def Data.toModule (M : Data A H) (hM : M.IsRightFredholm) : Module A H where
  toData := M
  commutator_compact := hM.1
  square_compact_right := hM.2.1
  adjoint_compact_right := hM.2.2

/-- **Right-localized defining properties of a bundled module.** Let `A` be an algebraic
nonunital complex star algebra with compatible scalar multiplication and involution, and
`H` a complete complex Hilbert space. No norm, completeness or C-star condition is imposed
on `A`. for a bundled Fredholm module `(π,F)`, `[F,π(a)]`, `(F²-I)π(a)` and `(F-F*)π(a)`
are compact for every `a ∈ A`. -/
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

/-- **Equivalence of left and right localization of Fredholm defects.** Let `A` be an
algebraic nonunital complex star algebra with compatible scalar multiplication and
involution, and `H` a complete complex Hilbert space. No norm, completeness or C-star
condition is imposed on `A`. Let `π : A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` be the representation
and cycle operator. compactness of `[F,π(a)]`, `(F²-I)π(a)` and `(F-F*)π(a)` for all `a`
is equivalent to compactness of `[F,π(a)]`, `π(a)(F²-I)` and `π(a)(F-F*)` for all `a`. -/
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

/-- **Left-localized compact square defect.** Let `A` be an algebraic nonunital complex star
algebra with compatible scalar multiplication and involution, and `H` a complete complex
Hilbert space. No norm, completeness or C-star condition is imposed on `A`. for a Fredholm
module `(π,F)` and `a ∈ A`, `π(a)(F²-I_H)` is compact. -/
theorem Module.square_compact_left (M : Module A H) (a : A) :
    IsCompactOperator (M.toData.representation a * M.toData.squareDefect) :=
  (M.toData.isRightFredholm_iff_isLeftFredholm.mp M.isRightFredholm).2.1 a

/-- **Left-localized compact adjoint defect.** Let `A` be an algebraic nonunital complex star
algebra with compatible scalar multiplication and involution, and `H` a complete complex
Hilbert space. No norm, completeness or C-star condition is imposed on `A`. for a Fredholm
module `(π,F)` and `a ∈ A`, `π(a)(F-F*)` is compact. -/
theorem Module.adjoint_compact_left (M : Module A H) (a : A) :
    IsCompactOperator (M.toData.representation a * M.toData.adjointDefect) :=
  (M.toData.isRightFredholm_iff_isLeftFredholm.mp M.isRightFredholm).2.2 a

/-- **Left-localized Fredholm properties of the module.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. for a bundled Fredholm module `(π,F)`, the three operators `[F,π(a)]`, `π(a)(F²-I)`
and `π(a)(F-F*)` are compact for every `a ∈ A`. -/
theorem Module.isLeftFredholm (M : Module A H) : M.toData.IsLeftFredholm :=
  M.toData.isRightFredholm_iff_isLeftFredholm.mp M.isRightFredholm

/-- **Normalized odd Hilbert-space Fredholm module.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. `NormalizedOdd A H` consists of `π : A →⋆ₙₐ[ℂ] B(H)` and `F ∈ B(H)` with `F*=F`,
`F²=I_H` and compact `[F,π(a)]` for every `a ∈ A`. -/
structure NormalizedOdd (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends Data A H where
  commutator_compact : ∀ a : A, IsCompactOperator (toData.commutator a)
  operator_selfAdjoint : star toData.operator = toData.operator
  operator_square : toData.operator * toData.operator = 1

/-- **Unnormalized module of a normalized odd cycle.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. a normalized odd module `(π,F)` gives a Fredholm module with unchanged `π,F`; its
square and adjoint defects vanish because `F²=I_H` and `F*=F`. -/
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

/-- **Normalized even Hilbert-space Fredholm module.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. a normalized odd cycle `(π,F)` is equipped with `Γ ∈ B(H)` satisfying `Γ*=Γ`,
`Γ²=I_H`, `Γπ(a)=π(a)Γ` for all `a`, and `ΓF=-FΓ`. The coefficient algebra is ungraded. -/
structure NormalizedEven (A : Type uA) (H : Type uH)
    [NonUnitalRing A] [_root_.Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarRing A] [StarModule ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends NormalizedOdd A H where
  /-- **Self-adjoint grading of a normalized even cycle.** Let `A` be an algebraic nonunital
  complex star algebra with compatible scalar multiplication and involution, and `H` a
  complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
  `A`. the grading is a bounded `Γ ∈ B(H)` with `Γ*=Γ`, `Γ²=I_H`, commuting with the
  representation and anticommuting with the cycle operator. -/
  grading : H →L[ℂ] H
  grading_selfAdjoint : star grading = grading
  grading_square : grading * grading = 1
  representation_even : ∀ a : A,
    grading * toNormalizedOdd.toData.representation a =
      toNormalizedOdd.toData.representation a * grading
  operator_odd :
    grading * toNormalizedOdd.toData.operator =
      -(toNormalizedOdd.toData.operator * grading)

/-- **Fredholm module after forgetting an even grading.** Let `A` be an algebraic nonunital
complex star algebra with compatible scalar multiplication and involution, and `H` a
complete complex Hilbert space. No norm, completeness or C-star condition is imposed on
`A`. forgetting the grading `Γ` of a normalized even cycle `(π,F,Γ)` gives the
unnormalized Fredholm module of its normalized odd part, retaining `π,F`. -/
def NormalizedEven.toModule (M : NormalizedEven A H) : Module A H :=
  M.toNormalizedOdd.toModule

end HilbertFredholmModule
