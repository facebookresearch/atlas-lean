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

public import MathlibExt.Analysis.CStarAlgebra.Extension.StableSum.Equivalence

/-!
# Stable extension classes relative to coherent folds

Fix compatible matrix-fold data `S` whose Busby sum is associative and commutative up to strong
multiplier-unitary equivalence. Quotient the Busby homomorphisms `A → Q(B)` by stable strong
equivalence, meaning strong equivalence after adjoining liftable summands.

The quotient has addition `[τ₁]+[τ₂] = [S.sum τ₁ τ₂]` and zero `[0]`, forming a commutative
additive monoid. Every liftable Busby map represents zero. These classes and operations are
parameterized by `S,hS`; the domain needs only a possibly nonunital, nonassociative semiring
with distributive complex scalar action and additive involution.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra Matrix MultiplierAlgebra

namespace CStarExtension

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
variable [NonUnitalCStarAlgebra B]

/-- **Setoid of stable strong Busby equivalence.** For `S` with associativity and commutativity up
to strong equivalence, the setoid relation is `StablyStrongEquivalent S`. -/
def StableSumData.setoid (S : StableSumData A B) (hS : S.IsCoherent) :
    Setoid (BusbyHom A B) where
  r := StablyStrongEquivalent S
  iseqv := by exact stably_strong_equivalent_equivalence S hS

/-- **Stable Busby classes for coherent folds.** `StableClass S hS` is the quotient of Busby
homomorphisms `A → Q(B)` by stable strong equivalence relative to `S`. -/
abbrev StableClass (S : StableSumData A B) (hS : S.IsCoherent) :=
  Quotient (S.setoid hS)

/-- **Strong equivalence implies stable strong equivalence.** Strongly unitarily equivalent Busby
maps become stably strongly equivalent for any compatible `S`, using the zero liftable summand
on both sides. -/
theorem StableSumData.stably_strong_equivalent_of_strong
    (S : StableSumData A B)
    {tau₁ tau₂ : BusbyHom A B}
    (h : StronglyUnitaryEquivalent tau₁ tau₂) :
    StablyStrongEquivalent S tau₁ tau₂ := by
  refine ⟨0, 0, zero_is_trivial, zero_is_trivial, ?_⟩
  exact S.sum_congr_strong h
    (strongly_unitary_equivalent_refl
      (0 : BusbyHom A B))

/-- **Interchange of coherent Busby sums.** If `S.IsCoherent`, the sums `(τ₁+τ₂)+(σ₁+σ₂)` and
`(τ₁+σ₁)+(τ₂+σ₂)` are strongly equivalent, with every addition interpreted as `S.sum`. -/
theorem StableSumData.sum_interchange_strong
    (S : StableSumData A B) (hS : S.IsCoherent)
    (tau₁ tau₂ sigma₁ sigma₂ :
      BusbyHom A B) :
    StronglyUnitaryEquivalent
      (S.sum (S.sum tau₁ tau₂) (S.sum sigma₁ sigma₂))
      (S.sum (S.sum tau₁ sigma₁) (S.sum tau₂ sigma₂)) := by
  have h₀ : StronglyUnitaryEquivalent
      (S.sum (S.sum tau₁ tau₂) (S.sum sigma₁ sigma₂))
      (S.sum tau₁ (S.sum tau₂ (S.sum sigma₁ sigma₂))) :=
    hS.1 tau₁ tau₂ (S.sum sigma₁ sigma₂)
  have h₁ : StronglyUnitaryEquivalent
      (S.sum tau₁ (S.sum tau₂ (S.sum sigma₁ sigma₂)))
      (S.sum tau₁ (S.sum (S.sum tau₂ sigma₁) sigma₂)) :=
    S.sum_congr_strong (strongly_unitary_equivalent_refl tau₁)
      (strongly_unitary_equivalent_symm (hS.1 tau₂ sigma₁ sigma₂))
  have h₂ : StronglyUnitaryEquivalent
      (S.sum tau₁ (S.sum (S.sum tau₂ sigma₁) sigma₂))
      (S.sum tau₁ (S.sum (S.sum sigma₁ tau₂) sigma₂)) :=
    S.sum_congr_strong (strongly_unitary_equivalent_refl tau₁)
      (S.sum_congr_strong (hS.2 tau₂ sigma₁)
        (strongly_unitary_equivalent_refl sigma₂))
  have h₃ : StronglyUnitaryEquivalent
      (S.sum tau₁ (S.sum (S.sum sigma₁ tau₂) sigma₂))
      (S.sum tau₁ (S.sum sigma₁ (S.sum tau₂ sigma₂))) :=
    S.sum_congr_strong (strongly_unitary_equivalent_refl tau₁)
      (hS.1 sigma₁ tau₂ sigma₂)
  have h₄ : StronglyUnitaryEquivalent
      (S.sum tau₁ (S.sum sigma₁ (S.sum tau₂ sigma₂)))
      (S.sum (S.sum tau₁ sigma₁) (S.sum tau₂ sigma₂)) :=
    strongly_unitary_equivalent_symm
      (hS.1 tau₁ sigma₁ (S.sum tau₂ sigma₂))
  exact strongly_unitary_equivalent_trans h₀ <|
    strongly_unitary_equivalent_trans h₁ <|
    strongly_unitary_equivalent_trans h₂ <|
    strongly_unitary_equivalent_trans h₃ h₄

/-- **Stable equivalence respects coherent addition.** For coherent `S`, stable equivalence in
each variable implies stable equivalence of the two resulting `S`-sums. -/
theorem StableSumData.sum_congr_stable
    (S : StableSumData A B) (hS : S.IsCoherent)
    {tau₁ tau₁' tau₂ tau₂' :
      BusbyHom A B}
    (h₁ : StablyStrongEquivalent S tau₁ tau₁')
    (h₂ : StablyStrongEquivalent S tau₂ tau₂') :
    StablyStrongEquivalent S (S.sum tau₁ tau₂)
      (S.sum tau₁' tau₂') := by
  obtain ⟨sigma₁, sigma₁', hsigma₁, hsigma₁', hcompare₁⟩ := h₁
  obtain ⟨sigma₂, sigma₂', hsigma₂, hsigma₂', hcompare₂⟩ := h₂
  refine ⟨S.sum sigma₁ sigma₂, S.sum sigma₁' sigma₂',
    S.sum_trivial hsigma₁ hsigma₂,
    S.sum_trivial hsigma₁' hsigma₂', ?_⟩
  have hleft := S.sum_interchange_strong hS tau₁ tau₂ sigma₁ sigma₂
  have hmiddle := S.sum_congr_strong hcompare₁ hcompare₂
  have hright := strongly_unitary_equivalent_symm
    (S.sum_interchange_strong hS tau₁' tau₂' sigma₁' sigma₂')
  exact strongly_unitary_equivalent_trans hleft
    (strongly_unitary_equivalent_trans hmiddle hright)

/-- **Right zero law after stable equivalence.** For coherent `S`, `S.sum τ 0` is stably strongly
equivalent to `τ`. -/
theorem StableSumData.sum_zero_stable
    (S : StableSumData A B) (hS : S.IsCoherent)
    (tau : BusbyHom A B) :
    StablyStrongEquivalent S (S.sum tau 0) tau := by
  refine ⟨0, S.sum 0 0, zero_is_trivial,
    S.sum_trivial zero_is_trivial zero_is_trivial, ?_⟩
  exact hS.1 tau 0 0

/-- **Left zero law after stable equivalence.** For coherent `S`, `S.sum 0 τ` is stably strongly
equivalent to `τ`. -/
theorem StableSumData.zero_sum_stable
    (S : StableSumData A B) (hS : S.IsCoherent)
    (tau : BusbyHom A B) :
    StablyStrongEquivalent S (S.sum 0 tau) tau := by
  refine ⟨0, S.sum 0 0, zero_is_trivial,
    S.sum_trivial zero_is_trivial zero_is_trivial, ?_⟩
  have hswap : StronglyUnitaryEquivalent
      (S.sum (S.sum 0 tau) 0) (S.sum (S.sum tau 0) 0) :=
    S.sum_congr_strong (hS.2 0 tau)
      (strongly_unitary_equivalent_refl
        (0 : BusbyHom A B))
  exact strongly_unitary_equivalent_trans hswap (hS.1 tau 0 0)

/-- **Liftable Busby map is stably zero.** For coherent `S`, a Busby map admitting a multiplier
homomorphism lift is stably strongly equivalent to zero. -/
theorem StableSumData.trivial_stably_strong_equivalent_zero
    (S : StableSumData A B) (hS : S.IsCoherent)
    {sigma : BusbyHom A B}
    (hsigma : IsTrivial sigma) :
    StablyStrongEquivalent S sigma 0 := by
  refine ⟨0, sigma, zero_is_trivial, hsigma, ?_⟩
  exact hS.2 sigma 0

namespace StableClass

/-- **Class of a Busby homomorphism.** `mk S hS τ` is the image of `τ : A → Q(B)` in the quotient
by stable strong equivalence relative to coherent `S`. -/
def mk (S : StableSumData A B) (hS : S.IsCoherent)
    (tau : BusbyHom A B) :
    StableClass S hS :=
  Quotient.mk (S.setoid hS) tau

/-- **Equality of stable Busby classes.** `mk S hS τ₁ = mk S hS τ₂` if and only if
`StablyStrongEquivalent S τ₁ τ₂`. -/
theorem mk_eq_mk_iff (S : StableSumData A B) (hS : S.IsCoherent)
    (tau₁ tau₂ : BusbyHom A B) :
    mk S hS tau₁ = mk S hS tau₂ ↔ StablyStrongEquivalent S tau₁ tau₂ :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **Zero stable class.** The zero of the coherent stable quotient is the class of the zero Busby
map `A → Q(B)`. -/
def zero (S : StableSumData A B) (hS : S.IsCoherent) : StableClass S hS :=
  mk S hS 0

/-- **Addition of stable Busby classes.** The operation on the coherent quotient is determined by
`[τ₁]+[τ₂] = [S.sum τ₁ τ₂]`. -/
def add (S : StableSumData A B) (hS : S.IsCoherent) :
    StableClass S hS → StableClass S hS → StableClass S hS :=
  Quotient.lift₂
    (fun tau₁ tau₂ => mk S hS (S.sum tau₁ tau₂))
    (fun _tau₁ _tau₂ _tau₁' _tau₂' h₁ h₂ =>
      Quotient.sound (S.sum_congr_stable hS h₁ h₂))

@[simp]
theorem add_mk (S : StableSumData A B) (hS : S.IsCoherent)
    (tau₁ tau₂ : BusbyHom A B) :
    add S hS (mk S hS tau₁) (mk S hS tau₂) =
      mk S hS (S.sum tau₁ tau₂) :=
  rfl

end StableClass

/-- **Commutative monoid of stable Busby classes.** For coherent `S`, the stable strong quotient
is a commutative additive monoid, with addition induced by `S.sum` and zero the class `[0]`. -/
noncomputable instance instStableClassAddCommMonoid
    (S : StableSumData A B) (hS : S.IsCoherent) :
    AddCommMonoid (StableClass S hS) where
  zero := StableClass.zero S hS
  add := StableClass.add S hS
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro tau₁
    refine Quotient.inductionOn y ?_
    intro tau₂
    refine Quotient.inductionOn z ?_
    intro tau₃
    change StableClass.mk S hS (S.sum (S.sum tau₁ tau₂) tau₃) =
      StableClass.mk S hS (S.sum tau₁ (S.sum tau₂ tau₃))
    exact Quotient.sound
      (S.stably_strong_equivalent_of_strong (hS.1 tau₁ tau₂ tau₃))
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro tau
    change StableClass.mk S hS (S.sum 0 tau) = StableClass.mk S hS tau
    exact Quotient.sound (S.zero_sum_stable hS tau)
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro tau
    change StableClass.mk S hS (S.sum tau 0) = StableClass.mk S hS tau
    exact Quotient.sound (S.sum_zero_stable hS tau)
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro tau₁ tau₂
    change StableClass.mk S hS (S.sum tau₁ tau₂) =
      StableClass.mk S hS (S.sum tau₂ tau₁)
    exact Quotient.sound
      (S.stably_strong_equivalent_of_strong (hS.2 tau₁ tau₂))
  nsmul :=
    letI : Zero (StableClass S hS) := ⟨StableClass.zero S hS⟩
    letI : Add (StableClass S hS) := ⟨StableClass.add S hS⟩
    nsmulRec
  nsmul_zero := by intro; rfl
  nsmul_succ := by intro n x; rfl

@[simp]
theorem StableClass.mk_add_mk
    (S : StableSumData A B) (hS : S.IsCoherent)
    (tau₁ tau₂ : BusbyHom A B) :
    StableClass.mk S hS tau₁ + StableClass.mk S hS tau₂ =
      StableClass.mk S hS (S.sum tau₁ tau₂) :=
  rfl

@[simp]
theorem StableClass.zero_eq_mk
    (S : StableSumData A B) (hS : S.IsCoherent) :
    (0 : StableClass S hS) = StableClass.mk S hS 0 :=
  rfl

/-- **Zero class of a liftable Busby map.** For coherent `S`, a homomorphism `σ : A → Q(B)`
admitting a multiplier lift satisfies `StableClass.mk S hS σ = 0`. -/
theorem StableClass.mk_eq_zero_of_trivial
    (S : StableSumData A B) (hS : S.IsCoherent)
    {sigma : BusbyHom A B}
    (hsigma : IsTrivial sigma) :
    StableClass.mk S hS sigma = 0 := by
  change StableClass.mk S hS sigma = StableClass.mk S hS 0
  exact Quotient.sound
    (S.trivial_stably_strong_equivalent_zero hS hsigma)

end CStarExtension
