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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Functoriality
public import MathlibExt.Analysis.CStarAlgebra.Extension.BusbyRelations
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Exact asymptotic lifts through the multiplier quotient

Manuilov--Thomsen, The Connes--Higson construction is an isomorphism,
arXiv:math/0004181v3, §2, calls a Busby map asymptotically split when it has
an asymptotic morphism into the actual multiplier algebra with the exact
quotient identity at every time in [1,∞).

Individual slices remain arbitrary nonlinear functions. No finite-time
linearity, coefficient continuity, stable sum, extension group or inverse
construction is imposed. Ordinary split maps give constant examples; the
existing ordinary `IsTrivial` relation is preserved.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped CStarAlgebra MultiplierAlgebra

noncomputable section
namespace CStarExtension

universe uA uB uC
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
attribute [local instance] CStarExtension.outerCStarAlgebra

/-- An actual nonlinear asymptotic family lifting the fixed Busby map exactly
at every time, including the initial time one. -/
structure ExactAsymptoticLift (tau : BusbyHom A B) where
  /-- The existing arbitrary-slice family with its genuine time topology and defects. -/
  family : AsymptoticMorphism A 𝓜(ℂ, B)
  /-- The identity is exact for every coefficient at every time, rather than a norm limit. -/
  quotient_eq : ∀ (t : AsymptoticTime) (a : A), outerQuotientMap (family t a) = tau a

/-- The source asymptotically split property, separate from an ordinary hom lift. -/
def IsAsymptoticallySplit (tau : BusbyHom A B) : Prop := Nonempty (ExactAsymptoticLift tau)

/-- The defining source quantifiers, with the actual multiplier quotient. -/
theorem isAsymptoticallySplit_iff (tau : BusbyHom A B) :
    IsAsymptoticallySplit tau ↔ ∃ phi : AsymptoticMorphism A 𝓜(ℂ, B),
      ∀ (t : AsymptoticTime) (a : A), outerQuotientMap (phi t a) = tau a := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.family, L.quotient_eq⟩
  · rintro ⟨phi, hphi⟩
    exact ⟨⟨phi, hphi⟩⟩

namespace ExactAsymptoticLift

/-- The family determines a lift; its remaining field is a proof. -/
@[ext]
theorem ext {tau : BusbyHom A B} {L K : ExactAsymptoticLift tau}
    (h : L.family = K.family) : L = K := by
  cases L
  cases K
  cases h
  rfl

/-- A genuine multiplier-valued homomorphism gives its constant exact lift. -/
def ofHom (rho : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) :
    ExactAsymptoticLift ((outerQuotientMap (A := B)).toNonUnitalStarAlgHom.comp rho) where
  family := AsymptoticMorphism.ofHom rho
  quotient_eq _ _ := rfl

/-- The literal zero family lifts the zero Busby homomorphism. -/
def zero : ExactAsymptoticLift (0 : BusbyHom A B) where
  family := AsymptoticMorphism.zero
  quotient_eq t a := by simp

/-- Pullback by a true coefficient homomorphism preserves every exact time identity. -/
def precomp {tau : BusbyHom A B} (L : ExactAsymptoticLift tau) (f : C →⋆ₙₐ[ℂ] A) :
    ExactAsymptoticLift (tau.comp f) where
  family := AsymptoticMorphism.precomp L.family f
  quotient_eq t a := L.quotient_eq t (f a)

/-- Continuous cofinal changes of the genuine half-line time preserve exactness. -/
def reparam {tau : BusbyHom A B} (L : ExactAsymptoticLift tau)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Filter.Tendsto r Filter.atTop Filter.atTop) : ExactAsymptoticLift tau where
  family := AsymptoticMorphism.reparam L.family r hr hrTop
  quotient_eq t a := L.quotient_eq (r t) a

/-- Canonical multiplier and corona transport through a coefficient equivalence. -/
def coefficientEquiv {tau : BusbyHom A B} (L : ExactAsymptoticLift tau) (e : B ≃⋆ₐ[ℂ] C) :
    ExactAsymptoticLift ((DoubleCentralizer.outerCongr e).toNonUnitalStarAlgHom.comp tau) where
  family := AsymptoticMorphism.postcomp L.family (DoubleCentralizer.congr e).toNonUnitalStarAlgHom
  quotient_eq t a := by
    change outerQuotientMap (DoubleCentralizer.congr e (L.family t a)) =
      DoubleCentralizer.outerCongr e (tau a)
    rw [← DoubleCentralizer.outerCongr_outerQuotientMap, L.quotient_eq]

end ExactAsymptoticLift

/-- Every ordinary split lift is an example of an asymptotic splitting. -/
theorem IsTrivial.isAsymptoticallySplit {tau : BusbyHom A B} (h : IsTrivial tau) :
    IsAsymptoticallySplit tau := by
  obtain ⟨rho, hrho⟩ := h
  rw [← hrho]
  exact ⟨ExactAsymptoticLift.ofHom rho⟩

/-- The zero extension has the exact zero asymptotic lift. -/
theorem zero_isAsymptoticallySplit : IsAsymptoticallySplit (0 : BusbyHom A B) :=
  ⟨ExactAsymptoticLift.zero⟩

/-- Conjugating by an actual multiplier unitary preserves the exact lift.
The family is postcomposed only by the genuine inner star automorphism. -/
theorem StronglyUnitaryEquivalent.isAsymptoticallySplit
    {tau₁ tau₂ : BusbyHom A B} (h : StronglyUnitaryEquivalent tau₁ tau₂)
    (h₁ : IsAsymptoticallySplit tau₁) : IsAsymptoticallySplit tau₂ := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨L⟩ := h₁
  refine ⟨{
    family := AsymptoticMorphism.postcomp L.family
      (Unitary.conjStarAlgAut ℂ (𝓜(ℂ, B)) u).toNonUnitalStarAlgHom
    quotient_eq := ?_ }⟩
  intro t a
  change outerQuotientMap ((u : 𝓜(ℂ, B)) * L.family t a * star (u : 𝓜(ℂ, B))) = tau₂ a
  rw [map_mul, map_mul, map_star, L.quotient_eq]
  exact (hu a).symm

/-- Strong multiplier-unitary equivalence preserves the source splitting property in both directions. -/
theorem isAsymptoticallySplit_iff_of_stronglyUnitaryEquivalent
    {tau₁ tau₂ : BusbyHom A B} (h : StronglyUnitaryEquivalent tau₁ tau₂) :
    IsAsymptoticallySplit tau₁ ↔ IsAsymptoticallySplit tau₂ :=
  ⟨h.isAsymptoticallySplit, (strongly_unitary_equivalent_symm h).isAsymptoticallySplit⟩

end CStarExtension
