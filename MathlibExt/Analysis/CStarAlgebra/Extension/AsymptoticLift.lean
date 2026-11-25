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
# Exact asymptotic lifts of Busby maps

For nonunital C-star algebras `A,B`, an exact asymptotic lift of `τ : A → Q(B)` is an asymptotic
morphism `ρ : A → M(B)` satisfying `q(ρ_t(a)) = τ(a)` for every `a` and every time `t ∈ [1,∞)`.
Its time orbits are continuous and its additive, scalar, multiplicative and star defects tend to
zero; individual time slices may be nonlinear.

Homomorphism lifts give constant asymptotic lifts. Precomposition by a star homomorphism,
continuous cofinal reparameterization, coefficient equivalence and multiplier-unitary
conjugation preserve exact lifting. This is the asymptotic splitting in Manuilov--Thomsen, The
Connes--Higson construction is an isomorphism, arXiv:math/0004181v3, Section 2.
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

/-- **Exact asymptotic lift of a Busby map.** For nonunital C-star algebras `A,B` and `τ : A →
Q(B)`, this record contains an asymptotic morphism `ρ : A → M(B)` with `q(ρ_t(a)) = τ(a)` for
every `t ∈ [1,∞)` and `a : A`. -/
structure ExactAsymptoticLift (tau : BusbyHom A B) where
  /-- **Multiplier-valued asymptotic family.** The lift family has continuous time orbits and
  additive, scalar, multiplicative and star defects tending to zero at infinity; its
  finite-time slices may be nonlinear. -/
  family : AsymptoticMorphism A 𝓜(ℂ, B)
  /-- **Exact quotient identity of the lift.** `outerQuotientMap (family t a) = tau a` holds at
  every time and for every coefficient, including time `1`. -/
  quotient_eq : ∀ (t : AsymptoticTime) (a : A), outerQuotientMap (family t a) = tau a

/-- **Asymptotic splitting of a Busby map.** A Busby homomorphism is asymptotically split when it
admits an exact multiplier-valued asymptotic lift `ρ` with `q(ρ_t(a)) = τ(a)` at all times. -/
def IsAsymptoticallySplit (tau : BusbyHom A B) : Prop := Nonempty (ExactAsymptoticLift tau)

/-- **Existence criterion for asymptotic splitting.** `IsAsymptoticallySplit tau` is equivalent to
existence of `phi : AsymptoticMorphism A M(B)` satisfying `q(phi t a) = tau a` for every `t ∈
[1,∞)` and `a : A`. -/
theorem isAsymptoticallySplit_iff (tau : BusbyHom A B) :
    IsAsymptoticallySplit tau ↔ ∃ phi : AsymptoticMorphism A 𝓜(ℂ, B),
      ∀ (t : AsymptoticTime) (a : A), outerQuotientMap (phi t a) = tau a := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.family, L.quotient_eq⟩
  · rintro ⟨phi, hphi⟩
    exact ⟨⟨phi, hphi⟩⟩

namespace ExactAsymptoticLift

/-- **Extensionality of exact asymptotic lifts.** Two exact lifts of the same Busby map are equal
when their multiplier-valued asymptotic families are equal. -/
@[ext]
theorem ext {tau : BusbyHom A B} {L K : ExactAsymptoticLift tau}
    (h : L.family = K.family) : L = K := by
  cases L
  cases K
  cases h
  rfl

/-- **Constant lift from a multiplier homomorphism.** A star homomorphism `ρ : A → M(B)` gives the
constant exact asymptotic lift `ρ_t(a) = ρ(a)` of `q ∘ ρ`. -/
def ofHom (rho : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) :
    ExactAsymptoticLift ((outerQuotientMap (A := B)).toNonUnitalStarAlgHom.comp rho) where
  family := AsymptoticMorphism.ofHom rho
  quotient_eq _ _ := rfl

/-- **Zero exact asymptotic lift.** The family `ρ_t(a) = 0` is an exact lift of the zero Busby
map. -/
def zero : ExactAsymptoticLift (0 : BusbyHom A B) where
  family := AsymptoticMorphism.zero
  quotient_eq t a := by simp

/-- **Precomposition of an exact asymptotic lift.** For an exact lift `ρ` of `τ` and a star
homomorphism `f : C → A`, the family `ρ_t(f a)` lifts `τ.comp f` exactly at every time. -/
def precomp {tau : BusbyHom A B} (L : ExactAsymptoticLift tau) (f : C →⋆ₙₐ[ℂ] A) :
    ExactAsymptoticLift (tau.comp f) where
  family := AsymptoticMorphism.precomp L.family f
  quotient_eq t a := L.quotient_eq t (f a)

/-- **Cofinal reparameterization of an exact lift.** If `r : [1,∞) → [1,∞)` is continuous and
tends to infinity along `atTop`, then `ρ_(r(t))(a)` is an exact asymptotic lift of the same
Busby map. -/
def reparam {tau : BusbyHom A B} (L : ExactAsymptoticLift tau)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Filter.Tendsto r Filter.atTop Filter.atTop) : ExactAsymptoticLift tau where
  family := AsymptoticMorphism.reparam L.family r hr hrTop
  quotient_eq t a := L.quotient_eq (r t) a

/-- **Transport of an exact lift across coefficient equivalence.** A star-algebra equivalence `e :
B ≃ C` transports `ρ_t` through the multiplier equivalence and transports its Busby map
through the corresponding corona equivalence. -/
def coefficientEquiv {tau : BusbyHom A B} (L : ExactAsymptoticLift tau) (e : B ≃⋆ₐ[ℂ] C) :
    ExactAsymptoticLift ((DoubleCentralizer.outerCongr e).toNonUnitalStarAlgHom.comp tau) where
  family := AsymptoticMorphism.postcomp L.family (DoubleCentralizer.congr e).toNonUnitalStarAlgHom
  quotient_eq t a := by
    change outerQuotientMap (DoubleCentralizer.congr e (L.family t a)) =
      DoubleCentralizer.outerCongr e (tau a)
    rw [← DoubleCentralizer.outerCongr_outerQuotientMap, L.quotient_eq]

end ExactAsymptoticLift

/-- **Splitting implies asymptotic splitting.** A Busby map that lifts to a star homomorphism into
`M(B)` is asymptotically split, using the constant lift. -/
theorem IsTrivial.isAsymptoticallySplit {tau : BusbyHom A B} (h : IsTrivial tau) :
    IsAsymptoticallySplit tau := by
  obtain ⟨rho, hrho⟩ := h
  rw [← hrho]
  exact ⟨ExactAsymptoticLift.ofHom rho⟩

/-- **Asymptotic splitting of the zero Busby map.** The zero map `A → Q(B)` is asymptotically
split by the zero multiplier-valued family. -/
theorem zero_isAsymptoticallySplit : IsAsymptoticallySplit (0 : BusbyHom A B) :=
  ⟨ExactAsymptoticLift.zero⟩

/-- **Unitary invariance of asymptotic splitting.** If `τ₂(a) = q(u) τ₁(a) q(u)*` for one
multiplier unitary `u` and `τ₁` is asymptotically split, conjugating its lift by `u` gives an
exact lift of `τ₂`. -/
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

/-- **Asymptotic splitting of strongly equivalent Busby maps.** Strong multiplier-unitary
equivalence `τ₁ ∼ τ₂` implies `IsAsymptoticallySplit τ₁ ↔ IsAsymptoticallySplit τ₂`. -/
theorem isAsymptoticallySplit_iff_of_stronglyUnitaryEquivalent
    {tau₁ tau₂ : BusbyHom A B} (h : StronglyUnitaryEquivalent tau₁ tau₂) :
    IsAsymptoticallySplit tau₁ ↔ IsAsymptoticallySplit tau₂ :=
  ⟨h.isAsymptoticallySplit, (strongly_unitary_equivalent_symm h).isAsymptoticallySplit⟩

end CStarExtension
