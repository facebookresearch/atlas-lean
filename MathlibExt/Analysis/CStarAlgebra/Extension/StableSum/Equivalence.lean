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


public import MathlibExt.Analysis.CStarAlgebra.Extension.StableSum.Calculus

/-!
# Equivalence relation of stable Busby sums

Fix compatible multiplier and corona folds `S` with associativity and commutativity up to strong
unitary equivalence. The relation that makes `τ₁,τ₂` equivalent after adjoining liftable Busby
maps is reflexive, symmetric and transitive.

Reflexivity uses the zero liftable map. Transitivity combines the strict unitary-conjugation
calculus with sum congruence and the fact that the sum of two liftable maps is liftable. The
domain is an algebraic semiring with complex scalar action and additive involution; completeness
is not imposed on that domain.
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

private theorem stably_strong_equivalent_refl (S : StableSumData A B)
    (tau : BusbyHom A B) :
    StablyStrongEquivalent S tau tau := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  refine ⟨0, 0, zero_is_trivial, zero_is_trivial, ?_⟩
  exact strongly_unitary_equivalent_refl (S.sum tau 0)

private theorem stably_strong_equivalent_symm (S : StableSumData A B)
    {tau₁ tau₂ : BusbyHom A B}
    (h : StablyStrongEquivalent S tau₁ tau₂) :
    StablyStrongEquivalent S tau₂ tau₁ := by
  obtain ⟨sigma₁, sigma₂, hsigma₁, hsigma₂, hcompare⟩ := h
  exact ⟨sigma₂, sigma₁, hsigma₂, hsigma₁,
    strongly_unitary_equivalent_symm hcompare⟩

private theorem stably_strong_equivalent_trans (S : StableSumData A B)
    (hS : S.IsCoherent)
    {tau₁ tau₂ tau₃ : BusbyHom A B}
    (h₁₂ : StablyStrongEquivalent S tau₁ tau₂)
    (h₂₃ : StablyStrongEquivalent S tau₂ tau₃) :
    StablyStrongEquivalent S tau₁ tau₃ := by
  obtain ⟨sigma₁, sigma₂, hsigma₁, hsigma₂, hcompare₁₂⟩ := h₁₂
  obtain ⟨sigma₃, sigma₄, hsigma₃, hsigma₄, hcompare₂₃⟩ := h₂₃
  have htrivialLeft : IsTrivial (S.sum sigma₁ sigma₃) :=
    S.sum_trivial hsigma₁ hsigma₃
  have htrivialRight : IsTrivial (S.sum sigma₄ sigma₂) :=
    S.sum_trivial hsigma₄ hsigma₂
  have hstep₀ : StronglyUnitaryEquivalent
      (S.sum tau₁ (S.sum sigma₁ sigma₃))
      (S.sum (S.sum tau₁ sigma₁) sigma₃) :=
    strongly_unitary_equivalent_symm (hS.1 tau₁ sigma₁ sigma₃)
  have hstep₁ : StronglyUnitaryEquivalent
      (S.sum (S.sum tau₁ sigma₁) sigma₃)
      (S.sum (S.sum tau₂ sigma₂) sigma₃) :=
    S.sum_congr_strong hcompare₁₂
      (strongly_unitary_equivalent_refl sigma₃)
  have hstep₂ : StronglyUnitaryEquivalent
      (S.sum (S.sum tau₂ sigma₂) sigma₃)
      (S.sum tau₂ (S.sum sigma₂ sigma₃)) :=
    hS.1 tau₂ sigma₂ sigma₃
  have hstep₃ : StronglyUnitaryEquivalent
      (S.sum tau₂ (S.sum sigma₂ sigma₃))
      (S.sum tau₂ (S.sum sigma₃ sigma₂)) :=
    S.sum_congr_strong (strongly_unitary_equivalent_refl tau₂)
      (hS.2 sigma₂ sigma₃)
  have hstep₄ : StronglyUnitaryEquivalent
      (S.sum tau₂ (S.sum sigma₃ sigma₂))
      (S.sum (S.sum tau₂ sigma₃) sigma₂) :=
    strongly_unitary_equivalent_symm (hS.1 tau₂ sigma₃ sigma₂)
  have hstep₅ : StronglyUnitaryEquivalent
      (S.sum (S.sum tau₂ sigma₃) sigma₂)
      (S.sum (S.sum tau₃ sigma₄) sigma₂) :=
    S.sum_congr_strong hcompare₂₃
      (strongly_unitary_equivalent_refl sigma₂)
  have hstep₆ : StronglyUnitaryEquivalent
      (S.sum (S.sum tau₃ sigma₄) sigma₂)
      (S.sum tau₃ (S.sum sigma₄ sigma₂)) :=
    hS.1 tau₃ sigma₄ sigma₂
  refine ⟨S.sum sigma₁ sigma₃, S.sum sigma₄ sigma₂,
    htrivialLeft, htrivialRight, ?_⟩
  exact strongly_unitary_equivalent_trans hstep₀ <|
    strongly_unitary_equivalent_trans hstep₁ <|
    strongly_unitary_equivalent_trans hstep₂ <|
    strongly_unitary_equivalent_trans hstep₃ <|
    strongly_unitary_equivalent_trans hstep₄ <|
    strongly_unitary_equivalent_trans hstep₅ hstep₆

/-- **Equivalence relation of stable strong Busby sums.** If `S.IsCoherent`, then
`StablyStrongEquivalent S` is reflexive, symmetric and transitive on the Busby homomorphisms
`A → Q(B)`. -/
theorem stably_strong_equivalent_equivalence (S : StableSumData A B)
    (hS : S.IsCoherent) :
    _root_.Equivalence (StablyStrongEquivalent S) := by
  constructor
  · exact stably_strong_equivalent_refl S
  · intro tau₁ tau₂ h
    exact stably_strong_equivalent_symm S h
  · intro tau₁ tau₂ tau₃ h₁₂ h₂₃
    exact stably_strong_equivalent_trans S hS h₁₂ h₂₃

end CStarExtension
