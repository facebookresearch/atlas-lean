/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.StackBundleCones
import MathlibExt.AlgebraicGeometry.AffineNormalConeMaps

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.StackBundleCones

namespace StackBundleConesTest

section AdditiveQuotient

variable {R : Type} [CommRing R] {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {d : M →ₗ[R] N}

/-- Arrows of the quotient groupoid add translations, and the identity translates by zero. -/
example (a : AdditiveQuotient d) : (𝟙 a : a ⟶ a).translation = 0 := rfl

example {a b c : AdditiveQuotient d} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).translation = f.translation + g.translation := rfl

example {a b : AdditiveQuotient d} (f : a ⟶ b) : (inv f).translation = -f.translation := by
  rw [← Groupoid.inv_eq_inv]; rfl

/-- An arrow exists exactly when the values differ by the image of `d`. -/
example (a : AdditiveQuotient d) (m : M) : a ⟶ ⟨a.value + d m⟩ := ⟨m, rfl⟩

example {a b : AdditiveQuotient d} (f : a ⟶ b) : b.value - a.value ∈ LinearMap.range d :=
  ⟨f.translation, by rw [f.relation]; abel⟩

/-- For the zero differential the groupoid is discrete on values. -/
example {a b : AdditiveQuotient (0 : M →ₗ[R] N)} (f : a ⟶ b) : a.value = b.value := by
  rw [f.relation]; simp

end AdditiveQuotient

section ConeHomotheties

variable {A B D : Type} [CommRing A] [CommRing B] [Algebra A B] [CommRing D] [Algebra B D]
  {P : Algebra.Extension.{0} A B}

/-- Scaling by one is the identity homothety. -/
example (a : IntrinsicConePoint P D) : IsScaledConePoint P 1 a a := fun x ↦ by simp

/-- Scaling by zero lands on a zero cone point. -/
example (a b : IntrinsicConePoint P D) (h : IsScaledConePoint P 0 a b) :
    IsZeroConePoint P b := fun x ↦ by simpa using h x

/-- Homotheties compose multiplicatively: scaling by `2` twice is scaling by `4`. -/
example (a b c : IntrinsicConePoint P D) (h₁ : IsScaledConePoint P 2 a b)
    (h₂ : IsScaledConePoint P 2 b c) : IsScaledConePoint P 4 a c := fun x ↦ by
  rw [h₂ x, h₁ x, ← mul_assoc]; norm_num

/-- A zero cone point stays zero under every homothety. -/
example (r : D) (a b : IntrinsicConePoint P D) (ha : IsZeroConePoint P a)
    (h : IsScaledConePoint P r a b) : IsZeroConePoint P b := fun x ↦ by
  rw [h x, ha x, mul_zero]

/-- Change of coefficients acts on cone points by composition. -/
example {C : Type} [CommRing C] [Algebra B C] (φ : D →ₐ[B] C) (a : IntrinsicConePoint P D) :
    ((coneCoefficientFunctor P φ).obj a).map = φ.comp a.map := rfl

/-- Change of coefficients preserves homotheties, with the scalar pushed forward. -/
example {C : Type} [CommRing C] [Algebra B C] (φ : D →ₐ[B] C) (r : D)
    (a b : IntrinsicConePoint P D) (h : IsScaledConePoint P r a b) :
    IsScaledConePoint P (φ r) ((coneCoefficientFunctor P φ).obj a)
      ((coneCoefficientFunctor P φ).obj b) := fun x ↦ by
  change φ (b.map _) = φ r * φ (a.map _)
  rw [h x, map_mul]

end ConeHomotheties

section NormalMaps

open MathlibExt.AlgebraicGeometry.AffineNormalConeMaps

variable {k B : Type} [CommRing k] [CommRing B] [Algebra k B] (P : Algebra.Extension.{0} k B)

/-- The identity square sends every kernel element to itself. -/
example (x : P.ker) : kernelImage P P (RingHom.id _) (RingHom.id _) rfl x = x := rfl

/-- Composing with the identity normal map does not change the underlying ring map. -/
example (F : NormalMap P P (RingHom.id _) (RingHom.id _) rfl) :
    (compose P P P (identity P) F).map = F.map := rfl

example (F : NormalMap P P (RingHom.id _) (RingHom.id _) rfl) :
    (compose P P P F (identity P)).map = F.map := rfl

end NormalMaps

end StackBundleConesTest
