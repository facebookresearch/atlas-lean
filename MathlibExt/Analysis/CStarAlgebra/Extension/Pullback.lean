/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Extension.Busby

/-!
# Pullback of a Busby extension along a homomorphism

Let `f : A₁ → A₂` be a complex nonunital star homomorphism and `τ : A₂ → Q(B)` a Busby map of
nonunital C-star algebras. Precomposition gives `τ ∘ f`, with pullback middle algebra `{(a,m) ∈
A₁ × M(B) | τ(f a) = q(m)}`.

The map `(a,m) ↦ (f a,m)` sends this algebra to the pullback of `τ`. It gives an extension
morphism with the identity map on `B` and `f` on the quotient, preserving both inclusion and
quotient squares.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped CStarAlgebra MultiplierAlgebra

namespace CStarExtension

universe uA₁ uA₂ uB

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {B : Type uB}
variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
variable [NonUnitalCStarAlgebra B]
attribute [local instance] outerMultiplierCStarAlgebra

variable (f : A₁ →⋆ₙₐ[ℂ] A₂) (τ : BusbyMap (A := A₂) (B := B))

/-- **Extension of a precomposed Busby map.** Let `A₁,A₂,B` be nonunital C-star algebras and let
`f : A₁ → A₂` and `τ : A₂ → Q(B)` be complex nonunital star-algebra homomorphisms, where `Q(B)
= M(B)/B`. This is the closed pullback extension defined by `τ.comp f`. -/
def pullback : CStarExtension.{uA₁, uB, max uA₁ uB} A₁ B :=
  ofBusby (τ.comp f)

@[simp]
theorem pullback_busby : (pullback f τ).busby = τ.comp f :=
  ofBusby_busby (τ.comp f)

/-- **Middle algebra of the precomposed extension.** `(pullback f τ).Middle = BusbyPullback
(τ.comp f)`, the closed algebra of pairs satisfying `τ(f a) = q(m)`. -/
theorem pullback_middle :
    (pullback f τ).Middle = (BusbyPullback (τ.comp f) : Type (max uA₁ uB)) := rfl

@[simp]
theorem pullback_inclusion (b : B) :
    (pullback f τ).inclusion b = pullbackInclusion (τ.comp f) b :=
  ofBusby_inclusion (τ.comp f) b

@[simp]
theorem pullback_quotient (p : BusbyPullback (τ.comp f)) :
    (pullback f τ).quotient p = pullbackQuotient (τ.comp f) p :=
  ofBusby_quotient (τ.comp f) p

/-- **Comparison of Busby pullback algebras.** The star homomorphism from the pullback of `τ ∘ f`
to that of `τ` sends `(a,m)` to `(f a,m)`. -/
def pullbackMiddleMap : BusbyPullback (τ.comp f) →⋆ₙₐ[ℂ] BusbyPullback τ := by
  apply NonUnitalCStarPullback.lift τ
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
    (f.comp (pullbackQuotient (τ.comp f)))
    (NonUnitalCStarPullback.sndHom (τ.comp f)
      (outerQuotientMap (A := B)).toNonUnitalStarAlgHom)
  apply NonUnitalStarAlgHom.ext
  intro p
  exact NonUnitalCStarPullback.condition (τ.comp f)
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom p

@[simp]
theorem pullbackMiddleMap_fst (p : BusbyPullback (τ.comp f)) :
    NonUnitalCStarPullback.fst τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom (pullbackMiddleMap f τ p) =
      f (pullbackQuotient (τ.comp f) p) := rfl

@[simp]
theorem pullbackMiddleMap_snd (p : BusbyPullback (τ.comp f)) :
    NonUnitalCStarPullback.snd τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom (pullbackMiddleMap f τ p) =
      NonUnitalCStarPullback.snd (τ.comp f)
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom p := rfl

/-- **Pair formula for pullback comparison.** Under the product embeddings, `pullbackMiddleMap f τ
p = (f p.1.1, p.1.2)`; the multiplier coordinate is unchanged. -/
theorem pullbackMiddleMap_coe (p : BusbyPullback (τ.comp f)) :
    ((pullbackMiddleMap f τ p : BusbyPullback τ) : A₂ × 𝓜(ℂ, B)) =
      (f p.1.1, p.1.2) := rfl

theorem pullbackMiddleMap_inclusion (b : B) :
    pullbackMiddleMap f τ ((pullback f τ).inclusion b) = (ofBusby τ).inclusion b := by
  rw [pullback_inclusion, ofBusby_inclusion]
  apply NonUnitalCStarPullback.ext τ
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
  · rw [pullbackMiddleMap_fst, pullbackInclusion_fst]
    change f 0 = 0
    exact map_zero f
  · rw [pullbackMiddleMap_snd, pullbackInclusion_snd, pullbackInclusion_snd]

theorem pullbackMiddleMap_quotient (p : BusbyPullback (τ.comp f)) :
    (ofBusby τ).quotient (pullbackMiddleMap f τ p) = f ((pullback f τ).quotient p) := by
  rw [ofBusby_quotient, pullback_quotient]
  exact pullbackMiddleMap_fst f τ p

/-- **Morphism of pullback extensions.** The middle map `(a,m) ↦ (f a,m)` defines a morphism from
`pullback f τ` to `ofBusby τ`, with ideal map `id_B` and quotient map `f`. -/
def pullbackHom : Hom (pullback f τ) (ofBusby τ) where
  idealMap := NonUnitalStarAlgHom.id ℂ B
  middleMap := pullbackMiddleMap f τ
  quotientMap := f
  inclusion_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro b
    exact pullbackMiddleMap_inclusion f τ b
  quotient_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro p
    exact pullbackMiddleMap_quotient f τ p

@[simp]
theorem pullbackHom_idealMap : (pullbackHom f τ).idealMap = NonUnitalStarAlgHom.id ℂ B := rfl

@[simp]
theorem pullbackHom_middleMap : (pullbackHom f τ).middleMap = pullbackMiddleMap f τ := rfl

@[simp]
theorem pullbackHom_quotientMap : (pullbackHom f τ).quotientMap = f := rfl

end CStarExtension
