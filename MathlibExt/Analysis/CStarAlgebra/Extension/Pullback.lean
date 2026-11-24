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
# Literal precomposition of normalized Busby extensions

Precomposition produces an actual Busby map and its normalized closed pullback.
The comparison to the original normalized Busby pullback is the literal pair
map `(a,T) ↦ (f a,T)`. Its ideal and quotient squares are derived, not supplied.
There is no operation on stable extension classes or arbitrary extension model.
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

/-- Normalize the literal precomposed Busby invariant. -/
def pullback : CStarExtension.{uA₁, uB, max uA₁ uB} A₁ B :=
  ofBusby (τ.comp f)

@[simp]
theorem pullback_busby : (pullback f τ).busby = τ.comp f :=
  ofBusby_busby (τ.comp f)

/-- The middle algebra is exactly the closed pullback of the precomposed map. -/
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

/-- The literal middle-algebra comparison applies `f` only to the first coordinate. -/
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

/-- The actual pair formula, including the unchanged multiplier coordinate. -/
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

/-- The pair comparison is a normalized extension morphism with identity ideal map. -/
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
