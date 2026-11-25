/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.MappedFactorArrows
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.EquivalenceComposition
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.RoundtripData

/-!
# Entire original factor Arrow functors and equivalence comparisons

The supplied functorial factorization gives both actual factor functors on
every Arrow and every commutative square. Its given equivalence counit gives
whole natural comparisons, retaining both factor endpoint maps and inverses.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty C}

/-- The complete original first factor on every Arrow and every square. -/
def originalLeftFactorFunctor (data : FunctorialFactorizationData W₁ W₂) :
    Arrow C ⥤ Arrow C where
  obj a := Arrow.mk (data.i.app a)
  map φ := Arrow.homMk φ.left (data.Z.map φ) (data.i.naturality φ)
  map_id a := by
    apply Arrow.hom_ext
    · rfl
    · exact data.Z.map_id a
  map_comp φ ψ := by
    apply Arrow.hom_ext
    · rfl
    · exact data.Z.map_comp φ ψ

/-- The complete original second factor on every Arrow and every square. -/
def originalRightFactorFunctor (data : FunctorialFactorizationData W₁ W₂) :
    Arrow C ⥤ Arrow C where
  obj a := Arrow.mk (data.p.app a)
  map φ := Arrow.homMk (data.Z.map φ) φ.right (data.p.naturality φ)
  map_id a := by
    apply Arrow.hom_ext
    · exact data.Z.map_id a
    · rfl
  map_comp φ ψ := by
    apply Arrow.hom_ext
    · exact data.Z.map_comp φ ψ
    · rfl

/-- Both complete first-factor square maps are the original supplied components. -/
theorem originalLeftFactorFunctor_map_fields
    (data : FunctorialFactorizationData W₁ W₂) {a b : Arrow C} (φ : a ⟶ b) :
    (data.originalLeftFactorFunctor.map φ).left = φ.left ∧
      (data.originalLeftFactorFunctor.map φ).right = data.Z.map φ := ⟨rfl, rfl⟩

/-- Both complete second-factor square maps are the original supplied components. -/
theorem originalRightFactorFunctor_map_fields
    (data : FunctorialFactorizationData W₁ W₂) {a b : Arrow C} (φ : a ⟶ b) :
    (data.originalRightFactorFunctor.map φ).left = data.Z.map φ ∧
      (data.originalRightFactorFunctor.map φ).right = φ.right := ⟨rfl, rfl⟩

section Equivalence

variable {V₁ V₂ : MorphismProperty D} [V₁.RespectsIso] [V₂.RespectsIso]

/-- The entire first-factor functor is compared through the given original middle counit. -/
def originalLeftFactorEquivalenceIso (data : FunctorialFactorizationData V₁ V₂)
    (e : C ≌ D) :
    (data.ofEquivalence e).originalLeftFactorFunctor ⋙ e.functor.mapArrow ≅
      e.functor.mapArrow ⋙ data.originalLeftFactorFunctor :=
  NatIso.ofComponents (fun a => data.ofEquivalenceLeftArrowIso e a) (by
    intro a b φ
    apply Arrow.hom_ext
    · change e.functor.map φ.left ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map φ.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (data.ofEquivalenceZComparisonIso e).hom.naturality φ)

/-- The entire second-factor functor retains the same counit on every square. -/
def originalRightFactorEquivalenceIso (data : FunctorialFactorizationData V₁ V₂)
    (e : C ≌ D) :
    (data.ofEquivalence e).originalRightFactorFunctor ⋙ e.functor.mapArrow ≅
      e.functor.mapArrow ⋙ data.originalRightFactorFunctor :=
  NatIso.ofComponents (fun a => data.ofEquivalenceRightArrowIso e a) (by
    intro a b φ
    apply Arrow.hom_ext
    · exact (data.ofEquivalenceZComparisonIso e).hom.naturality φ
    · change e.functor.map φ.right ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map φ.right
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The whole first-factor comparison keeps the caller identity and middle counit. -/
theorem originalLeftFactorEquivalenceIso_hom_fields
    (data : FunctorialFactorizationData V₁ V₂) (e : C ≌ D) (a : Arrow C) :
    (data.originalLeftFactorEquivalenceIso e).hom.app a =
      Arrow.homMk (𝟙 (e.functor.obj a.left))
        ((data.ofEquivalenceZComparisonIso e).hom.app a)
        ((Category.id_comp _).trans (data.ofEquivalence_mapped_i e a).symm) := rfl

/-- The whole second-factor comparison keeps the middle counit and caller identity. -/
theorem originalRightFactorEquivalenceIso_hom_fields
    (data : FunctorialFactorizationData V₁ V₂) (e : C ≌ D) (a : Arrow C) :
    ((data.originalRightFactorEquivalenceIso e).hom.app a).left =
        (data.ofEquivalenceZComparisonIso e).hom.app a ∧
      ((data.originalRightFactorEquivalenceIso e).hom.app a).right =
        𝟙 (e.functor.obj a.right) := ⟨rfl, rfl⟩

end Equivalence
end CategoryTheory.MorphismProperty.FunctorialFactorizationData
