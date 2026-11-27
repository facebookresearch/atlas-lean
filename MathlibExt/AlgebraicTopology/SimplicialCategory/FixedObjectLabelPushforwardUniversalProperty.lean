/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardInterpretation

/-! # The actual universal property of arbitrary-label enriched pushforward

Whole fixed-object maps from the presented target are determined by every
original source Hom generator. Extending and restricting preserve those
same generators in both directions, with no label-injectivity hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward

variable {A O : Type u} (a : A → O) (C : FixedObjects A)
variable {D : FixedObjects O}

/-- Every whole extension retaining the original source functor is the actual presented
extension. -/
theorem desc_unique (F : C ⟶ LabelRestriction.object a D) (G : object a C ⟶ D)
    (h : unit a C ≫ LabelRestriction.map a G = F) : G = desc a C F := by
  apply Presentations.generators_ext (quiver a C) (relations a C)
  intro x y
  rw [generator_desc]
  ext q g
  rcases g with ⟨s, t, hs, ht, c⟩
  cases hs
  cases ht
  have hh := congrArg (fun k : C ⟶ LabelRestriction.object a D => homMap k s t) h
  rw [homMap_comp, homMap_unit, LabelRestriction.homMap_map] at hh
  exact congrArg (fun k => k.app q c) hh

/-- Restricting an actual whole target map and extending it recovers that same target map. -/
theorem desc_unit (G : object a C ⟶ D) :
    desc a C (unit a C ≫ LabelRestriction.map a G) = G :=
  (desc_unique a C _ G rfl).symm

/-- The native whole-Hom bijection for arbitrary-label pushforward and restriction. -/
def homEquiv (D : FixedObjects O) :
    (object a C ⟶ D) ≃ (C ⟶ LabelRestriction.object a D) where
  toFun G := unit a C ≫ LabelRestriction.map a G
  invFun F := desc a C F
  left_inv := desc_unit a C
  right_inv := unit_desc a C

/-- The forward bijection retains the actual original whole unit followed by restriction. -/
@[simp]
theorem homEquiv_apply (D : FixedObjects O) (G : object a C ⟶ D) :
    homEquiv a C D G = unit a C ≫ LabelRestriction.map a G := rfl

/-- The inverse bijection is the actual relation-respecting whole presented extension. -/
@[simp]
theorem homEquiv_symm_apply (D : FixedObjects O) (F : C ⟶ LabelRestriction.object a D) :
    (homEquiv a C D).symm F = desc a C F := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
