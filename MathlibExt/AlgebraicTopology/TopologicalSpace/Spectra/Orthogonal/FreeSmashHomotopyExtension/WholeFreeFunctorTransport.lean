/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.RightModuleFreeEvaluation

/-!
# Free right modules under monoidal data equality

Equality of two monoidal structures and heterogeneous equality of their
monoid structures transport the corresponding free right-module functors.
After precomposition by any functor, the resulting composites remain
heterogeneously equal.
-/

set_option autoImplicit false
noncomputable section
universe uA vA uC vC
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.WholeFreeTransport

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {A : Type uA} [Category.{vA} A] {C : Type uC} [Category.{vC} C]

/-- Equality of the entire chosen tensor and monoid transports the whole original free functor. -/
theorem functor_heq (m₀ m₁ : MonoidalCategory C) (hm : m₀ = m₁) (S : C)
    (s₀ : letI := m₀; MonObj S) (s₁ : letI := m₁; MonObj S)
    (hs : HEq s₀ s₁) (F : A ⥤ C) :
    HEq (letI := m₀; letI := s₀; F ⋙ RightModuleFree.functor S)
      (letI := m₁; letI := s₁; F ⋙ RightModuleFree.functor S) := by
  cases hm
  cases eq_of_heq hs
  rfl



end OrthogonalIGeneratorProbe.WholeFreeTransport
