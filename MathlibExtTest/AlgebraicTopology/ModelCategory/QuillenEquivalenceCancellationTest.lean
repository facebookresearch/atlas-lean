/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory HomotopicalAlgebra

namespace MathlibExtTest.QuillenEquivalenceCancellation

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
  (adj : L ⊣ R) (adj' : L' ⊣ R')
  [adj.IsQuillenEquivalence] [adj'.IsQuillenAdjunction]
  [(adj.comp adj').IsQuillenEquivalence]

example : adj'.IsQuillenEquivalence :=
  Adjunction.IsQuillenEquivalence.cancel_left adj adj'

example {X : D} {Y : E} [IsCofibrant X] [IsFibrant Y] (f : L'.obj X ⟶ Y) :
    weakEquivalences E f ↔ weakEquivalences D (adj'.homEquiv X Y f) := by
  let _ : adj'.IsQuillenEquivalence := Adjunction.IsQuillenEquivalence.cancel_left adj adj'
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff (adj := adj') f

example {X : D} {Y : E} [IsCofibrant X] [IsFibrant Y] (f : L'.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj'.homEquiv X Y f) := by
  let _ : adj'.IsQuillenEquivalence := Adjunction.IsQuillenEquivalence.cancel_left adj adj'
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj') f

end MathlibExtTest.QuillenEquivalenceCancellation
