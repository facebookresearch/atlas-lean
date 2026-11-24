/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCriterion

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u v u' v'

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenAdjunction]
  (hcrit : ∀ (X : C) (Y : D) [IsCofibrant X] [IsFibrant X] [IsFibrant Y]
    (f : L.obj X ⟶ Y),
    weakEquivalences D f ↔ weakEquivalences C (adj.homEquiv X Y f))

-- The native constructor works without universal source cofibrancy.
example : adj.IsQuillenEquivalence :=
  Adjunction.IsQuillenEquivalence.mkOfFibrantSourceCriterion adj hcrit

-- The class field retains each original cofibrant source and original arrow.
example (X : C) (Y : D) [IsCofibrant X] [IsFibrant Y]
    (f : L.obj X ⟶ Y) :
    weakEquivalences D f ↔ weakEquivalences C (adj.homEquiv X Y f) := by
  let : adj.IsQuillenEquivalence :=
    Adjunction.IsQuillenEquivalence.mkOfFibrantSourceCriterion adj hcrit
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff f

#print axioms CategoryTheory.Adjunction.IsQuillenEquivalence.mkOfFibrantSourceCriterion
