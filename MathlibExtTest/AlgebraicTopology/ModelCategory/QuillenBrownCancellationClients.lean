/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCancellation
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceRightCancellation

/-!
# Brown preservation and Quillen equivalence clients

The endpoint assumptions are local to the objects of each arrow; no model
category is assumed to have all its objects cofibrant or fibrant.
-/

open CategoryTheory HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenBrownCancellationClients

variable {C : Type*} [Category* C] [ModelCategory C]
  {D : Type*} [Category* D] [ModelCategory D]
  {E : Type*} [Category* E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
  (adj : L ⊣ R) (adj' : L' ⊣ R')

example [adj.IsQuillenAdjunction] {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (L.map f) :=
  Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) f

example [adj.IsQuillenAdjunction] {X Y : D} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (R.map f) :=
  Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f

open Adjunction.IsQuillenEquivalence in
-- Recognize the second equivalence on bifibrant sources only, then cancel it to
-- recover the criterion for the original arrow, whose source need not be fibrant.
example [adj.IsQuillenAdjunction] [adj'.IsQuillenAdjunction]
    [(adj.comp adj').IsQuillenEquivalence]
    (recognize : ∀ (U : D) (V : E) [IsCofibrant U] [IsFibrant U] [IsFibrant V]
      (g : L'.obj U ⟶ V), weakEquivalences E g ↔ weakEquivalences D (adj'.homEquiv U V g))
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f) := by
  have : adj'.IsQuillenEquivalence := mkOfFibrantSourceCriterion adj' recognize
  have : adj.IsQuillenEquivalence := cancel_right adj adj'
  exact weakEquivalence_homEquiv_iff (adj := adj) f

open Adjunction.IsQuillenEquivalence in
example [adj.IsQuillenEquivalence] [adj'.IsQuillenAdjunction]
    [(adj.comp adj').IsQuillenEquivalence]
    {X : D} {Y : E} [IsCofibrant X] [IsFibrant Y] (f : L'.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj'.homEquiv X Y f) := by
  have : adj'.IsQuillenEquivalence := cancel_left adj adj'
  exact weakEquivalence_homEquiv_iff (adj := adj') f

end MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenBrownCancellationClients
